import OMAReductions.R_InscribedSquare_exists_inscribed_rectangle_R1_H2_R1_H2_R1
import Mathlib

/-! Helper cohomology and cubical section lemmas. -/

open Finset Real
open scoped Classical

noncomputable section

namespace OMA.InscribedSquareH1Helpers

abbrev Cochain1 := (ℕ → ℕ → ℕ → ℤ) × (ℕ → ℕ → ℕ → ℤ) × (ℕ → ℕ → ℕ → ℤ)
abbrev Cochain2 := (ℕ → ℕ → ℕ → ℤ) × (ℕ → ℕ → ℕ → ℤ) × (ℕ → ℕ → ℕ → ℤ)

def d1 (b : Cochain1) : Cochain2 :=
  (fun i j k => b.1 i j k + b.2.1 (i + 1) j k - b.1 i (j + 1) k - b.2.1 i j k,
   fun i j k => b.1 i j k + b.2.2 (i + 1) j k - b.1 i j (k + 1) - b.2.2 i j k,
   fun i j k => b.2.1 i j k + b.2.2 i (j + 1) k - b.2.1 i j (k + 1) - b.2.2 i j k)

def d2 (c : Cochain2) (i j k : ℕ) : ℤ :=
  (c.2.2 (i + 1) j k - c.2.2 i j k) -
  (c.2.1 i (j + 1) k - c.2.1 i j k) +
  (c.1 i j (k + 1) - c.1 i j k)

lemma d2_d1 (b : Cochain1) (i j k : ℕ) : d2 (d1 b) i j k = 0 := by
  simp only [d1, d2]; ring

def addC2 (c d : Cochain2) : Cochain2 :=
  (fun i j k => c.1 i j k + d.1 i j k,
   fun i j k => c.2.1 i j k + d.2.1 i j k,
   fun i j k => c.2.2 i j k + d.2.2 i j k)

def scaleC2 (s : ℤ) (c : Cochain2) : Cochain2 :=
  (fun i j k => s * c.1 i j k,
   fun i j k => s * c.2.1 i j k,
   fun i j k => s * c.2.2 i j k)

def subC1 (a b : Cochain1) : Cochain1 :=
  (fun i j k => a.1 i j k - b.1 i j k,
   fun i j k => a.2.1 i j k - b.2.1 i j k,
   fun i j k => a.2.2 i j k - b.2.2 i j k)

def scaleC1 (s : ℤ) (a : Cochain1) : Cochain1 :=
  (fun i j k => s * a.1 i j k,
   fun i j k => s * a.2.1 i j k,
   fun i j k => s * a.2.2 i j k)

lemma d2_add (c d : Cochain2) (i j k : ℕ) :
    d2 (addC2 c d) i j k = d2 c i j k + d2 d i j k := by
  simp only [addC2, d2]; ring

lemma d2_scale (s : ℤ) (c : Cochain2) (i j k : ℕ) :
    d2 (scaleC2 s c) i j k = s * d2 c i j k := by
  simp only [scaleC2, d2]; ring

lemma d1_sub_1 (a b : Cochain1) (i j k : ℕ) :
    (d1 (subC1 a b)).1 i j k = (d1 a).1 i j k - (d1 b).1 i j k := by
  simp only [d1, subC1]; ring

lemma d1_sub_2 (a b : Cochain1) (i j k : ℕ) :
    (d1 (subC1 a b)).2.1 i j k = (d1 a).2.1 i j k - (d1 b).2.1 i j k := by
  simp only [d1, subC1]; ring

lemma d1_sub_3 (a b : Cochain1) (i j k : ℕ) :
    (d1 (subC1 a b)).2.2 i j k = (d1 a).2.2 i j k - (d1 b).2.2 i j k := by
  simp only [d1, subC1]; ring

lemma d1_scale_1 (s : ℤ) (a : Cochain1) (i j k : ℕ) :
    (d1 (scaleC1 s a)).1 i j k = s * (d1 a).1 i j k := by
  simp only [d1, scaleC1]; ring

lemma d1_scale_2 (s : ℤ) (a : Cochain1) (i j k : ℕ) :
    (d1 (scaleC1 s a)).2.1 i j k = s * (d1 a).2.1 i j k := by
  simp only [d1, scaleC1]; ring

lemma d1_scale_3 (s : ℤ) (a : Cochain1) (i j k : ℕ) :
    (d1 (scaleC1 s a)).2.2 i j k = s * (d1 a).2.2 i j k := by
  simp only [d1, scaleC1]; ring

def zeroC2 : Cochain2 := (fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0)

lemma d2_zero (i j k : ℕ) : d2 zeroC2 i j k = 0 := by simp [zeroC2, d2]

def poincare1 (z : Cochain2) : Cochain1 :=
  (fun i j k => - ∑ r ∈ range k, z.2.1 i j r,
   fun i j k => (∑ s ∈ range i, z.1 s j 0) - ∑ r ∈ range k, z.2.2 i j r,
   fun _ _ _ => 0)

lemma d1_poincare1_xz (z : Cochain2) (i j k : ℕ) :
    (d1 (poincare1 z)).2.1 i j k = z.2.1 i j k := by
  simp only [d1, poincare1, sum_range_succ]; ring

lemma d1_poincare1_yz (z : Cochain2) (i j k : ℕ) :
    (d1 (poincare1 z)).2.2 i j k = z.2.2 i j k := by
  simp only [d1, poincare1, sum_range_succ]; ring

lemma d1_poincare1_xy {M : ℕ} (z : Cochain2)
    (hz : ∀ x < M, ∀ y < M, ∀ w < M, d2 z x y w = 0)
    {i j k : ℕ} (hi : i < M) (hj : j < M) (hk : k ≤ M) :
    (d1 (poincare1 z)).1 i j k = z.1 i j k := by
  induction k with
  | zero =>
    simp only [d1, poincare1, range_zero, sum_empty, sum_range_succ]; ring
  | succ k ih =>
    have hklt : k < M := Nat.lt_of_succ_le hk
    have h0 := hz i hi j hj k hklt
    have hih := ih (Nat.le_of_lt hklt)
    simp only [d1, poincare1, sum_range_succ] at hih ⊢
    simp only [d2] at h0
    linarith

def ActXY (A : Finset (ℕ × ℕ × ℕ)) (i j k : ℕ) : Prop :=
  (i, j, k) ∈ A ∨ (0 < k ∧ (i, j, k - 1) ∈ A)

def ActXZ (A : Finset (ℕ × ℕ × ℕ)) (i j k : ℕ) : Prop :=
  (i, j, k) ∈ A ∨ (0 < j ∧ (i, j - 1, k) ∈ A)

def ActYZ (A : Finset (ℕ × ℕ × ℕ)) (i j k : ℕ) : Prop :=
  (i, j, k) ∈ A ∨ (0 < i ∧ (i - 1, j, k) ∈ A)

def actXYB (A : Finset (ℕ × ℕ × ℕ)) (i j k : ℕ) : Bool :=
  decide ((i, j, k) ∈ A) || (decide (0 < k) && decide ((i, j, k - 1) ∈ A))

def actXZB (A : Finset (ℕ × ℕ × ℕ)) (i j k : ℕ) : Bool :=
  decide ((i, j, k) ∈ A) || (decide (0 < j) && decide ((i, j - 1, k) ∈ A))

def actYZB (A : Finset (ℕ × ℕ × ℕ)) (i j k : ℕ) : Bool :=
  decide ((i, j, k) ∈ A) || (decide (0 < i) && decide ((i - 1, j, k) ∈ A))

lemma actXYB_iff (A : Finset (ℕ × ℕ × ℕ)) (i j k : ℕ) :
    actXYB A i j k = true ↔ ActXY A i j k := by
  simp [actXYB, ActXY]

lemma actXZB_iff (A : Finset (ℕ × ℕ × ℕ)) (i j k : ℕ) :
    actXZB A i j k = true ↔ ActXZ A i j k := by
  simp [actXZB, ActXZ]

lemma actYZB_iff (A : Finset (ℕ × ℕ × ℕ)) (i j k : ℕ) :
    actYZB A i j k = true ↔ ActYZ A i j k := by
  simp [actYZB, ActYZ]

def VanishesOnAct (A : Finset (ℕ × ℕ × ℕ)) (c : Cochain2) : Prop :=
  (∀ i j k, ActXY A i j k → c.1 i j k = 0) ∧
  (∀ i j k, ActXZ A i j k → c.2.1 i j k = 0) ∧
  (∀ i j k, ActYZ A i j k → c.2.2 i j k = 0)

lemma vanishesOnAct_add {A : Finset (ℕ × ℕ × ℕ)} {c d : Cochain2}
    (hc : VanishesOnAct A c) (hd : VanishesOnAct A d) :
    VanishesOnAct A (addC2 c d) := by
  refine ⟨fun i j k h => ?_, fun i j k h => ?_, fun i j k h => ?_⟩
  · simp [addC2, hc.1 i j k h, hd.1 i j k h]
  · simp [addC2, hc.2.1 i j k h, hd.2.1 i j k h]
  · simp [addC2, hc.2.2 i j k h, hd.2.2 i j k h]

lemma flux_sink {A : Finset (ℕ × ℕ × ℕ)}
    (hA : ∀ q ∈ A, 1 ≤ q.1) (t : ℤ) :
    ∃ d : Cochain2, VanishesOnAct A d ∧
      ∀ r : ℕ × ℕ × ℕ, d2 d r.1 r.2.1 r.2.2 = if r = (0, 0, 0) then t else 0 := by
  refine ⟨(fun _ _ _ => 0, fun _ _ _ => 0,
    fun i j k => if i = 0 ∧ j = 0 ∧ k = 0 then -t else 0), ?_, ?_⟩
  · refine ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun i j k h => ?_⟩
    dsimp only
    rcases h with h | ⟨hi, _⟩
    · have := hA (i, j, k) h
      simp at this
      split_ifs <;> omega
    · split_ifs <;> omega
  · rintro ⟨x, y, z⟩
    simp only [d2, Nat.succ_ne_zero, false_and, ↓reduceIte, zero_sub, sub_zero, add_zero]
    by_cases h : x = 0 ∧ y = 0 ∧ z = 0
    · rcases h with ⟨rfl, rfl, rfl⟩; simp
    · have h' : (x, y, z) ≠ (0, 0, 0) := by rintro ⟨rfl, rfl, rfl⟩; exact h ⟨rfl, rfl, rfl⟩
      simp [h, h']

def CubeAdj (p q : ℕ × ℕ × ℕ) : Prop :=
  ((p.1 + 1 = q.1 ∨ q.1 + 1 = p.1) ∧ p.2 = q.2) ∨
  (p.1 = q.1 ∧ (p.2.1 + 1 = q.2.1 ∨ q.2.1 + 1 = p.2.1) ∧ p.2.2 = q.2.2) ∨
  (p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ (p.2.2 + 1 = q.2.2 ∨ q.2.2 + 1 = p.2.2))

lemma cubeAdj_symm {p q : ℕ × ℕ × ℕ} (h : CubeAdj p q) : CubeAdj q p := by
  unfold CubeAdj at h ⊢; tauto

lemma cubeAdj_ne {p q : ℕ × ℕ × ℕ} (h : CubeAdj p q) : p ≠ q := by
  rintro rfl
  unfold CubeAdj at h
  rcases h with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h⟩ <;> omega

lemma flux_step_x {A : Finset (ℕ × ℕ × ℕ)} {i j k : ℕ}
    (hp : (i, j, k) ∉ A) (hq : (i + 1, j, k) ∉ A) (t : ℤ) :
    ∃ d : Cochain2, VanishesOnAct A d ∧
      ∀ r : ℕ × ℕ × ℕ, d2 d r.1 r.2.1 r.2.2 =
        (if r = (i, j, k) then -t else 0) + (if r = (i + 1, j, k) then t else 0) := by
  refine ⟨(fun _ _ _ => 0, fun _ _ _ => 0,
    fun x y z => if x = i + 1 ∧ y = j ∧ z = k then -t else 0), ?_, ?_⟩
  · refine ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun x y z h => ?_⟩
    dsimp only
    split_ifs with he
    · rcases he with ⟨rfl, rfl, rfl⟩
      rcases h with h1 | ⟨_, h2⟩
      · exact (hq h1).elim
      · exact (hp h2).elim
    · rfl
  · rintro ⟨x, y, z⟩
    simp only [d2, sub_zero, add_zero, Prod.mk.injEq, add_left_inj]
    by_cases h1 : x = i ∧ y = j ∧ z = k
    · rcases h1 with ⟨rfl, rfl, rfl⟩; simp
    · by_cases h2 : x = i + 1 ∧ y = j ∧ z = k
      · rcases h2 with ⟨rfl, rfl, rfl⟩; simp
      · simp [h1, h2]

lemma flux_step_y {A : Finset (ℕ × ℕ × ℕ)} {i j k : ℕ}
    (hp : (i, j, k) ∉ A) (hq : (i, j + 1, k) ∉ A) (t : ℤ) :
    ∃ d : Cochain2, VanishesOnAct A d ∧
      ∀ r : ℕ × ℕ × ℕ, d2 d r.1 r.2.1 r.2.2 =
        (if r = (i, j, k) then -t else 0) + (if r = (i, j + 1, k) then t else 0) := by
  refine ⟨(fun _ _ _ => 0,
    fun x y z => if x = i ∧ y = j + 1 ∧ z = k then t else 0, fun _ _ _ => 0), ?_, ?_⟩
  · refine ⟨fun _ _ _ _ => rfl, fun x y z h => ?_, fun _ _ _ _ => rfl⟩
    dsimp only
    split_ifs with he
    · rcases he with ⟨rfl, rfl, rfl⟩
      rcases h with h1 | ⟨_, h2⟩
      · exact (hq h1).elim
      · exact (hp h2).elim
    · rfl
  · rintro ⟨x, y, z⟩
    simp only [d2, sub_zero, zero_sub, add_zero, Prod.mk.injEq, add_left_inj]
    by_cases h1 : x = i ∧ y = j ∧ z = k
    · rcases h1 with ⟨rfl, rfl, rfl⟩; simp
    · by_cases h2 : x = i ∧ y = j + 1 ∧ z = k
      · rcases h2 with ⟨rfl, rfl, rfl⟩; simp
      · simp [h1, h2]

lemma flux_step_z {A : Finset (ℕ × ℕ × ℕ)} {i j k : ℕ}
    (hp : (i, j, k) ∉ A) (hq : (i, j, k + 1) ∉ A) (t : ℤ) :
    ∃ d : Cochain2, VanishesOnAct A d ∧
      ∀ r : ℕ × ℕ × ℕ, d2 d r.1 r.2.1 r.2.2 =
        (if r = (i, j, k) then -t else 0) + (if r = (i, j, k + 1) then t else 0) := by
  refine ⟨(fun x y z => if x = i ∧ y = j ∧ z = k + 1 then -t else 0,
    fun _ _ _ => 0, fun _ _ _ => 0), ?_, ?_⟩
  · refine ⟨fun x y z h => ?_, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
    dsimp only
    split_ifs with he
    · rcases he with ⟨rfl, rfl, rfl⟩
      rcases h with h1 | ⟨_, h2⟩
      · exact (hq h1).elim
      · exact (hp h2).elim
    · rfl
  · rintro ⟨x, y, z⟩
    simp only [d2, sub_zero, zero_add, Prod.mk.injEq, add_left_inj]
    by_cases h1 : x = i ∧ y = j ∧ z = k
    · rcases h1 with ⟨rfl, rfl, rfl⟩; simp
    · by_cases h2 : x = i ∧ y = j ∧ z = k + 1
      · rcases h2 with ⟨rfl, rfl, rfl⟩; simp
      · simp [h1, h2]

lemma flux_adj {A : Finset (ℕ × ℕ × ℕ)} {p q : ℕ × ℕ × ℕ}
    (hp : p ∉ A) (hq : q ∉ A) (hadj : CubeAdj p q) (t : ℤ) :
    ∃ d : Cochain2, VanishesOnAct A d ∧
      ∀ r : ℕ × ℕ × ℕ, d2 d r.1 r.2.1 r.2.2 =
        (if r = p then -t else 0) + (if r = q then t else 0) := by
  rcases p with ⟨pi, pj, pk⟩; rcases q with ⟨qi, qj, qk⟩
  unfold CubeAdj at hadj
  dsimp only at hadj
  rcases hadj with ⟨h1 | h1, h2⟩ | ⟨rfl, h1 | h1, rfl⟩ | ⟨rfl, rfl, h1 | h1⟩
  · injection h2 with hj hk; subst h1 hj hk; exact flux_step_x hp hq t
  · injection h2 with hj hk; subst h1 hj hk
    obtain ⟨d, hd1, hd2⟩ := flux_step_x hq hp (-t)
    refine ⟨d, hd1, fun r => (hd2 r).trans ?_⟩; split_ifs <;> ring
  · subst h1; exact flux_step_y hp hq t
  · subst h1
    obtain ⟨d, hd1, hd2⟩ := flux_step_y hq hp (-t)
    refine ⟨d, hd1, fun r => (hd2 r).trans ?_⟩; split_ifs <;> ring
  · subst h1; exact flux_step_z hp hq t
  · subst h1
    obtain ⟨d, hd1, hd2⟩ := flux_step_z hq hp (-t)
    refine ⟨d, hd1, fun r => (hd2 r).trans ?_⟩; split_ifs <;> ring

def box (M : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  range M ×ˢ (range M ×ˢ range M)

lemma mem_box_iff {M : ℕ} {q : ℕ × ℕ × ℕ} :
    q ∈ box M ↔ q.1 < M ∧ q.2.1 < M ∧ q.2.2 < M := by
  simp [box, mem_product, mem_range]

lemma mem_interior_of_closed {M : ℕ} (hM : 4 ≤ M) {A Ω : Finset (ℕ × ℕ × ℕ)}
    (hA : ∀ q ∈ A, 1 ≤ q.1 ∧ q.1 + 2 ≤ M ∧ 1 ≤ q.2.1 ∧ q.2.1 + 2 ≤ M ∧ 1 ≤ q.2.2 ∧ q.2.2 + 2 ≤ M)
    (hΩI : Ω ⊆ box M \ A) (h0 : (0, 0, 0) ∉ Ω)
    (hcl : ∀ p ∈ Ω, ∀ q ∈ box M \ A, CubeAdj p q → q ∈ Ω) :
    ∀ q ∈ Ω, 1 ≤ q.1 ∧ q.1 + 2 ≤ M ∧ 1 ≤ q.2.1 ∧ q.2.1 + 2 ≤ M ∧ 1 ≤ q.2.2 ∧ q.2.2 + 2 ≤ M := by
  have bdI : ∀ i j k, i < M → j < M → k < M →
      (i = 0 ∨ i + 1 = M ∨ j = 0 ∨ j + 1 = M ∨ k = 0 ∨ k + 1 = M) →
      (i, j, k) ∈ box M \ A := by
    intro i j k hi hj hk hb
    refine mem_sdiff.mpr ⟨mem_box_iff.mpr ⟨hi, hj, hk⟩, fun ha => ?_⟩
    have := hA (i, j, k) ha; simp at this; omega
  have step : ∀ p q, p ∈ box M \ A → p ∉ Ω → CubeAdj q p → q ∉ Ω :=
    fun p q hpI hp hadj hq => hp (hcl q hq p hpI hadj)
  have n_i00 : ∀ i < M, (i, 0, 0) ∉ Ω := by
    intro i; induction i with
    | zero => intro _; exact h0
    | succ i ih =>
      intro hi
      exact step (i, 0, 0) (i + 1, 0, 0)
        (bdI i 0 0 (by omega) (by omega) (by omega) (Or.inr (Or.inr (Or.inl rfl))))
        (ih (by omega)) (Or.inl ⟨Or.inr rfl, rfl⟩)
  have n_ij0 : ∀ i < M, ∀ j < M, (i, j, 0) ∉ Ω := by
    intro i hi j; induction j with
    | zero => intro _; exact n_i00 i hi
    | succ j ih =>
      intro hj
      exact step (i, j, 0) (i, j + 1, 0)
        (bdI i j 0 hi (by omega) (by omega) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
        (ih (by omega)) (Or.inr (Or.inl ⟨rfl, Or.inr rfl, rfl⟩))
  have n_0jk : ∀ j < M, ∀ k < M, (0, j, k) ∉ Ω := by
    intro j hj k; induction k with
    | zero => intro _; exact n_ij0 0 (by omega) j hj
    | succ k ih =>
      intro hk
      exact step (0, j, k) (0, j, k + 1)
        (bdI 0 j k (by omega) hj (by omega) (Or.inl rfl))
        (ih (by omega)) (Or.inr (Or.inr ⟨rfl, rfl, Or.inr rfl⟩))
  have n_i0k : ∀ i < M, ∀ k < M, (i, 0, k) ∉ Ω := by
    intro i hi k; induction k with
    | zero => intro _; exact n_i00 i hi
    | succ k ih =>
      intro hk
      exact step (i, 0, k) (i, 0, k + 1)
        (bdI i 0 k hi (by omega) (by omega) (Or.inr (Or.inr (Or.inl rfl))))
        (ih (by omega)) (Or.inr (Or.inr ⟨rfl, rfl, Or.inr rfl⟩))
  have n_ijM : ∀ i < M, ∀ j < M, (i, j, M - 1) ∉ Ω := by
    intro i hi j hj; induction i with
    | zero => exact n_0jk j hj (M - 1) (by omega)
    | succ i ih =>
      exact step (i, j, M - 1) (i + 1, j, M - 1)
        (bdI i j (M - 1) (by omega) hj (by omega) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))))
        (ih (by omega)) (Or.inl ⟨Or.inr rfl, rfl⟩)
  have n_iMk : ∀ i < M, ∀ k < M, (i, M - 1, k) ∉ Ω := by
    intro i hi k hk; induction i with
    | zero => exact n_0jk (M - 1) (by omega) k hk
    | succ i ih =>
      exact step (i, M - 1, k) (i + 1, M - 1, k)
        (bdI i (M - 1) k (by omega) (by omega) hk (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
        (ih (by omega)) (Or.inl ⟨Or.inr rfl, rfl⟩)
  have n_Mjk : ∀ j < M, ∀ k < M, (M - 1, j, k) ∉ Ω := by
    intro j hj k hk; induction j with
    | zero => exact n_i0k (M - 1) (by omega) k hk
    | succ j ih =>
      exact step (M - 1, j, k) (M - 1, j + 1, k)
        (bdI (M - 1) j k (by omega) (by omega) hk (Or.inr (Or.inl (by omega))))
        (ih (by omega)) (Or.inr (Or.inl ⟨rfl, Or.inr rfl, rfl⟩))
  rintro ⟨i, j, k⟩ hq
  obtain ⟨hi, hj, hk⟩ := mem_box_iff.mp (mem_sdiff.mp (hΩI hq)).1
  have h1 : i ≠ 0 := fun e => n_0jk j hj k hk (e ▸ hq)
  have h2 : i ≠ M - 1 := fun e => n_Mjk j hj k hk (e ▸ hq)
  have h3 : j ≠ 0 := fun e => n_i0k i hi k hk (e ▸ hq)
  have h4 : j ≠ M - 1 := fun e => n_iMk i hi k hk (e ▸ hq)
  have h5 : k ≠ 0 := fun e => n_ij0 i hi j hj (e ▸ hq)
  have h6 : k ≠ M - 1 := fun e => n_ijM i hi j hj (e ▸ hq)
  dsimp only at hi hj hk ⊢; omega

lemma sum_d2_vanishes_eq_zero {M : ℕ} (hM : 4 ≤ M) {A Ω : Finset (ℕ × ℕ × ℕ)}
    (hA : ∀ q ∈ A, 1 ≤ q.1 ∧ q.1 + 2 ≤ M ∧ 1 ≤ q.2.1 ∧ q.2.1 + 2 ≤ M ∧ 1 ≤ q.2.2 ∧ q.2.2 + 2 ≤ M)
    (hΩI : Ω ⊆ box M \ A) (h0 : (0, 0, 0) ∉ Ω)
    (hcl : ∀ p ∈ Ω, ∀ q ∈ box M \ A, CubeAdj p q → q ∈ Ω)
    {c : Cochain2} (hc : VanishesOnAct A c) :
    ∑ q ∈ Ω, d2 c q.1 q.2.1 q.2.2 = 0 := by
  have hint := mem_interior_of_closed hM hA hΩI h0 hcl
  let B1 := box (M + 1)
  have hsub0 : Ω ⊆ B1 := fun q hq => by
    have := hint q hq; exact mem_box_iff.mpr ⟨by omega, by omega, by omega⟩
  have hyz : ∑ q ∈ Ω, c.2.2 (q.1 + 1) q.2.1 q.2.2 = ∑ q ∈ Ω, c.2.2 q.1 q.2.1 q.2.2 := by
    let sh : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun q => (q.1 + 1, q.2.1, q.2.2)
    have hinj : Function.Injective sh := by rintro ⟨a, b, d⟩ ⟨x, y, z⟩ h; simpa [sh] using h
    have hsub1 : Ω.image sh ⊆ B1 := by
      intro s hs; obtain ⟨q, hq, rfl⟩ := mem_image.mp hs
      have := hint q hq; exact mem_box_iff.mpr ⟨by dsimp [sh]; omega, by dsimp [sh]; omega, by dsimp [sh]; omega⟩
    have himg : ∑ q ∈ Ω, c.2.2 (q.1 + 1) q.2.1 q.2.2 = ∑ s ∈ Ω.image sh, c.2.2 s.1 s.2.1 s.2.2 :=
      (sum_image (f := fun s : ℕ × ℕ × ℕ => c.2.2 s.1 s.2.1 s.2.2) (fun x _ y _ h => hinj h)).symm
    have e_lhs : ∑ s ∈ Ω.image sh, c.2.2 s.1 s.2.1 s.2.2 =
        ∑ s ∈ B1, if s ∈ Ω.image sh then c.2.2 s.1 s.2.1 s.2.2 else 0 := by
      rw [sum_ite_mem, inter_eq_right.mpr hsub1]
    have e_rhs : ∑ q ∈ Ω, c.2.2 q.1 q.2.1 q.2.2 =
        ∑ s ∈ B1, if s ∈ Ω then c.2.2 s.1 s.2.1 s.2.2 else 0 := by
      rw [sum_ite_mem, inter_eq_right.mpr hsub0]
    rw [himg, e_lhs, e_rhs]
    refine sum_congr rfl fun ⟨i, j, k⟩ hs => ?_
    by_cases hcz : c.2.2 i j k = 0
    · simp [hcz]
    · have hna : ¬ ActYZ A i j k := fun ha => hcz (hc.2.2 i j k ha)
      have iff_mem : (i, j, k) ∈ Ω.image sh ↔ (i, j, k) ∈ Ω := by
        constructor
        · intro hm; obtain ⟨⟨x, y, z⟩, hxyz, he⟩ := mem_image.mp hm
          simp only [sh, Prod.mk.injEq] at he
          rcases he with ⟨hx, rfl, rfl⟩
          have hxM := hint (x, y, z) hxyz
          have hmemB : (x + 1, y, z) ∈ box M := mem_box_iff.mpr ⟨by dsimp at hxM ⊢; omega, by dsimp at hxM ⊢; omega, by dsimp at hxM ⊢; omega⟩
          have hnA : (x + 1, y, z) ∉ A := fun ha => hna (Or.inl (hx ▸ ha))
          have := hcl (x, y, z) hxyz (x + 1, y, z) (mem_sdiff.mpr ⟨hmemB, hnA⟩) (Or.inl ⟨Or.inl rfl, rfl⟩)
          simpa [hx] using this
        · intro hm
          have hiM := hint (i, j, k) hm
          have hipos : 1 ≤ i := hiM.1
          have hmemB : (i - 1, j, k) ∈ box M := mem_box_iff.mpr ⟨by dsimp at hiM ⊢; omega, by dsimp at hiM ⊢; omega, by dsimp at hiM ⊢; omega⟩
          have hnA : (i - 1, j, k) ∉ A := fun ha => hna (Or.inr ⟨by omega, ha⟩)
          have hm' := hcl (i, j, k) hm (i - 1, j, k) (mem_sdiff.mpr ⟨hmemB, hnA⟩) (Or.inl ⟨Or.inr (by dsimp; omega), rfl⟩)
          exact mem_image.mpr ⟨(i - 1, j, k), hm', by ext <;> dsimp [sh] <;> omega⟩
      exact if_congr iff_mem rfl rfl
  have hxz : ∑ q ∈ Ω, c.2.1 q.1 (q.2.1 + 1) q.2.2 = ∑ q ∈ Ω, c.2.1 q.1 q.2.1 q.2.2 := by
    let sh : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun q => (q.1, q.2.1 + 1, q.2.2)
    have hinj : Function.Injective sh := by rintro ⟨a, b, d⟩ ⟨x, y, z⟩ h; simpa [sh] using h
    have hsub1 : Ω.image sh ⊆ B1 := by
      intro s hs; obtain ⟨q, hq, rfl⟩ := mem_image.mp hs
      have := hint q hq; exact mem_box_iff.mpr ⟨by dsimp [sh]; omega, by dsimp [sh]; omega, by dsimp [sh]; omega⟩
    have himg : ∑ q ∈ Ω, c.2.1 q.1 (q.2.1 + 1) q.2.2 = ∑ s ∈ Ω.image sh, c.2.1 s.1 s.2.1 s.2.2 :=
      (sum_image (f := fun s : ℕ × ℕ × ℕ => c.2.1 s.1 s.2.1 s.2.2) (fun x _ y _ h => hinj h)).symm
    have e_lhs : ∑ s ∈ Ω.image sh, c.2.1 s.1 s.2.1 s.2.2 =
        ∑ s ∈ B1, if s ∈ Ω.image sh then c.2.1 s.1 s.2.1 s.2.2 else 0 := by
      rw [sum_ite_mem, inter_eq_right.mpr hsub1]
    have e_rhs : ∑ q ∈ Ω, c.2.1 q.1 q.2.1 q.2.2 =
        ∑ s ∈ B1, if s ∈ Ω then c.2.1 s.1 s.2.1 s.2.2 else 0 := by
      rw [sum_ite_mem, inter_eq_right.mpr hsub0]
    rw [himg, e_lhs, e_rhs]
    refine sum_congr rfl fun ⟨i, j, k⟩ hs => ?_
    by_cases hcz : c.2.1 i j k = 0
    · simp [hcz]
    · have hna : ¬ ActXZ A i j k := fun ha => hcz (hc.2.1 i j k ha)
      have iff_mem : (i, j, k) ∈ Ω.image sh ↔ (i, j, k) ∈ Ω := by
        constructor
        · intro hm; obtain ⟨⟨x, y, z⟩, hxyz, he⟩ := mem_image.mp hm
          simp only [sh, Prod.mk.injEq] at he
          rcases he with ⟨rfl, hy, rfl⟩
          have hyM := hint (x, y, z) hxyz
          have hmemB : (x, y + 1, z) ∈ box M := mem_box_iff.mpr ⟨by dsimp at hyM ⊢; omega, by dsimp at hyM ⊢; omega, by dsimp at hyM ⊢; omega⟩
          have hnA : (x, y + 1, z) ∉ A := fun ha => hna (Or.inl (hy ▸ ha))
          have := hcl (x, y, z) hxyz (x, y + 1, z) (mem_sdiff.mpr ⟨hmemB, hnA⟩) (Or.inr (Or.inl ⟨rfl, Or.inl rfl, rfl⟩))
          simpa [hy] using this
        · intro hm
          have hjM := hint (i, j, k) hm
          have hjpos : 1 ≤ j := hjM.2.2.1
          have hmemB : (i, j - 1, k) ∈ box M := mem_box_iff.mpr ⟨by dsimp at hjM ⊢; omega, by dsimp at hjM ⊢; omega, by dsimp at hjM ⊢; omega⟩
          have hnA : (i, j - 1, k) ∉ A := fun ha => hna (Or.inr ⟨by omega, ha⟩)
          have hm' := hcl (i, j, k) hm (i, j - 1, k) (mem_sdiff.mpr ⟨hmemB, hnA⟩) (Or.inr (Or.inl ⟨rfl, Or.inr (by dsimp; omega), rfl⟩))
          exact mem_image.mpr ⟨(i, j - 1, k), hm', by ext <;> dsimp [sh] <;> omega⟩
      exact if_congr iff_mem rfl rfl
  have hxy : ∑ q ∈ Ω, c.1 q.1 q.2.1 (q.2.2 + 1) = ∑ q ∈ Ω, c.1 q.1 q.2.1 q.2.2 := by
    let sh : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun q => (q.1, q.2.1, q.2.2 + 1)
    have hinj : Function.Injective sh := by rintro ⟨a, b, d⟩ ⟨x, y, z⟩ h; simpa [sh] using h
    have hsub1 : Ω.image sh ⊆ B1 := by
      intro s hs; obtain ⟨q, hq, rfl⟩ := mem_image.mp hs
      have := hint q hq; exact mem_box_iff.mpr ⟨by dsimp [sh]; omega, by dsimp [sh]; omega, by dsimp [sh]; omega⟩
    have himg : ∑ q ∈ Ω, c.1 q.1 q.2.1 (q.2.2 + 1) = ∑ s ∈ Ω.image sh, c.1 s.1 s.2.1 s.2.2 :=
      (sum_image (f := fun s : ℕ × ℕ × ℕ => c.1 s.1 s.2.1 s.2.2) (fun x _ y _ h => hinj h)).symm
    have e_lhs : ∑ s ∈ Ω.image sh, c.1 s.1 s.2.1 s.2.2 =
        ∑ s ∈ B1, if s ∈ Ω.image sh then c.1 s.1 s.2.1 s.2.2 else 0 := by
      rw [sum_ite_mem, inter_eq_right.mpr hsub1]
    have e_rhs : ∑ q ∈ Ω, c.1 q.1 q.2.1 q.2.2 =
        ∑ s ∈ B1, if s ∈ Ω then c.1 s.1 s.2.1 s.2.2 else 0 := by
      rw [sum_ite_mem, inter_eq_right.mpr hsub0]
    rw [himg, e_lhs, e_rhs]
    refine sum_congr rfl fun ⟨i, j, k⟩ hs => ?_
    by_cases hcz : c.1 i j k = 0
    · simp [hcz]
    · have hna : ¬ ActXY A i j k := fun ha => hcz (hc.1 i j k ha)
      have iff_mem : (i, j, k) ∈ Ω.image sh ↔ (i, j, k) ∈ Ω := by
        constructor
        · intro hm; obtain ⟨⟨x, y, z⟩, hxyz, he⟩ := mem_image.mp hm
          simp only [sh, Prod.mk.injEq] at he
          rcases he with ⟨rfl, rfl, hz⟩
          have hzM := hint (x, y, z) hxyz
          have hmemB : (x, y, z + 1) ∈ box M := mem_box_iff.mpr ⟨by dsimp at hzM ⊢; omega, by dsimp at hzM ⊢; omega, by dsimp at hzM ⊢; omega⟩
          have hnA : (x, y, z + 1) ∉ A := fun ha => hna (Or.inl (hz ▸ ha))
          have := hcl (x, y, z) hxyz (x, y, z + 1) (mem_sdiff.mpr ⟨hmemB, hnA⟩) (Or.inr (Or.inr ⟨rfl, rfl, Or.inl rfl⟩))
          simpa [hz] using this
        · intro hm
          have hkM := hint (i, j, k) hm
          have hkpos : 1 ≤ k := hkM.2.2.2.2.1
          have hmemB : (i, j, k - 1) ∈ box M := mem_box_iff.mpr ⟨by dsimp at hkM ⊢; omega, by dsimp at hkM ⊢; omega, by dsimp at hkM ⊢; omega⟩
          have hnA : (i, j, k - 1) ∉ A := fun ha => hna (Or.inr ⟨by omega, ha⟩)
          have hm' := hcl (i, j, k) hm (i, j, k - 1) (mem_sdiff.mpr ⟨hmemB, hnA⟩) (Or.inr (Or.inr ⟨rfl, rfl, Or.inr (by dsimp; omega)⟩))
          exact mem_image.mpr ⟨(i, j, k - 1), hm', by ext <;> dsimp [sh] <;> omega⟩
      exact if_congr iff_mem rfl rfl
  simp only [d2, sum_add_distrib, sum_sub_distrib, hyz, hxz, hxy, sub_self, add_zero]

def stepSet (S X : Finset (ℕ × ℕ × ℕ)) : Finset (ℕ × ℕ × ℕ) :=
  X ∪ S.filter (fun q => ∃ p ∈ X, CubeAdj p q)

def reach (S : Finset (ℕ × ℕ × ℕ)) (q₀ : ℕ × ℕ × ℕ) : ℕ → Finset (ℕ × ℕ × ℕ)
  | 0 => {q₀}
  | k + 1 => stepSet S (reach S q₀ k)

lemma reach_sub_next (S : Finset (ℕ × ℕ × ℕ)) (q₀ : ℕ × ℕ × ℕ) (k : ℕ) :
    reach S q₀ k ⊆ reach S q₀ (k + 1) := subset_union_left

lemma reach_mono (S : Finset (ℕ × ℕ × ℕ)) (q₀ : ℕ × ℕ × ℕ) {a b : ℕ} (hab : a ≤ b) :
    reach S q₀ a ⊆ reach S q₀ b := by
  induction hab with
  | refl => exact Subset.rfl
  | step _ ih => exact ih.trans (reach_sub_next S q₀ _)

lemma mem_reach_zero (S : Finset (ℕ × ℕ × ℕ)) (q₀ : ℕ × ℕ × ℕ) : q₀ ∈ reach S q₀ 0 :=
  mem_singleton_self q₀

lemma reach_sub_self {S : Finset (ℕ × ℕ × ℕ)} {q₀ : ℕ × ℕ × ℕ} (hq₀ : q₀ ∈ S) (k : ℕ) :
    reach S q₀ k ⊆ S := by
  induction k with
  | zero => exact singleton_subset_iff.mpr hq₀
  | succ k ih => exact union_subset ih (filter_subset _ _)

lemma reach_eq_after {S : Finset (ℕ × ℕ × ℕ)} {q₀ : ℕ × ℕ × ℕ} {k : ℕ}
    (h : reach S q₀ (k + 1) = reach S q₀ k) : ∀ m ≥ k, reach S q₀ m = reach S q₀ k := by
  intro m hm
  induction hm with
  | refl => rfl
  | step _ ih => rw [reach, ih]; exact h

lemma reach_stabilizes {S : Finset (ℕ × ℕ × ℕ)} {q₀ : ℕ × ℕ × ℕ} (hq₀ : q₀ ∈ S) :
    reach S q₀ (S.card + 1) = reach S q₀ S.card := by
  by_contra hne
  have hall : ∀ k ≤ S.card, k + 1 ≤ (reach S q₀ k).card := by
    intro k; induction k with
    | zero => intro _; simp [reach]
    | succ k ih =>
      intro hk
      have hne_k : reach S q₀ (k + 1) ≠ reach S q₀ k := by
        intro heq
        have h1 := reach_eq_after heq S.card (by omega)
        have h2 := reach_eq_after heq (S.card + 1) (by omega)
        exact hne (h2.trans h1.symm)
      have hssub : reach S q₀ k ⊂ reach S q₀ (k + 1) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨reach_sub_next S q₀ k, hne_k.symm⟩
      have hlt := card_lt_card hssub
      have := ih (by omega)
      omega
  have h1 := hall S.card le_rfl
  have h2 := card_le_card (reach_sub_self hq₀ S.card)
  omega

def comp (S : Finset (ℕ × ℕ × ℕ)) (q₀ : ℕ × ℕ × ℕ) : Finset (ℕ × ℕ × ℕ) :=
  reach S q₀ S.card

lemma comp_closed {S : Finset (ℕ × ℕ × ℕ)} {q₀ : ℕ × ℕ × ℕ} (hq₀ : q₀ ∈ S) :
    ∀ p ∈ comp S q₀, ∀ q ∈ S, CubeAdj p q → q ∈ comp S q₀ := by
  intro p hp q hq hadj
  have hst := reach_stabilizes hq₀
  unfold comp at hp ⊢
  rw [← hst, reach, stepSet]
  exact mem_union_right _ (mem_filter.mpr ⟨hq, p, hp, hadj⟩)

lemma comp_sub_of_closed {S Ω : Finset (ℕ × ℕ × ℕ)} {q₀ : ℕ × ℕ × ℕ}
    (hq₀ : q₀ ∈ Ω) (hcl : ∀ p ∈ Ω, ∀ q ∈ S, CubeAdj p q → q ∈ Ω) (k : ℕ) :
    reach S q₀ k ⊆ Ω := by
  induction k with
  | zero => exact singleton_subset_iff.mpr hq₀
  | succ k ih =>
    intro x hx
    rcases mem_union.mp hx with hx1 | hx2
    · exact ih hx1
    · obtain ⟨hxS, p, hp, hadj⟩ := mem_filter.mp hx2
      exact hcl p (ih hp) x hxS hadj

lemma comp_disjoint_of_closed' {S Ω : Finset (ℕ × ℕ × ℕ)} {q₀ : ℕ × ℕ × ℕ}
    (hq₀S : q₀ ∈ S) (hq₀ : q₀ ∉ Ω) (hcl : ∀ p ∈ Ω, ∀ q ∈ S, CubeAdj p q → q ∈ Ω) :
    ∀ x ∈ comp S q₀, x ∉ Ω := by
  have hk : ∀ k, ∀ x ∈ reach S q₀ k, x ∉ Ω := by
    intro k; induction k with
    | zero => intro x hx; rw [mem_singleton.mp hx]; exact hq₀
    | succ k ih =>
      intro x hx hxΩ
      rcases mem_union.mp hx with hx1 | hx2
      · exact ih x hx1 hxΩ
      · obtain ⟨_, p, hp, hadj⟩ := mem_filter.mp hx2
        exact ih p hp (hcl x hxΩ p (reach_sub_self hq₀S k hp) (cubeAdj_symm hadj))
  exact hk S.card

lemma exists_peel_leaf {S : Finset (ℕ × ℕ × ℕ)} {q₀ : ℕ × ℕ × ℕ} (hq₀ : q₀ ∈ S)
    (hne : ∃ y ∈ comp S q₀, y ≠ q₀) :
    ∃ q₁ ∈ comp S q₀, ∃ q₂ ∈ comp S q₀,
      q₁ ≠ q₀ ∧ q₂ ≠ q₁ ∧ CubeAdj q₂ q₁ ∧
      (comp S q₀).erase q₁ ⊆ comp (S.erase q₁) q₀ := by
  let P : Finset ℕ := (range S.card).filter (fun m => ¬ reach S q₀ (m + 1) ⊆ reach S q₀ m)
  have hPne : P.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have hall : ∀ m ≤ S.card, reach S q₀ m = {q₀} := by
      intro m; induction m with
      | zero => intro _; rfl
      | succ m ih =>
        intro hm
        have hnot : m ∉ P := by rw [hemp]; simp
        simp only [P, mem_filter, mem_range, not_and, not_not] at hnot
        have hsub := hnot (by omega)
        exact Subset.antisymm (hsub.trans (by rw [ih (by omega)]))
          (by rw [← ih (by omega)]; exact reach_sub_next S q₀ m)
    obtain ⟨y, hy, hy0⟩ := hne
    rw [comp, hall S.card le_rfl] at hy
    exact hy0 (mem_singleton.mp hy)
  let m := P.max' hPne
  have hmP : m ∈ P := max'_mem P hPne
  obtain ⟨hm_lt, hm_nsub⟩ := mem_filter.mp hmP
  rw [mem_range] at hm_lt
  have hstab : ∀ k, m + 1 ≤ k → k ≤ S.card → reach S q₀ k = reach S q₀ (m + 1) := by
    intro k hmk hkS
    induction hmk with
    | refl => rfl
    | @step r hmr ih =>
      have hr_not : r ∉ P := fun hr => Nat.not_le.mpr (Nat.lt_of_succ_le hmr) (le_max' P r hr)
      simp only [P, mem_filter, mem_range, not_and, not_not] at hr_not
      have hsub := hr_not (by omega)
      exact (Subset.antisymm hsub (reach_sub_next S q₀ r)).trans (ih (by omega))
  have hcomp_eq : comp S q₀ = reach S q₀ (m + 1) := hstab S.card (by omega) le_rfl
  obtain ⟨q₁, hq₁_in, hq₁_out⟩ := not_subset.mp hm_nsub
  have hq₁_comp : q₁ ∈ comp S q₀ := hcomp_eq ▸ hq₁_in
  have hq₁_ne0 : q₁ ≠ q₀ := fun e => hq₁_out (e ▸ reach_mono S q₀ (Nat.zero_le m) (mem_reach_zero S q₀))
  have hq₁_step : q₁ ∈ S.filter (fun q => ∃ p ∈ reach S q₀ m, CubeAdj p q) := by
    rcases mem_union.mp hq₁_in with h1 | h2
    · exact (hq₁_out h1).elim
    · exact h2
  obtain ⟨hq₁S, q₂, hq₂m, hadj⟩ := mem_filter.mp hq₁_step
  have hq₂_comp : q₂ ∈ comp S q₀ := hcomp_eq ▸ reach_sub_next S q₀ m hq₂m
  have hq₂_ne1 : q₂ ≠ q₁ := fun e => hq₁_out (e ▸ hq₂m)
  have hreach_eq : ∀ r ≤ m, reach S q₀ r ⊆ reach (S.erase q₁) q₀ r := by
    intro r; induction r with
    | zero => intro _; exact Subset.rfl
    | succ r ih =>
      intro hr x hx
      rcases mem_union.mp hx with hx1 | hx2
      · exact mem_union_left _ (ih (by omega) hx1)
      · obtain ⟨hxS, p, hp, hadjp⟩ := mem_filter.mp hx2
        have hxq₁ : x ≠ q₁ := fun e => hq₁_out (reach_mono S q₀ hr (e ▸ hx))
        exact mem_union_right _ (mem_filter.mpr ⟨mem_erase.mpr ⟨hxq₁, hxS⟩, p, ih (by omega) hp, hadjp⟩)
  refine ⟨q₁, hq₁_comp, q₂, hq₂_comp, hq₁_ne0, hq₂_ne1, hadj, ?_⟩
  intro x hx
  obtain ⟨hx_ne1, hx_comp⟩ := mem_erase.mp hx
  rw [hcomp_eq] at hx_comp
  have hm_le : m + 1 ≤ (S.erase q₁).card + 1 := by
    rw [card_erase_of_mem hq₁S]; omega
  have hstep_sub : x ∈ reach (S.erase q₁) q₀ (m + 1) := by
    rcases mem_union.mp hx_comp with hx1 | hx2
    · exact reach_sub_next _ _ m (hreach_eq m le_rfl hx1)
    · obtain ⟨hxS, p, hp, hadjp⟩ := mem_filter.mp hx2
      exact mem_union_right _ (mem_filter.mpr ⟨mem_erase.mpr ⟨hx_ne1, hxS⟩, p, hreach_eq m le_rfl hp, hadjp⟩)
  by_cases hm_card : m + 1 ≤ (S.erase q₁).card
  · exact reach_mono (S.erase q₁) q₀ hm_card hstep_sub
  · have heq_card : m = (S.erase q₁).card := by omega
    rw [comp, ← reach_stabilizes (mem_erase.mpr ⟨hq₁_ne0.symm, hq₀⟩), ← heq_card]
    exact hstep_sub

lemma solve_div_on_set {M : ℕ} {A : Finset (ℕ × ℕ × ℕ)}
    (hA0 : ∀ q ∈ A, 1 ≤ q.1) :
    ∀ (n : ℕ) (S : Finset (ℕ × ℕ × ℕ)), S.card = n →
      S ⊆ box M \ A → (0, 0, 0) ∈ S →
      ∀ w : ℕ × ℕ × ℕ → ℤ,
        (∀ q ∈ box M \ S, w q = 0) →
        (∀ Ω ⊆ S, (0, 0, 0) ∉ Ω → (∀ p ∈ Ω, ∀ q ∈ S, CubeAdj p q → q ∈ Ω) → ∑ q ∈ Ω, w q = 0) →
        ∃ d : Cochain2, VanishesOnAct A d ∧ ∀ q ∈ box M, d2 d q.1 q.2.1 q.2.2 = - w q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hScard hSI h0S w hw_out hw_cl
    by_cases hS_one : ∀ x ∈ S, x = (0, 0, 0)
    · obtain ⟨d, hd_act, hd2⟩ := flux_sink hA0 (- w (0, 0, 0))
      refine ⟨d, hd_act, fun q hqB => ?_⟩
      rw [hd2 q]
      by_cases hq0 : q = (0, 0, 0)
      · subst hq0; simp
      · simp only [hq0, ↓reduceIte]
        have hq_notS : q ∉ S := fun hqS => hq0 (hS_one q hqS)
        rw [hw_out q (mem_sdiff.mpr ⟨hqB, hq_notS⟩), neg_zero]
    · have hS_ex : ∃ x ∈ S, x ≠ (0, 0, 0) := by
        by_contra hall; apply hS_one; intro x hx; by_contra hne; exact hall ⟨x, hx, hne⟩
      let C0 := comp S (0, 0, 0)
      by_cases hC0_nt : ∃ y ∈ C0, y ≠ (0, 0, 0)
      · obtain ⟨q₁, hq₁C, q₂, hq₂C, hq₁_ne0, hq₂_ne1, hadj, hsub_comp⟩ :=
          exists_peel_leaf h0S hC0_nt
        have hq₁S : q₁ ∈ S := reach_sub_self h0S S.card hq₁C
        have hq₂S : q₂ ∈ S := reach_sub_self h0S S.card hq₂C
        have hq₁nA : q₁ ∉ A := (mem_sdiff.mp (hSI hq₁S)).2
        have hq₂nA : q₂ ∉ A := (mem_sdiff.mp (hSI hq₂S)).2
        obtain ⟨d_st, hst_act, hst_d2⟩ := flux_adj hq₁nA hq₂nA (cubeAdj_symm hadj) (w q₁)
        let S' := S.erase q₁
        let w' : ℕ × ℕ × ℕ → ℤ := fun r => w r + d2 d_st r.1 r.2.1 r.2.2
        have hcard_lt : S'.card < n := by rw [← hScard]; exact card_erase_lt_of_mem hq₁S
        have h0S' : (0, 0, 0) ∈ S' := mem_erase.mpr ⟨hq₁_ne0.symm, h0S⟩
        have hq₂S' : q₂ ∈ S' := mem_erase.mpr ⟨hq₂_ne1, hq₂S⟩
        have hw'_out : ∀ q ∈ box M \ S', w' q = 0 := by
          intro q hq
          obtain ⟨hqB, hq_nS'⟩ := mem_sdiff.mp hq
          dsimp only [w']
          rw [hst_d2 q]
          by_cases hq1 : q = q₁
          · rw [hq1]; simp [hq₂_ne1.symm]
          · have hq_nS : q ∉ S := fun hqS => hq_nS' (mem_erase.mpr ⟨hq1, hqS⟩)
            have hq2 : q ≠ q₂ := fun e => hq_nS (e ▸ hq₂S)
            simp [hq1, hq2, hw_out q (mem_sdiff.mpr ⟨hqB, hq_nS⟩)]
        have hw'_cl : ∀ Ω ⊆ S', (0, 0, 0) ∉ Ω →
            (∀ p ∈ Ω, ∀ q ∈ S', CubeAdj p q → q ∈ Ω) → ∑ q ∈ Ω, w' q = 0 := by
          intro Ω hΩS' h0Ω hΩcl
          have hdisj := comp_disjoint_of_closed' h0S' h0Ω hΩcl
          have hq₂_nΩ : q₂ ∉ Ω := hdisj q₂ (hsub_comp (mem_erase.mpr ⟨hq₂_ne1, hq₂C⟩))
          have hq₁_nΩ : q₁ ∉ Ω := fun h => (mem_erase.mp (hΩS' h)).1 rfl
          have hΩ_Scl : ∀ p ∈ Ω, ∀ q ∈ S, CubeAdj p q → q ∈ Ω := by
            intro p hp q hq hadjpq
            by_cases hqq1 : q = q₁
            · exfalso
              have hadjp1 : CubeAdj p q₁ := hqq1 ▸ hadjpq
              have hpC0 : p ∈ C0 := comp_closed h0S q₁ hq₁C p (erase_subset _ _ (hΩS' hp)) (cubeAdj_symm hadjp1)
              have hp_ne1 : p ≠ q₁ := (mem_erase.mp (hΩS' hp)).1
              exact hdisj p (hsub_comp (mem_erase.mpr ⟨hp_ne1, hpC0⟩)) hp
            · exact hΩcl p hp q (mem_erase.mpr ⟨hqq1, hq⟩) hadjpq
          have heq_sum : ∑ q ∈ Ω, w' q = ∑ q ∈ Ω, w q := by
            refine sum_congr rfl fun q hq => ?_
            have h1 : q ≠ q₁ := fun e => hq₁_nΩ (e ▸ hq)
            have h2 : q ≠ q₂ := fun e => hq₂_nΩ (e ▸ hq)
            dsimp only [w']; rw [hst_d2 q]; simp [h1, h2]
          rw [heq_sum]
          exact hw_cl Ω (hΩS'.trans (erase_subset _ _)) h0Ω hΩ_Scl
        obtain ⟨d_rest, hrest_act, hrest_d2⟩ := ih S'.card hcard_lt S' rfl
          (erase_subset _ _ |>.trans hSI) h0S' w' hw'_out hw'_cl
        refine ⟨addC2 d_st d_rest, vanishesOnAct_add hst_act hrest_act, fun q hqB => ?_⟩
        rw [d2_add, hrest_d2 q hqB]
        dsimp only [w']; ring
      · have hC0_all : ∀ y ∈ C0, y = (0, 0, 0) := fun y hy => by
          by_contra hne; exact hC0_nt ⟨y, hy, hne⟩
        obtain ⟨q₀, hq₀S, hq₀_ne0⟩ := hS_ex
        let C := comp S q₀
        have h0_nC : (0, 0, 0) ∉ C := by
          intro h0C
          have hsym : ∀ k, ∀ x ∈ reach S q₀ k, q₀ ∈ comp S x := by
            intro k; induction k with
            | zero => intro x hx; rw [mem_singleton.mp hx]; exact reach_mono S q₀ (Nat.zero_le _) (mem_reach_zero S q₀)
            | succ k ihk =>
              intro x hx
              rcases mem_union.mp hx with hx1 | hx2
              · exact ihk x hx1
              · obtain ⟨hxS, p, hp, hadjp⟩ := mem_filter.mp hx2
                have hpS : p ∈ S := reach_sub_self hq₀S k hp
                have hp_in_x : p ∈ comp S x := comp_closed hxS x (reach_mono S x (Nat.zero_le _) (mem_reach_zero S x)) p hpS (cubeAdj_symm hadjp)
                exact comp_sub_of_closed hp_in_x (comp_closed hxS) S.card (ihk p hp)
          exact hq₀_ne0 (hC0_all q₀ (hsym S.card (0, 0, 0) h0C))
        have hC_sum : ∑ q ∈ C, w q = 0 :=
          hw_cl C (reach_sub_self hq₀S S.card) h0_nC (comp_closed hq₀S)
        by_cases hC_nt : ∃ y ∈ C, y ≠ q₀
        · obtain ⟨q₁, hq₁C, q₂, hq₂C, hq₁_ne_q₀, hq₂_ne1, hadj, hsub_comp⟩ :=
            exists_peel_leaf hq₀S hC_nt
          have hq₁S : q₁ ∈ S := reach_sub_self hq₀S S.card hq₁C
          have hq₂S : q₂ ∈ S := reach_sub_self hq₀S S.card hq₂C
          have hq₁_ne0 : q₁ ≠ (0, 0, 0) := fun e => h0_nC (e ▸ hq₁C)
          have hq₁nA : q₁ ∉ A := (mem_sdiff.mp (hSI hq₁S)).2
          have hq₂nA : q₂ ∉ A := (mem_sdiff.mp (hSI hq₂S)).2
          obtain ⟨d_st, hst_act, hst_d2⟩ := flux_adj hq₁nA hq₂nA (cubeAdj_symm hadj) (w q₁)
          let S' := S.erase q₁
          let w' : ℕ × ℕ × ℕ → ℤ := fun r => w r + d2 d_st r.1 r.2.1 r.2.2
          have hcard_lt : S'.card < n := by rw [← hScard]; exact card_erase_lt_of_mem hq₁S
          have h0S' : (0, 0, 0) ∈ S' := mem_erase.mpr ⟨hq₁_ne0.symm, h0S⟩
          have hq₀S' : q₀ ∈ S' := mem_erase.mpr ⟨hq₁_ne_q₀.symm, hq₀S⟩
          have hq₂S' : q₂ ∈ S' := mem_erase.mpr ⟨hq₂_ne1, hq₂S⟩
          have hw'_out : ∀ q ∈ box M \ S', w' q = 0 := by
            intro q hq
            obtain ⟨hqB, hq_nS'⟩ := mem_sdiff.mp hq
            dsimp only [w']; rw [hst_d2 q]
            by_cases hq1 : q = q₁
            · rw [hq1]; simp [hq₂_ne1.symm]
            · have hq_nS : q ∉ S := fun hqS => hq_nS' (mem_erase.mpr ⟨hq1, hqS⟩)
              have hq2 : q ≠ q₂ := fun e => hq_nS (e ▸ hq₂S)
              simp [hq1, hq2, hw_out q (mem_sdiff.mpr ⟨hqB, hq_nS⟩)]
          have hw'_cl : ∀ Ω ⊆ S', (0, 0, 0) ∉ Ω →
              (∀ p ∈ Ω, ∀ q ∈ S', CubeAdj p q → q ∈ Ω) → ∑ q ∈ Ω, w' q = 0 := by
            intro Ω hΩS' h0Ω hΩcl
            have hq₁_nΩ : q₁ ∉ Ω := fun h => (mem_erase.mp (hΩS' h)).1 rfl
            by_cases hq₀Ω : q₀ ∈ Ω
            · have hC'_sub : C.erase q₁ ⊆ Ω :=
                hsub_comp.trans (comp_sub_of_closed hq₀Ω hΩcl S'.card)
              have hq₂Ω : q₂ ∈ Ω := hC'_sub (mem_erase.mpr ⟨hq₂_ne1, hq₂C⟩)
              let Ωf := insert q₁ Ω
              have hΩfS : Ωf ⊆ S := insert_subset_iff.mpr ⟨hq₁S, hΩS'.trans (erase_subset _ _)⟩
              have h0Ωf : (0, 0, 0) ∉ Ωf := by
                simp only [Ωf, mem_insert, not_or]; exact ⟨hq₁_ne0.symm, h0Ω⟩
              have hΩf_cl : ∀ p ∈ Ωf, ∀ q ∈ S, CubeAdj p q → q ∈ Ωf := by
                intro p hp q hq hadjpq
                by_cases hqq1 : q = q₁
                · rw [hqq1]; exact mem_insert_self _ _
                · rcases mem_insert.mp hp with hp1 | hpΩ
                  · have hadj1q : CubeAdj q₁ q := hp1 ▸ hadjpq
                    exact mem_insert_of_mem (hC'_sub (mem_erase.mpr ⟨hqq1, comp_closed hq₀S q₁ hq₁C q hq hadj1q⟩))
                  · exact mem_insert_of_mem (hΩcl p hpΩ q (mem_erase.mpr ⟨hqq1, hq⟩) hadjpq)
              have hsum_f : ∑ q ∈ Ωf, w q = 0 := hw_cl Ωf hΩfS h0Ωf hΩf_cl
              rw [sum_insert hq₁_nΩ] at hsum_f
              have hsum_w' : ∑ q ∈ Ω, w' q = ∑ q ∈ Ω, w q + w q₁ := by
                have : ∑ q ∈ Ω, d2 d_st q.1 q.2.1 q.2.2 = w q₁ := by
                  have hcongr : ∑ q ∈ Ω, d2 d_st q.1 q.2.1 q.2.2 =
                      ∑ q ∈ Ω, if q = q₂ then w q₁ else 0 := by
                    refine sum_congr rfl fun q hq => ?_
                    rw [hst_d2 q]
                    have hne1 : q ≠ q₁ := fun e => hq₁_nΩ (e ▸ hq)
                    simp [hne1]
                  rw [hcongr, sum_ite_eq' Ω q₂, if_pos hq₂Ω]
                simp only [w', sum_add_distrib, this]
              linarith
            · have hdisj := comp_disjoint_of_closed' hq₀S' hq₀Ω hΩcl
              have hq₂_nΩ : q₂ ∉ Ω := hdisj q₂ (hsub_comp (mem_erase.mpr ⟨hq₂_ne1, hq₂C⟩))
              have hΩ_Scl : ∀ p ∈ Ω, ∀ q ∈ S, CubeAdj p q → q ∈ Ω := by
                intro p hp q hq hadjpq
                by_cases hqq1 : q = q₁
                · exfalso
                  have hadjp1 : CubeAdj p q₁ := hqq1 ▸ hadjpq
                  have hpC : p ∈ C := comp_closed hq₀S q₁ hq₁C p (erase_subset _ _ (hΩS' hp)) (cubeAdj_symm hadjp1)
                  have hp_ne1 : p ≠ q₁ := (mem_erase.mp (hΩS' hp)).1
                  exact hdisj p (hsub_comp (mem_erase.mpr ⟨hp_ne1, hpC⟩)) hp
                · exact hΩcl p hp q (mem_erase.mpr ⟨hqq1, hq⟩) hadjpq
              have heq_sum : ∑ q ∈ Ω, w' q = ∑ q ∈ Ω, w q := by
                refine sum_congr rfl fun q hq => ?_
                have h1 : q ≠ q₁ := fun e => hq₁_nΩ (e ▸ hq)
                have h2 : q ≠ q₂ := fun e => hq₂_nΩ (e ▸ hq)
                dsimp only [w']; rw [hst_d2 q]; simp [h1, h2]
              rw [heq_sum]
              exact hw_cl Ω (hΩS'.trans (erase_subset _ _)) h0Ω hΩ_Scl
          obtain ⟨d_rest, hrest_act, hrest_d2⟩ := ih S'.card hcard_lt S' rfl
            (erase_subset _ _ |>.trans hSI) h0S' w' hw'_out hw'_cl
          refine ⟨addC2 d_st d_rest, vanishesOnAct_add hst_act hrest_act, fun q hqB => ?_⟩
          rw [d2_add, hrest_d2 q hqB]
          dsimp only [w']; ring
        · have hC_all : ∀ y ∈ C, y = q₀ := fun y hy => by
            by_contra hne; exact hC_nt ⟨y, hy, hne⟩
          have hC_eq : C = {q₀} := Subset.antisymm
            (fun y hy => mem_singleton.mpr (hC_all y hy))
            (singleton_subset_iff.mpr (reach_mono S q₀ (Nat.zero_le _) (mem_reach_zero S q₀)))
          rw [hC_eq, sum_singleton] at hC_sum
          let S' := S.erase q₀
          have hcard_lt : S'.card < n := by rw [← hScard]; exact card_erase_lt_of_mem hq₀S
          have h0S' : (0, 0, 0) ∈ S' := mem_erase.mpr ⟨hq₀_ne0.symm, h0S⟩
          have hw_out' : ∀ q ∈ box M \ S', w q = 0 := by
            intro q hq
            obtain ⟨hqB, hq_nS'⟩ := mem_sdiff.mp hq
            by_cases hqq0 : q = q₀
            · rw [hqq0]; exact hC_sum
            · exact hw_out q (mem_sdiff.mpr ⟨hqB, fun hqS => hq_nS' (mem_erase.mpr ⟨hqq0, hqS⟩)⟩)
          have hw_cl' : ∀ Ω ⊆ S', (0, 0, 0) ∉ Ω →
              (∀ p ∈ Ω, ∀ q ∈ S', CubeAdj p q → q ∈ Ω) → ∑ q ∈ Ω, w q = 0 := by
            intro Ω hΩS' h0Ω hΩcl
            refine hw_cl Ω (hΩS'.trans (erase_subset _ _)) h0Ω (fun p hp q hq hadjpq => ?_)
            by_cases hqq0 : q = q₀
            · exfalso
              have hadjp0 : CubeAdj p q₀ := hqq0 ▸ hadjpq
              have hpC : p ∈ C := comp_closed hq₀S q₀ (reach_mono S q₀ (Nat.zero_le _) (mem_reach_zero S q₀)) p
                (erase_subset _ _ (hΩS' hp)) (cubeAdj_symm hadjp0)
              exact (mem_erase.mp (hΩS' hp)).1 (hC_all p hpC)
            · exact hΩcl p hp q (mem_erase.mpr ⟨hqq0, hq⟩) hadjpq
          exact ih S'.card hcard_lt S' rfl (erase_subset _ _ |>.trans hSI) h0S' w hw_out' hw_cl'

lemma lift_mod2_cocycle {M : ℕ} (hM : 4 ≤ M) {A : Finset (ℕ × ℕ × ℕ)}
    (hA : ∀ q ∈ A, 1 ≤ q.1 ∧ q.1 + 2 ≤ M ∧ 1 ≤ q.2.1 ∧ q.2.1 + 2 ≤ M ∧ 1 ≤ q.2.2 ∧ q.2.2 + 2 ≤ M)
    (b0 : Cochain1)
    (heven_xy : ∀ i j k, ActXY A i j k → 2 ∣ (d1 b0).1 i j k)
    (heven_xz : ∀ i j k, ActXZ A i j k → 2 ∣ (d1 b0).2.1 i j k)
    (heven_yz : ∀ i j k, ActYZ A i j k → 2 ∣ (d1 b0).2.2 i j k) :
    ∃ a : Cochain1,
      (∀ i j k, ActXY A i j k → (d1 (subC1 b0 (scaleC1 2 a))).1 i j k = 0) ∧
      (∀ i j k, ActXZ A i j k → (d1 (subC1 b0 (scaleC1 2 a))).2.1 i j k = 0) ∧
      (∀ i j k, ActYZ A i j k → (d1 (subC1 b0 (scaleC1 2 a))).2.2 i j k = 0) := by
  let c_act : Cochain2 :=
    (fun i j k => if actXYB A i j k then (d1 b0).1 i j k / 2 else 0,
     fun i j k => if actXZB A i j k then (d1 b0).2.1 i j k / 2 else 0,
     fun i j k => if actYZB A i j k then (d1 b0).2.2 i j k / 2 else 0)
  let c_inact : Cochain2 :=
    (fun i j k => if actXYB A i j k then 0 else (d1 b0).1 i j k,
     fun i j k => if actXZB A i j k then 0 else (d1 b0).2.1 i j k,
     fun i j k => if actYZB A i j k then 0 else (d1 b0).2.2 i j k)
  have hcin_van : VanishesOnAct A c_inact := by
    refine ⟨fun i j k h => ?_, fun i j k h => ?_, fun i j k h => ?_⟩
    · simp [c_inact, (actXYB_iff A i j k).mpr h]
    · simp [c_inact, (actXZB_iff A i j k).mpr h]
    · simp [c_inact, (actYZB_iff A i j k).mpr h]
  have hdecomp_1 : ∀ i j k, 2 * c_act.1 i j k + c_inact.1 i j k = (d1 b0).1 i j k := by
    intro i j k; dsimp only [c_act, c_inact]
    cases h : actXYB A i j k
    · simp
    · simp only [↓reduceIte, add_zero]
      exact Int.mul_ediv_cancel' (heven_xy i j k ((actXYB_iff A i j k).mp h))
  have hdecomp_2 : ∀ i j k, 2 * c_act.2.1 i j k + c_inact.2.1 i j k = (d1 b0).2.1 i j k := by
    intro i j k; dsimp only [c_act, c_inact]
    cases h : actXZB A i j k
    · simp
    · simp only [↓reduceIte, add_zero]
      exact Int.mul_ediv_cancel' (heven_xz i j k ((actXZB_iff A i j k).mp h))
  have hdecomp_3 : ∀ i j k, 2 * c_act.2.2 i j k + c_inact.2.2 i j k = (d1 b0).2.2 i j k := by
    intro i j k; dsimp only [c_act, c_inact]
    cases h : actYZB A i j k
    · simp
    · simp only [↓reduceIte, add_zero]
      exact Int.mul_ediv_cancel' (heven_yz i j k ((actYZB_iff A i j k).mp h))
  have hd2_rel : ∀ i j k, 2 * d2 c_act i j k + d2 c_inact i j k = 0 := by
    intro i j k
    have : d2 (addC2 (scaleC2 2 c_act) c_inact) i j k = d2 (d1 b0) i j k := by
      simp only [d2, addC2, scaleC2, hdecomp_1, hdecomp_2, hdecomp_3]
    rw [d2_add, d2_scale, d2_d1] at this
    exact this
  let S := box M \ A
  have h0S : (0, 0, 0) ∈ S := by
    refine mem_sdiff.mpr ⟨mem_box_iff.mpr ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega⟩, fun ha => ?_⟩
    have := (hA (0, 0, 0) ha).1; simp at this
  have hw_out : ∀ q ∈ box M \ S, d2 c_act q.1 q.2.1 q.2.2 = 0 := by
    rintro ⟨i, j, k⟩ hq
    have hqA : (i, j, k) ∈ A := by
      obtain ⟨hqB, hqnS⟩ := mem_sdiff.mp hq
      by_contra hqnA; exact hqnS (mem_sdiff.mpr ⟨hqB, hqnA⟩)
    have hin0 : d2 c_inact i j k = 0 := by
      simp only [d2,
        hcin_van.2.2 (i + 1) j k (Or.inr ⟨by omega, hqA⟩),
        hcin_van.2.2 i j k (Or.inl hqA),
        hcin_van.2.1 i (j + 1) k (Or.inr ⟨by omega, hqA⟩),
        hcin_van.2.1 i j k (Or.inl hqA),
        hcin_van.1 i j (k + 1) (Or.inr ⟨by omega, hqA⟩),
        hcin_van.1 i j k (Or.inl hqA)]
      ring
    have hrel := hd2_rel i j k
    dsimp only; linarith
  have hw_cl : ∀ Ω ⊆ S, (0, 0, 0) ∉ Ω →
      (∀ p ∈ Ω, ∀ q ∈ S, CubeAdj p q → q ∈ Ω) → ∑ q ∈ Ω, d2 c_act q.1 q.2.1 q.2.2 = 0 := by
    intro Ω hΩS h0Ω hΩcl
    have hsum_in := sum_d2_vanishes_eq_zero hM hA hΩS h0Ω hΩcl hcin_van
    have hsum_rel : 2 * (∑ q ∈ Ω, d2 c_act q.1 q.2.1 q.2.2) + ∑ q ∈ Ω, d2 c_inact q.1 q.2.1 q.2.2 = 0 := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_eq_zero fun q _ => hd2_rel q.1 q.2.1 q.2.2
    omega
  obtain ⟨d_inact, hdin_van, hdin_d2⟩ := solve_div_on_set (fun q hq => (hA q hq).1)
    S.card S rfl Subset.rfl h0S (fun q => d2 c_act q.1 q.2.1 q.2.2) hw_out hw_cl
  let z := addC2 c_act d_inact
  have hz_d2 : ∀ x < M, ∀ y < M, ∀ w < M, d2 z x y w = 0 := by
    intro x hx y hy w hw
    rw [d2_add, hdin_d2 (x, y, w) (mem_box_iff.mpr ⟨hx, hy, hw⟩)]
    ring
  refine ⟨poincare1 z, ?_, ?_, ?_⟩
  · intro i j k hact
    have hbounds : i < M ∧ j < M ∧ k ≤ M := by
      rcases hact with h | ⟨hk0, h⟩
      · have := hA (i, j, k) h; dsimp at this; omega
      · have := hA (i, j, k - 1) h; dsimp at this; omega
    rw [d1_sub_1, d1_scale_1, d1_poincare1_xy z hz_d2 hbounds.1 hbounds.2.1 hbounds.2.2]
    dsimp only [z, addC2]
    rw [hdin_van.1 i j k hact, add_zero]
    have hdec := hdecomp_1 i j k
    rw [hcin_van.1 i j k hact, add_zero] at hdec
    linarith
  · intro i j k hact
    rw [d1_sub_2, d1_scale_2, d1_poincare1_xz z]
    dsimp only [z, addC2]
    rw [hdin_van.2.1 i j k hact, add_zero]
    have hdec := hdecomp_2 i j k
    rw [hcin_van.2.1 i j k hact, add_zero] at hdec
    linarith
  · intro i j k hact
    rw [d1_sub_3, d1_scale_3, d1_poincare1_yz z]
    dsimp only [z, addC2]
    rw [hdin_van.2.2 i j k hact, add_zero]
    have hdec := hdecomp_3 i j k
    rw [hcin_van.2.2 i j k hact, add_zero] at hdec
    linarith


def dot3 (u v : Fin 3 → ℝ) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

def sgnOf (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

def bitOf (t : ℝ) : ℤ := if 0 ≤ t then 0 else 1

lemma zpow_bitOf (t : ℝ) : (-1 : ℝ) ^ bitOf t = sgnOf t := by
  unfold bitOf sgnOf; split_ifs <;> norm_num

lemma sgnOf_sq (t : ℝ) : sgnOf t ^ 2 = 1 := by
  unfold sgnOf; split_ifs <;> norm_num

lemma sgnOf_mul_self (t : ℝ) : sgnOf t * sgnOf t = 1 := by
  unfold sgnOf; split_ifs <;> norm_num

lemma sgnOf_ne_zero (t : ℝ) : sgnOf t ≠ 0 := by
  unfold sgnOf; split_ifs <;> norm_num

lemma dot3_sq_bound {x y : Fin 3 → ℝ} (hx : dot3 x x = 1) (hy : dot3 y y = 1)
    (hP : ∀ i j : Fin 3, |x i * x j - y i * y j| < 1 / 20) :
    (19 / 20 : ℝ) ^ 2 < (dot3 x y) ^ 2 := by
  have sqb : ∀ i j : Fin 3, (x i * x j - y i * y j) ^ 2 < 1 / 400 := by
    intro i j
    have h := abs_lt.mp (hP i j)
    nlinarith
  have s00 := sqb 0 0; have s01 := sqb 0 1; have s02 := sqb 0 2
  have s10 := sqb 1 0; have s11 := sqb 1 1; have s12 := sqb 1 2
  have s20 := sqb 2 0; have s21 := sqb 2 1; have s22 := sqb 2 2
  have hid : 2 * (dot3 x y) ^ 2 = (dot3 x x) ^ 2 + (dot3 y y) ^ 2 -
      ((x 0 * x 0 - y 0 * y 0) ^ 2 + (x 0 * x 1 - y 0 * y 1) ^ 2 + (x 0 * x 2 - y 0 * y 2) ^ 2 +
       (x 1 * x 0 - y 1 * y 0) ^ 2 + (x 1 * x 1 - y 1 * y 1) ^ 2 + (x 1 * x 2 - y 1 * y 2) ^ 2 +
       (x 2 * x 0 - y 2 * y 0) ^ 2 + (x 2 * x 1 - y 2 * y 1) ^ 2 + (x 2 * x 2 - y 2 * y 2) ^ 2) := by
    simp only [dot3]; ring
  rw [hx, hy] at hid
  nlinarith

lemma same_hemi_dot {u w x : Fin 3 → ℝ}
    (hu : dot3 u u = 1) (hw : dot3 w w = 1) (hx : dot3 x x = 1)
    (hux : (19 / 20 : ℝ) ^ 2 < (dot3 u x) ^ 2)
    (hwx : (19 / 20 : ℝ) ^ 2 < (dot3 w x) ^ 2) :
    4 / 5 < sgnOf (dot3 u x) * sgnOf (dot3 w x) * dot3 u w := by
  let su := sgnOf (dot3 u x)
  let sw := sgnOf (dot3 w x)
  have h1 : 19 / 20 < su * dot3 u x := by dsimp [su, sgnOf]; split_ifs <;> nlinarith
  have h2 : 19 / 20 < sw * dot3 w x := by dsimp [sw, sgnOf]; split_ifs <;> nlinarith
  have hsu2 : su ^ 2 = 1 := sgnOf_sq _
  have hsw2 : sw ^ 2 = 1 := sgnOf_sq _
  have id_u : (su * u 0 - x 0) ^ 2 + (su * u 1 - x 1) ^ 2 + (su * u 2 - x 2) ^ 2 =
      su ^ 2 * dot3 u u + dot3 x x - 2 * (su * dot3 u x) := by simp only [dot3]; ring
  have id_w : (sw * w 0 - x 0) ^ 2 + (sw * w 1 - x 1) ^ 2 + (sw * w 2 - x 2) ^ 2 =
      sw ^ 2 * dot3 w w + dot3 x x - 2 * (sw * dot3 w x) := by simp only [dot3]; ring
  have id_uw : (su * u 0 - sw * w 0) ^ 2 + (su * u 1 - sw * w 1) ^ 2 + (su * u 2 - sw * w 2) ^ 2 =
      su ^ 2 * dot3 u u + sw ^ 2 * dot3 w w - 2 * (su * sw * dot3 u w) := by simp only [dot3]; ring
  rw [hsu2, hu, hx] at id_u
  rw [hsw2, hw, hx] at id_w
  rw [hsu2, hsw2, hu, hw] at id_uw
  nlinarith [sq_nonneg ((su * u 0 - x 0) + (sw * w 0 - x 0)),
             sq_nonneg ((su * u 1 - x 1) + (sw * w 1 - x 1)),
             sq_nonneg ((su * u 2 - x 2) + (sw * w 2 - x 2))]

lemma bitOf_edge_rel {u w x : Fin 3 → ℝ}
    (hu : dot3 u u = 1) (hw : dot3 w w = 1) (hx : dot3 x x = 1)
    (hux : (19 / 20 : ℝ) ^ 2 < (dot3 u x) ^ 2)
    (hwx : (19 / 20 : ℝ) ^ 2 < (dot3 w x) ^ 2) :
    2 ∣ (bitOf (dot3 u w) - (bitOf (dot3 w x) - bitOf (dot3 u x))) ∧
      (-1 : ℝ) ^ bitOf (dot3 u w) = sgnOf (dot3 u x) * sgnOf (dot3 w x) := by
  have hpos := same_hemi_dot hu hw hx hux hwx
  rw [zpow_bitOf]
  by_cases h1 : 0 ≤ dot3 u w <;> by_cases h2 : 0 ≤ dot3 w x <;> by_cases h3 : 0 ≤ dot3 u x <;>
    simp only [bitOf, sgnOf, h1, h2, h3, ↓reduceIte] at hpos ⊢ <;>
    norm_num at hpos <;>
    first | (exfalso; linarith) | refine ⟨by omega, by norm_num⟩

def verts (q : ℕ × ℕ × ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ({q.1, q.1 + 1} : Finset ℕ) ×ˢ (({q.2.1, q.2.1 + 1} : Finset ℕ) ×ˢ ({q.2.2, q.2.2 + 1} : Finset ℕ))

lemma mem_verts_iff {q v : ℕ × ℕ × ℕ} :
    v ∈ verts q ↔ (v.1 = q.1 ∨ v.1 = q.1 + 1) ∧
      (v.2.1 = q.2.1 ∨ v.2.1 = q.2.1 + 1) ∧ (v.2.2 = q.2.2 ∨ v.2.2 = q.2.2 + 1) := by
  simp [verts, mem_product]

def cubeSet (q : ℕ × ℕ × ℕ) : Set (Fin 3 → ℝ) :=
  { y | (q.1 : ℝ) ≤ y 0 ∧ y 0 ≤ (q.1 : ℝ) + 1 ∧
        (q.2.1 : ℝ) ≤ y 1 ∧ y 1 ≤ (q.2.1 : ℝ) + 1 ∧
        (q.2.2 : ℝ) ≤ y 2 ∧ y 2 ≤ (q.2.2 : ℝ) + 1 }

def mq (b : Cochain1) (q v : ℕ × ℕ × ℕ) : ℤ :=
  (if v.1 = q.1 then 0 else b.1 q.1 q.2.1 q.2.2) +
  (if v.2.1 = q.2.1 then 0 else b.2.1 v.1 q.2.1 q.2.2) +
  (if v.2.2 = q.2.2 then 0 else b.2.2 v.1 v.2.1 q.2.2)

lemma mq_base (b : Cochain1) (q : ℕ × ℕ × ℕ) : mq b q q = 0 := by
  simp [mq]

lemma mq_step_z (b : Cochain1) (q : ℕ × ℕ × ℕ) (vi vj : ℕ) :
    mq b q (vi, vj, q.2.2 + 1) - mq b q (vi, vj, q.2.2) = b.2.2 vi vj q.2.2 := by
  simp [mq]

lemma mq_step_y {A : Finset (ℕ × ℕ × ℕ)} {b : Cochain1} {q : ℕ × ℕ × ℕ} (hq : q ∈ A)
    (hyz : ∀ i j k, ActYZ A i j k → (d1 b).2.2 i j k = 0)
    {vi vk : ℕ} (hvi : vi = q.1 ∨ vi = q.1 + 1) (hvk : vk = q.2.2 ∨ vk = q.2.2 + 1) :
    mq b q (vi, q.2.1 + 1, vk) - mq b q (vi, q.2.1, vk) = b.2.1 vi q.2.1 vk := by
  rcases hvk with rfl | rfl
  · simp [mq]
  · have hact : ActYZ A vi q.2.1 q.2.2 := by
      rcases hvi with rfl | rfl
      · exact Or.inl hq
      · exact Or.inr ⟨by omega, hq⟩
    have h0 := hyz vi q.2.1 q.2.2 hact
    simp only [d1] at h0
    simp only [mq, Nat.add_eq_left, one_ne_zero, ↓reduceIte]
    linarith

lemma mq_step_x {A : Finset (ℕ × ℕ × ℕ)} {b : Cochain1} {q : ℕ × ℕ × ℕ} (hq : q ∈ A)
    (hxy : ∀ i j k, ActXY A i j k → (d1 b).1 i j k = 0)
    (hxz : ∀ i j k, ActXZ A i j k → (d1 b).2.1 i j k = 0)
    (hyz : ∀ i j k, ActYZ A i j k → (d1 b).2.2 i j k = 0)
    {vj vk : ℕ} (hvj : vj = q.2.1 ∨ vj = q.2.1 + 1) (hvk : vk = q.2.2 ∨ vk = q.2.2 + 1) :
    mq b q (q.1 + 1, vj, vk) - mq b q (q.1, vj, vk) = b.1 q.1 vj vk := by
  have f_xy0 := hxy q.1 q.2.1 q.2.2 (Or.inl hq)
  have f_xz0 := hxz q.1 q.2.1 q.2.2 (Or.inl hq)
  have f_xz1 := hxz q.1 (q.2.1 + 1) q.2.2 (Or.inr ⟨by omega, hq⟩)
  have f_yz0 := hyz q.1 q.2.1 q.2.2 (Or.inl hq)
  have f_yz1 := hyz (q.1 + 1) q.2.1 q.2.2 (Or.inr ⟨by omega, hq⟩)
  simp only [d1] at f_xy0 f_xz0 f_xz1 f_yz0 f_yz1
  rcases hvj with rfl | rfl <;> rcases hvk with rfl | rfl <;>
    simp only [mq, Nat.add_eq_left, one_ne_zero, ↓reduceIte] <;> linarith

lemma mq_diff_eq {A : Finset (ℕ × ℕ × ℕ)} {b : Cochain1}
    (hxy : ∀ i j k, ActXY A i j k → (d1 b).1 i j k = 0)
    (hxz : ∀ i j k, ActXZ A i j k → (d1 b).2.1 i j k = 0)
    (hyz : ∀ i j k, ActYZ A i j k → (d1 b).2.2 i j k = 0)
    {q q' u v : ℕ × ℕ × ℕ} (hq : q ∈ A) (hq' : q' ∈ A)
    (huq : u ∈ verts q) (huq' : u ∈ verts q')
    (hvq : v ∈ verts q) (hvq' : v ∈ verts q') :
    mq b q' v - mq b q' u = mq b q v - mq b q u := by
  obtain ⟨hu1, hu2, hu3⟩ := mem_verts_iff.mp huq
  obtain ⟨hu1', hu2', hu3'⟩ := mem_verts_iff.mp huq'
  obtain ⟨hv1, hv2, hv3⟩ := mem_verts_iff.mp hvq
  obtain ⟨hv1', hv2', hv3'⟩ := mem_verts_iff.mp hvq'
  have dx : mq b q' (v.1, u.2.1, u.2.2) - mq b q' u = mq b q (v.1, u.2.1, u.2.2) - mq b q u := by
    by_cases h : v.1 = u.1
    · rcases u with ⟨ui, uj, uk⟩; dsimp only at h; subst h; simp
    · have hqi : q'.1 = q.1 := by omega
      rcases hu1 with h0 | h0
      · have hv1_eq : v.1 = q.1 + 1 := by omega
        rcases u with ⟨ui, uj, uk⟩; dsimp only at h0 hu2 hu3 hu2' hu3'
        rw [hv1_eq, h0, ← hqi]
        have s1 := mq_step_x hq' hxy hxz hyz hu2' hu3'
        rw [hqi] at s1 ⊢
        rw [s1, mq_step_x hq hxy hxz hyz hu2 hu3]
      · have hv1_eq : v.1 = q.1 := by omega
        rcases u with ⟨ui, uj, uk⟩; dsimp only at h0 hu2 hu3 hu2' hu3'
        have s1 := mq_step_x hq' hxy hxz hyz hu2' hu3'
        have s2 := mq_step_x hq hxy hxz hyz hu2 hu3
        rw [hqi] at s1
        rw [hv1_eq, h0]; linarith
  have dy : mq b q' (v.1, v.2.1, u.2.2) - mq b q' (v.1, u.2.1, u.2.2) =
      mq b q (v.1, v.2.1, u.2.2) - mq b q (v.1, u.2.1, u.2.2) := by
    by_cases h : v.2.1 = u.2.1
    · rw [h]; simp
    · have hqj : q'.2.1 = q.2.1 := by omega
      rcases hu2 with h0 | h0
      · have hv2_eq : v.2.1 = q.2.1 + 1 := by omega
        have s1 := mq_step_y hq' hyz hv1' hu3'
        have s2 := mq_step_y hq hyz hv1 hu3
        rw [hqj] at s1
        rw [hv2_eq, h0]; linarith
      · have hv2_eq : v.2.1 = q.2.1 := by omega
        have s1 := mq_step_y hq' hyz hv1' hu3'
        have s2 := mq_step_y hq hyz hv1 hu3
        rw [hqj] at s1
        rw [hv2_eq, h0]; linarith
  have dz : mq b q' v - mq b q' (v.1, v.2.1, u.2.2) =
      mq b q v - mq b q (v.1, v.2.1, u.2.2) := by
    rcases v with ⟨vi, vj, vk⟩; dsimp only at hv3 hv3' ⊢
    by_cases h : vk = u.2.2
    · subst h; simp
    · have hqk : q'.2.2 = q.2.2 := by omega
      rcases hu3 with h0 | h0
      · have hvk_eq : vk = q.2.2 + 1 := by omega
        have s1 := mq_step_z b q' vi vj
        have s2 := mq_step_z b q vi vj
        rw [hqk] at s1
        rw [hvk_eq, h0]; linarith
      · have hvk_eq : vk = q.2.2 := by omega
        have s1 := mq_step_z b q' vi vj
        have s2 := mq_step_z b q vi vj
        rw [hqk] at s1
        rw [hvk_eq, h0]; linarith
  linarith

def tent1 (t : ℝ) (n : ℕ) : ℝ := max 0 (1 - |t - (n : ℝ)|)

def tent (y : Fin 3 → ℝ) (v : ℕ × ℕ × ℕ) : ℝ :=
  tent1 (y 0) v.1 * tent1 (y 1) v.2.1 * tent1 (y 2) v.2.2

lemma tent1_nonneg (t : ℝ) (n : ℕ) : 0 ≤ tent1 t n := le_max_left _ _

lemma tent_nonneg (y : Fin 3 → ℝ) (v : ℕ × ℕ × ℕ) : 0 ≤ tent y v :=
  mul_nonneg (mul_nonneg (tent1_nonneg _ _) (tent1_nonneg _ _)) (tent1_nonneg _ _)

lemma tent1_zero_of_out {t : ℝ} {q n : ℕ} (h1 : (q : ℝ) ≤ t) (h2 : t ≤ (q : ℝ) + 1)
    (hn1 : n ≠ q) (hn2 : n ≠ q + 1) : tent1 t n = 0 := by
  unfold tent1
  rw [max_eq_left_iff]
  have hcases : n + 1 ≤ q ∨ q + 2 ≤ n := by omega
  rcases hcases with hle | hge
  · have hleR : (n : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hle
    have : 1 ≤ |t - (n : ℝ)| := le_trans (by linarith) (le_abs_self _)
    linarith
  · have hgeR : (q : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hge
    have : 1 ≤ |t - (n : ℝ)| := le_trans (by linarith) (neg_le_abs _)
    linarith

lemma tent_zero_of_not_mem {q v : ℕ × ℕ × ℕ} {y : Fin 3 → ℝ}
    (hy : y ∈ cubeSet q) (hv : v ∉ verts q) : tent y v = 0 := by
  obtain ⟨h0a, h0b, h1a, h1b, h2a, h2b⟩ := hy
  rw [mem_verts_iff] at hv
  unfold tent
  by_cases c0 : v.1 = q.1 ∨ v.1 = q.1 + 1
  · by_cases c1 : v.2.1 = q.2.1 ∨ v.2.1 = q.2.1 + 1
    · have c2 : ¬ (v.2.2 = q.2.2 ∨ v.2.2 = q.2.2 + 1) := fun h => hv ⟨c0, c1, h⟩
      rw [not_or] at c2
      rw [tent1_zero_of_out h2a h2b c2.1 c2.2, mul_zero]
    · rw [not_or] at c1
      rw [tent1_zero_of_out h1a h1b c1.1 c1.2, mul_zero, zero_mul]
  · rw [not_or] at c0
    rw [tent1_zero_of_out h0a h0b c0.1 c0.2, zero_mul, zero_mul]

lemma tent1_pair_sum {t : ℝ} {q : ℕ} (h1 : (q : ℝ) ≤ t) (h2 : t ≤ (q : ℝ) + 1) :
    tent1 t q + tent1 t (q + 1) = 1 := by
  unfold tent1
  have a1 : |t - (q : ℝ)| = t - (q : ℝ) := abs_of_nonneg (by linarith)
  have a2 : |t - ((q + 1 : ℕ) : ℝ)| = (q : ℝ) + 1 - t := by
    push_cast
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [a1, a2, max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

lemma sum_tent_verts {q : ℕ × ℕ × ℕ} {y : Fin 3 → ℝ} (hy : y ∈ cubeSet q) :
    ∑ v ∈ verts q, tent y v = 1 := by
  obtain ⟨h0a, h0b, h1a, h1b, h2a, h2b⟩ := hy
  have ne0 : q.1 ≠ q.1 + 1 := by omega
  have ne1 : q.2.1 ≠ q.2.1 + 1 := by omega
  have ne2 : q.2.2 ≠ q.2.2 + 1 := by omega
  simp only [verts, tent, sum_product, sum_pair ne0, sum_pair ne1, sum_pair ne2]
  have s0 := tent1_pair_sum h0a h0b
  have s1 := tent1_pair_sum h1a h1b
  have s2 := tent1_pair_sum h2a h2b
  calc _ = (tent1 (y 0) q.1 + tent1 (y 0) (q.1 + 1)) *
           (tent1 (y 1) q.2.1 + tent1 (y 1) (q.2.1 + 1)) *
           (tent1 (y 2) q.2.2 + tent1 (y 2) (q.2.2 + 1)) := by ring
       _ = 1 := by rw [s0, s1, s2]; ring

def uq (b : Cochain1) (ev : ℕ × ℕ × ℕ → Fin 3 → ℝ)
    (q : ℕ × ℕ × ℕ) (y : Fin 3 → ℝ) : Fin 3 → ℂ :=
  let ph : ℂ := Complex.exp (↑(Real.pi * ∑ v ∈ verts q, tent y v * (mq b q v : ℝ)) * Complex.I)
  fun r => ph * ↑(∑ v ∈ verts q, tent y v * ((-1 : ℝ) ^ mq b q v * ev v r))

lemma continuous_tent1 (n : ℕ) : Continuous (fun t : ℝ => tent1 t n) := by
  unfold tent1; fun_prop

lemma continuous_tent (v : ℕ × ℕ × ℕ) : Continuous (fun y : Fin 3 → ℝ => tent y v) := by
  unfold tent
  have c0 : Continuous (fun y : Fin 3 → ℝ => tent1 (y 0) v.1) :=
    (continuous_tent1 v.1).comp (continuous_apply 0)
  have c1 : Continuous (fun y : Fin 3 → ℝ => tent1 (y 1) v.2.1) :=
    (continuous_tent1 v.2.1).comp (continuous_apply 1)
  have c2 : Continuous (fun y : Fin 3 → ℝ => tent1 (y 2) v.2.2) :=
    (continuous_tent1 v.2.2).comp (continuous_apply 2)
  exact (c0.mul c1).mul c2

lemma continuous_uq (b : Cochain1) (ev : ℕ × ℕ × ℕ → Fin 3 → ℝ) (q : ℕ × ℕ × ℕ) :
    Continuous (uq b ev q) := by
  unfold uq
  refine continuous_pi fun r => ?_
  have cs1 : Continuous (fun y : Fin 3 → ℝ => ∑ v ∈ verts q, tent y v * (mq b q v : ℝ)) :=
    continuous_finsetSum _ fun v _ => (continuous_tent v).mul continuous_const
  have cs2 : Continuous (fun y : Fin 3 → ℝ => ∑ v ∈ verts q, tent y v * ((-1 : ℝ) ^ mq b q v * ev v r)) :=
    continuous_finsetSum _ fun v _ => (continuous_tent v).mul continuous_const
  have cph : Continuous (fun y : Fin 3 → ℝ =>
      Complex.exp (↑(Real.pi * ∑ v ∈ verts q, tent y v * (mq b q v : ℝ)) * Complex.I)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_const.mul cs1)).mul continuous_const)
  exact cph.mul (Complex.continuous_ofReal.comp cs2)

lemma exp_int_pi_I (k : ℤ) :
    Complex.exp (↑(Real.pi * (k : ℝ)) * Complex.I) = (-1 : ℂ) ^ k := by
  have h : (↑(Real.pi * (k : ℝ)) * Complex.I : ℂ) = (k : ℂ) * (↑Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul, Complex.exp_pi_mul_I]

lemma uq_eq_on_inter {A : Finset (ℕ × ℕ × ℕ)} {b : Cochain1}
    (hxy : ∀ i j k, ActXY A i j k → (d1 b).1 i j k = 0)
    (hxz : ∀ i j k, ActXZ A i j k → (d1 b).2.1 i j k = 0)
    (hyz : ∀ i j k, ActYZ A i j k → (d1 b).2.2 i j k = 0)
    (ev : ℕ × ℕ × ℕ → Fin 3 → ℝ)
    {q q' : ℕ × ℕ × ℕ} (hq : q ∈ A) (hq' : q' ∈ A)
    {y : Fin 3 → ℝ} (hyq : y ∈ cubeSet q) (hyq' : y ∈ cubeSet q') :
    uq b ev q' y = uq b ev q y := by
  have hsum1 := sum_tent_verts hyq
  obtain ⟨u, huq, htu_ne⟩ : ∃ u ∈ verts q, tent y u ≠ 0 := by
    by_contra hall; push Not at hall
    have : ∑ v ∈ verts q, tent y v = 0 := sum_eq_zero fun v hv => by rw [hall v hv]
    linarith
  have huq' : u ∈ verts q' := by
    by_contra hnot; exact htu_ne (tent_zero_of_not_mem hyq' hnot)
  let k : ℤ := mq b q' u - mq b q u
  let U := verts q ∪ verts q'
  have shift_on : ∀ v, tent y v ≠ 0 → mq b q' v = mq b q v + k := by
    intro v htv
    have hvq : v ∈ verts q := by by_contra hn; exact htv (tent_zero_of_not_mem hyq hn)
    have hvq' : v ∈ verts q' := by by_contra hn; exact htv (tent_zero_of_not_mem hyq' hn)
    have hd := mq_diff_eq hxy hxz hyz hq hq' huq huq' hvq hvq'
    dsimp only [k]; linarith
  have sum_ph : ∑ v ∈ verts q', tent y v * (mq b q' v : ℝ) =
      (∑ v ∈ verts q, tent y v * (mq b q v : ℝ)) + (k : ℝ) := by
    have e1 : ∑ v ∈ verts q', tent y v * (mq b q' v : ℝ) = ∑ v ∈ U, tent y v * (mq b q' v : ℝ) :=
      sum_subset subset_union_right fun v _ hvn => by rw [tent_zero_of_not_mem hyq' hvn, zero_mul]
    have e2 : ∑ v ∈ verts q, tent y v * (mq b q v : ℝ) = ∑ v ∈ U, tent y v * (mq b q v : ℝ) :=
      sum_subset subset_union_left fun v _ hvn => by rw [tent_zero_of_not_mem hyq hvn, zero_mul]
    have e3 : ∑ v ∈ U, tent y v = 1 := by
      rw [← hsum1]
      exact (sum_subset subset_union_left fun v _ hvn => tent_zero_of_not_mem hyq hvn).symm
    have ek : (k : ℝ) = (∑ v ∈ U, tent y v) * (k : ℝ) := by rw [e3, one_mul]
    have e4 : ∑ v ∈ U, tent y v * (mq b q' v : ℝ) =
        ∑ v ∈ U, (tent y v * (mq b q v : ℝ) + tent y v * (k : ℝ)) := by
      refine sum_congr rfl fun v _ => ?_
      by_cases htv : tent y v = 0
      · simp [htv]
      · rw [shift_on v htv]; push_cast; ring
    rw [e1, e2, e4, sum_add_distrib, ← sum_mul, ← ek]
  funext r
  have sum_vec : ∑ v ∈ verts q', tent y v * ((-1 : ℝ) ^ mq b q' v * ev v r) =
      ((-1 : ℝ) ^ k) * ∑ v ∈ verts q, tent y v * ((-1 : ℝ) ^ mq b q v * ev v r) := by
    have e1 : ∑ v ∈ verts q', tent y v * ((-1 : ℝ) ^ mq b q' v * ev v r) =
        ∑ v ∈ U, tent y v * ((-1 : ℝ) ^ mq b q' v * ev v r) :=
      sum_subset subset_union_right fun v _ hvn => by rw [tent_zero_of_not_mem hyq' hvn, zero_mul]
    have e2 : ∑ v ∈ verts q, tent y v * ((-1 : ℝ) ^ mq b q v * ev v r) =
        ∑ v ∈ U, tent y v * ((-1 : ℝ) ^ mq b q v * ev v r) :=
      sum_subset subset_union_left fun v _ hvn => by rw [tent_zero_of_not_mem hyq hvn, zero_mul]
    rw [e1, e2, mul_sum]
    refine sum_congr rfl fun v _ => ?_
    by_cases htv : tent y v = 0
    · simp [htv]
    · rw [shift_on v htv, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
      ring
  unfold uq
  rw [sum_ph, sum_vec]
  have hexp : Complex.exp (↑(Real.pi * ((∑ v ∈ verts q, tent y v * (mq b q v : ℝ)) + (k : ℝ))) * Complex.I) =
      Complex.exp (↑(Real.pi * ∑ v ∈ verts q, tent y v * (mq b q v : ℝ)) * Complex.I) * (-1 : ℂ) ^ k := by
    have hsplit : (↑(Real.pi * ((∑ v ∈ verts q, tent y v * (mq b q v : ℝ)) + (k : ℝ))) * Complex.I : ℂ) =
        ↑(Real.pi * ∑ v ∈ verts q, tent y v * (mq b q v : ℝ)) * Complex.I +
        ↑(Real.pi * (k : ℝ)) * Complex.I := by push_cast; ring
    rw [hsplit, Complex.exp_add, exp_int_pi_I]
  have hc (S : ℝ) : (↑((-1 : ℝ) ^ k * S) : ℂ) = (-1 : ℂ) ^ k * ↑S := by push_cast; ring
  rw [hexp, hc]
  have h1 : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← mul_zpow, show (-1 : ℂ) * (-1 : ℂ) = 1 by ring, one_zpow]
  calc _ = Complex.exp (↑(Real.pi * ∑ v ∈ verts q, tent y v * (mq b q v : ℝ)) * Complex.I) *
           (((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) *
            ↑(∑ v ∈ verts q, tent y v * ((-1 : ℝ) ^ mq b q v * ev v r))) := by ring
       _ = _ := by rw [h1, one_mul]


lemma paste_closed_finset {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    (defaultE : E) {α : Type*} (S : Finset α) (F : α → Set X) (g : α → X → E)
    (hclosed : ∀ q ∈ S, IsClosed (F q))
    (hcont : ∀ q ∈ S, Continuous (g q))
    (hcover : ∀ x : X, ∃ q ∈ S, x ∈ F q)
    (hcompat : ∀ q ∈ S, ∀ q' ∈ S, ∀ x, x ∈ F q → x ∈ F q' → g q x = g q' x) :
    ∃ G : X → E, Continuous G ∧ ∀ q ∈ S, ∀ x ∈ F q, G x = g q x := by
  let G : X → E := fun x =>
    if h : ∃ q ∈ S, x ∈ F q then g h.choose x else defaultE
  have hG_eq : ∀ q ∈ S, ∀ x ∈ F q, G x = g q x := by
    intro q hq x hx
    have hex : ∃ q' ∈ S, x ∈ F q' := ⟨q, hq, hx⟩
    dsimp only [G]
    rw [dif_pos hex]
    obtain ⟨hq1, hx1⟩ := hex.choose_spec
    exact hcompat hex.choose hq1 q hq x hx1 hx
  refine ⟨G, continuous_iff_isClosed.mpr fun t ht => ?_, hG_eq⟩
  have heq : G ⁻¹' t = ⋃ q ∈ S, (F q ∩ g q ⁻¹' t) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    constructor
    · intro hGx
      obtain ⟨q, hq, hx⟩ := hcover x
      exact ⟨q, hq, hx, by rwa [← hG_eq q hq x hx]⟩
    · rintro ⟨q, hq, hx, hgx⟩
      rwa [hG_eq q hq x hx]
  rw [heq]
  exact S.finite_toSet.isClosed_biUnion fun q hq =>
    (hclosed q hq).inter (ht.preimage (hcont q hq))

lemma zpow_sub_two_mul (m n : ℤ) : (-1 : ℝ) ^ (m - 2 * n) = (-1 : ℝ) ^ m := by
  rw [zpow_sub₀ (by norm_num : (-1 : ℝ) ≠ 0), zpow_mul, show (-1 : ℝ) ^ (2 : ℤ) = 1 by norm_num,
    one_zpow, div_one]

lemma zpow_mq_walk {A : Finset (ℕ × ℕ × ℕ)} {b0 a : Cochain1}
    (hxy : ∀ i j k, ActXY A i j k → (d1 (subC1 b0 (scaleC1 2 a))).1 i j k = 0)
    (hxz : ∀ i j k, ActXZ A i j k → (d1 (subC1 b0 (scaleC1 2 a))).2.1 i j k = 0)
    (hyz : ∀ i j k, ActYZ A i j k → (d1 (subC1 b0 (scaleC1 2 a))).2.2 i j k = 0)
    (ev : ℕ × ℕ × ℕ → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    {q : ℕ × ℕ × ℕ} (hq : q ∈ A)
    (hx1 : dot3 x x = 1)
    (hev_unit : ∀ v ∈ verts q, dot3 (ev v) (ev v) = 1)
    (hev_near : ∀ v ∈ verts q, (19 / 20 : ℝ) ^ 2 < (dot3 (ev v) x) ^ 2)
    (hb0_x : ∀ i j k, b0.1 i j k = bitOf (dot3 (ev (i, j, k)) (ev (i + 1, j, k))))
    (hb0_y : ∀ i j k, b0.2.1 i j k = bitOf (dot3 (ev (i, j, k)) (ev (i, j + 1, k))))
    (hb0_z : ∀ i j k, b0.2.2 i j k = bitOf (dot3 (ev (i, j, k)) (ev (i, j, k + 1))))
    {v : ℕ × ℕ × ℕ} (hv : v ∈ verts q) :
    (-1 : ℝ) ^ mq (subC1 b0 (scaleC1 2 a)) q v =
      sgnOf (dot3 (ev q) x) * sgnOf (dot3 (ev v) x) := by
  let b := subC1 b0 (scaleC1 2 a)
  obtain ⟨hv1, hv2, hv3⟩ := mem_verts_iff.mp hv
  have hq_in : q ∈ verts q := mem_verts_iff.mpr ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  have v1_in : (v.1, q.2.1, q.2.2) ∈ verts q := mem_verts_iff.mpr ⟨hv1, Or.inl rfl, Or.inl rfl⟩
  have v2_in : (v.1, v.2.1, q.2.2) ∈ verts q := mem_verts_iff.mpr ⟨hv1, hv2, Or.inl rfl⟩
  have sx : (-1 : ℝ) ^ mq b q (v.1, q.2.1, q.2.2) =
      sgnOf (dot3 (ev q) x) * sgnOf (dot3 (ev (v.1, q.2.1, q.2.2)) x) := by
    rcases hv1 with h1 | h1
    · have heq : (v.1, q.2.1, q.2.2) = q := Prod.ext h1 rfl
      rw [heq, mq_base, zpow_zero, sgnOf_mul_self]
    · have hst := mq_step_x hq hxy hxz hyz (Or.inl rfl : q.2.1 = q.2.1 ∨ _) (Or.inl rfl : q.2.2 = q.2.2 ∨ _)
      have hq_eta : (q.1, q.2.1, q.2.2) = q := rfl
      rw [hq_eta, mq_base, sub_zero] at hst
      rw [h1, hst]
      dsimp only [b, subC1, scaleC1]
      rw [zpow_sub_two_mul, hb0_x, hq_eta]
      exact (bitOf_edge_rel (hev_unit q hq_in) (hev_unit _ (h1 ▸ v1_in)) hx1
        (hev_near q hq_in) (hev_near _ (h1 ▸ v1_in))).2
  have sy : (-1 : ℝ) ^ mq b q (v.1, v.2.1, q.2.2) =
      sgnOf (dot3 (ev q) x) * sgnOf (dot3 (ev (v.1, v.2.1, q.2.2)) x) := by
    rcases hv2 with h2 | h2
    · rw [h2]; exact sx
    · have hst := mq_step_y hq hyz hv1 (Or.inl rfl : q.2.2 = q.2.2 ∨ _)
      have heq : mq b q (v.1, q.2.1 + 1, q.2.2) = mq b q (v.1, q.2.1, q.2.2) + b.2.1 v.1 q.2.1 q.2.2 := by linarith
      rw [h2, heq, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), sx]
      have hb_eq : (-1 : ℝ) ^ b.2.1 v.1 q.2.1 q.2.2 =
          sgnOf (dot3 (ev (v.1, q.2.1, q.2.2)) x) * sgnOf (dot3 (ev (v.1, q.2.1 + 1, q.2.2)) x) := by
        dsimp only [b, subC1, scaleC1]
        rw [zpow_sub_two_mul, hb0_y]
        exact (bitOf_edge_rel (hev_unit _ v1_in) (hev_unit _ (h2 ▸ v2_in)) hx1
          (hev_near _ v1_in) (hev_near _ (h2 ▸ v2_in))).2
      rw [hb_eq]
      calc _ = sgnOf (dot3 (ev q) x) *
               (sgnOf (dot3 (ev (v.1, q.2.1, q.2.2)) x) * sgnOf (dot3 (ev (v.1, q.2.1, q.2.2)) x)) *
               sgnOf (dot3 (ev (v.1, q.2.1 + 1, q.2.2)) x) := by ring
           _ = _ := by rw [sgnOf_mul_self, mul_one]
  rcases v with ⟨vi, vj, vk⟩
  dsimp only at hv1 hv2 hv3 v2_in sy ⊢
  rcases hv3 with h3 | h3
  · subst h3; exact sy
  · have hst := mq_step_z b q vi vj
    have heq : mq b q (vi, vj, q.2.2 + 1) = mq b q (vi, vj, q.2.2) + b.2.2 vi vj q.2.2 := by linarith
    rw [h3, heq, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), sy]
    have hb_eq : (-1 : ℝ) ^ b.2.2 vi vj q.2.2 =
        sgnOf (dot3 (ev (vi, vj, q.2.2)) x) * sgnOf (dot3 (ev (vi, vj, q.2.2 + 1)) x) := by
      dsimp only [b, subC1, scaleC1]
      rw [zpow_sub_two_mul, hb0_z]
      exact (bitOf_edge_rel (hev_unit _ v2_in) (hev_unit _ (h3 ▸ hv)) hx1
        (hev_near _ v2_in) (hev_near _ (h3 ▸ hv))).2
    rw [hb_eq]
    calc _ = sgnOf (dot3 (ev q) x) *
             (sgnOf (dot3 (ev (vi, vj, q.2.2)) x) * sgnOf (dot3 (ev (vi, vj, q.2.2)) x)) *
             sgnOf (dot3 (ev (vi, vj, q.2.2 + 1)) x) := by ring
         _ = _ := by rw [sgnOf_mul_self, mul_one]

end OMA.InscribedSquareH1Helpers

end

open OMA.InscribedSquareH1Helpers in
theorem OMA.solution : OMA.R_InscribedSquare_exists_inscribed_rectangle_R1_H2_R1_H2_R1.H1 := by
  classical
  intro K hK P hP hP_rank1
  by_cases hK_ne : K.Nonempty
  · have : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let coords : EuclideanSpace ℝ (Fin 2) × ℝ → Fin 3 → ℝ :=
      fun p => ![p.1 0, p.1 1, p.2]
    have hcont_coords : Continuous coords := by
      refine continuous_pi fun r => ?_
      fin_cases r
      · dsimp [coords]; exact (PiLp.continuous_apply 2 _ 0).comp continuous_fst
      · dsimp [coords]; exact (PiLp.continuous_apply 2 _ 1).comp continuous_fst
      · dsimp [coords]; exact continuous_snd
    have hdist_coords : ∀ p q : EuclideanSpace ℝ (Fin 2) × ℝ,
        dist p q ≤ |coords p 0 - coords q 0| + |coords p 1 - coords q 1| + |coords p 2 - coords q 2| := by
      intro p q
      have hd1 : dist p.1 q.1 ≤ |coords p 0 - coords q 0| + |coords p 1 - coords q 1| := by
        rw [dist_eq_norm]
        have hsq := EuclideanSpace.real_norm_sq_eq (p.1 - q.1)
        rw [Fin.sum_univ_two] at hsq
        simp only [PiLp.sub_apply] at hsq
        have h0 := abs_nonneg (p.1 0 - q.1 0)
        have h1 := abs_nonneg (p.1 1 - q.1 1)
        have h2 := norm_nonneg (p.1 - q.1)
        have h3 : (p.1 0 - q.1 0) ^ 2 = |p.1 0 - q.1 0| ^ 2 := (sq_abs _).symm
        have h4 : (p.1 1 - q.1 1) ^ 2 = |p.1 1 - q.1 1| ^ 2 := (sq_abs _).symm
        dsimp [coords]
        nlinarith
      have hd2 : dist p.2 q.2 ≤ |coords p 2 - coords q 2| := by
        simp [Real.dist_eq, coords]
      rw [Prod.dist_eq]
      exact max_le (le_trans hd1 (by linarith [abs_nonneg (coords p 2 - coords q 2)]))
        (le_trans hd2 (by linarith [abs_nonneg (coords p 0 - coords q 0), abs_nonneg (coords p 1 - coords q 1)]))
    obtain ⟨R₁, hR₁⟩ := (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin 2) × ℝ)).mp hK.isBounded
    let R₀ : ℝ := max 1 R₁
    have hR₀_pos : 0 < R₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hcoords_bound : ∀ k : K, ∀ r : Fin 3, |coords k.val r| ≤ R₀ := by
      intro k r
      have hkB : dist k.val 0 ≤ R₁ := Metric.mem_closedBall.mp (hR₁ k.2)
      have hkR₀ : dist k.val 0 ≤ R₀ := hkB.trans (le_max_right _ _)
      rw [Prod.dist_eq] at hkR₀
      fin_cases r
      · dsimp [coords]
        have hle : ‖k.val.1 0‖ ≤ ‖k.val.1‖ := PiLp.norm_apply_le k.val.1 0
        rw [Real.norm_eq_abs] at hle
        exact hle.trans (by simpa [dist_zero_right] using (le_max_left _ _).trans hkR₀)
      · dsimp [coords]
        have hle : ‖k.val.1 1‖ ≤ ‖k.val.1‖ := PiLp.norm_apply_le k.val.1 1
        rw [Real.norm_eq_abs] at hle
        exact hle.trans (by simpa [dist_zero_right] using (le_max_left _ _).trans hkR₀)
      · dsimp [coords]
        exact (by simpa [Real.dist_eq] using (le_max_right _ _).trans hkR₀)
    have hP_uc : UniformContinuous P := CompactSpace.uniformContinuous_of_continuous hP
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformContinuous_iff.mp hP_uc (1 / 20) (by norm_num)
    let N : ℕ := ⌊12 * R₀ / δ⌋₊ + 1
    have hN_pos : 0 < N := Nat.succ_pos _
    have hN_posR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
    have hN_gt : 12 * R₀ / δ < (N : ℝ) := by
      dsimp [N]; push_cast; exact Nat.lt_floor_add_one _
    let h : ℝ := 2 * R₀ / (N : ℝ)
    have hh_pos : 0 < h := div_pos (by linarith) hN_posR
    have h6h_lt : 6 * h < δ := by
      dsimp [h]
      rw [show 6 * (2 * R₀ / (N : ℝ)) = 12 * R₀ / (N : ℝ) by ring]
      rw [div_lt_iff₀ hN_posR]
      have := (div_lt_iff₀ hδ_pos).mp hN_gt
      linarith
    let M : ℕ := N + 4
    have hM4 : 4 ≤ M := by dsimp [M]; omega
    let φ : K → Fin 3 → ℝ := fun k r => (coords k.val r + R₀) / h + 2
    have hφ_cont : Continuous φ := by
      refine continuous_pi fun r => ?_
      exact (((((continuous_apply r).comp hcont_coords).comp continuous_subtype_val).add continuous_const).div_const h).add continuous_const
    have hφ_bounds : ∀ k : K, ∀ r : Fin 3, 2 ≤ φ k r ∧ φ k r ≤ (N : ℝ) + 2 := by
      intro k r
      have hb := abs_le.mp (hcoords_bound k r)
      dsimp [φ]
      constructor
      · have : 0 ≤ (coords k.val r + R₀) / h := div_nonneg (by linarith) hh_pos.le
        linarith
      · have htop : (coords k.val r + R₀) / h ≤ (N : ℝ) := by
          rw [div_le_iff₀ hh_pos]
          have : (N : ℝ) * h = 2 * R₀ := by dsimp [h]; field_simp
          linarith
        linarith
    have hP_close_of_phi : ∀ k₁ k₂ : K, (∀ r : Fin 3, |φ k₁ r - φ k₂ r| ≤ 2) →
        ∀ i j : Fin 3, |P k₁ i j - P k₂ i j| < 1 / 20 := by
      intro k₁ k₂ hclose i j
      have hcoord_diff : ∀ r : Fin 3, |coords k₁.val r - coords k₂.val r| ≤ 2 * h := by
        intro r
        have heq : coords k₁.val r - coords k₂.val r = h * (φ k₁ r - φ k₂ r) := by
          dsimp [φ]; field_simp; ring
        rw [heq, abs_mul, abs_of_pos hh_pos]
        nlinarith [hclose r]
      have hdist_lt : dist k₁ k₂ < δ := by
        change dist k₁.val k₂.val < δ
        have hd := hdist_coords k₁.val k₂.val
        have c0 := hcoord_diff 0; have c1 := hcoord_diff 1; have c2 := hcoord_diff 2
        linarith
      have hdP := hδ hdist_lt
      have h1 : dist (P k₁ i j) (P k₂ i j) ≤ dist (P k₁ i) (P k₂ i) := dist_le_pi_dist (P k₁ i) (P k₂ i) j
      have h2 : dist (P k₁ i) (P k₂ i) ≤ dist (P k₁) (P k₂) := dist_le_pi_dist (P k₁) (P k₂) i
      simpa [Real.dist_eq] using (h1.trans h2).trans_lt hdP
    let xk : K → Fin 3 → ℝ := fun k i => (hP_rank1 k).choose.val i
    have hxk_P : ∀ k : K, ∀ i j : Fin 3, P k i j = xk k i * xk k j :=
      fun k i j => (hP_rank1 k).choose_spec i j
    have hxk_unit : ∀ k : K, dot3 (xk k) (xk k) = 1 := by
      intro k
      have hs : ‖(hP_rank1 k).choose.val‖ = 1 := mem_sphere_zero_iff_norm.mp (hP_rank1 k).choose.2
      have hsq := EuclideanSpace.real_norm_sq_eq (hP_rank1 k).choose.val
      rw [hs, Fin.sum_univ_three] at hsq
      simp only [dot3, xk]
      linarith
    let A : Finset (ℕ × ℕ × ℕ) := (box M).filter (fun q => ∃ k : K, φ k ∈ cubeSet q)
    have hA_bounds : ∀ q ∈ A, 1 ≤ q.1 ∧ q.1 + 2 ≤ M ∧ 1 ≤ q.2.1 ∧ q.2.1 + 2 ≤ M ∧ 1 ≤ q.2.2 ∧ q.2.2 + 2 ≤ M := by
      rintro ⟨qi, qj, qk⟩ hq
      obtain ⟨_, k, h0a, h0b, h1a, h1b, h2a, h2b⟩ := mem_filter.mp hq
      have b0 := hφ_bounds k 0; have b1 := hφ_bounds k 1; have b2 := hφ_bounds k 2
      dsimp only at h0a h0b h1a h1b h2a h2b ⊢
      have i1 : (1 : ℝ) ≤ (qi : ℝ) := by linarith
      have i2 : (qi : ℝ) ≤ (N : ℝ) + 2 := by linarith
      have j1 : (1 : ℝ) ≤ (qj : ℝ) := by linarith
      have j2 : (qj : ℝ) ≤ (N : ℝ) + 2 := by linarith
      have k1 : (1 : ℝ) ≤ (qk : ℝ) := by linarith
      have k2 : (qk : ℝ) ≤ (N : ℝ) + 2 := by linarith
      have ni1 : 1 ≤ qi := by exact_mod_cast i1
      have ni2 : qi ≤ N + 2 := by exact_mod_cast i2
      have nj1 : 1 ≤ qj := by exact_mod_cast j1
      have nj2 : qj ≤ N + 2 := by exact_mod_cast j2
      have nk1 : 1 ≤ qk := by exact_mod_cast k1
      have nk2 : qk ≤ N + 2 := by exact_mod_cast k2
      dsimp [M]; omega
    have hcover : ∀ k : K, ∃ q ∈ A, φ k ∈ cubeSet q := by
      intro k
      let q : ℕ × ℕ × ℕ := (⌊φ k 0⌋₊, ⌊φ k 1⌋₊, ⌊φ k 2⌋₊)
      have b0 := hφ_bounds k 0; have b1 := hφ_bounds k 1; have b2 := hφ_bounds k 2
      have hcube : φ k ∈ cubeSet q := by
        refine ⟨Nat.floor_le (by linarith), (Nat.lt_floor_add_one _).le,
                Nat.floor_le (by linarith), (Nat.lt_floor_add_one _).le,
                Nat.floor_le (by linarith), (Nat.lt_floor_add_one _).le⟩
      have hqB : q ∈ box M := by
        have l0 : (⌊φ k 0⌋₊ : ℝ) ≤ (N : ℝ) + 2 := (Nat.floor_le (by linarith)).trans b0.2
        have l1 : (⌊φ k 1⌋₊ : ℝ) ≤ (N : ℝ) + 2 := (Nat.floor_le (by linarith)).trans b1.2
        have l2 : (⌊φ k 2⌋₊ : ℝ) ≤ (N : ℝ) + 2 := (Nat.floor_le (by linarith)).trans b2.2
        have n0 : ⌊φ k 0⌋₊ ≤ N + 2 := by exact_mod_cast l0
        have n1 : ⌊φ k 1⌋₊ ≤ N + 2 := by exact_mod_cast l1
        have n2 : ⌊φ k 2⌋₊ ≤ N + 2 := by exact_mod_cast l2
        exact mem_box_iff.mpr ⟨by dsimp [q, M]; omega, by dsimp [q, M]; omega, by dsimp [q, M]; omega⟩
      exact ⟨q, mem_filter.mpr ⟨hqB, k, hcube⟩, hcube⟩
    let k_def : K := ⟨hK_ne.some, hK_ne.some_mem⟩
    let kq : ℕ × ℕ × ℕ → K := fun q => if hq : ∃ k : K, φ k ∈ cubeSet q then hq.choose else k_def
    have hkq_in : ∀ q ∈ A, φ (kq q) ∈ cubeSet q := by
      intro q hq
      obtain ⟨_, hex⟩ := mem_filter.mp hq
      dsimp only [kq]; rw [dif_pos hex]; exact hex.choose_spec
    let xq : ℕ × ℕ × ℕ → Fin 3 → ℝ := fun q => xk (kq q)
    let ev : ℕ × ℕ × ℕ → Fin 3 → ℝ := fun v =>
      if hv : ∃ q ∈ A, v ∈ verts q then xq hv.choose else ![1, 0, 0]
    have hphi_vert : ∀ q : ℕ × ℕ × ℕ, ∀ y : Fin 3 → ℝ, y ∈ cubeSet q → ∀ v ∈ verts q,
        |y 0 - (v.1 : ℝ)| ≤ 1 ∧ |y 1 - (v.2.1 : ℝ)| ≤ 1 ∧ |y 2 - (v.2.2 : ℝ)| ≤ 1 := by
      intro q y hy v hv
      obtain ⟨h0a, h0b, h1a, h1b, h2a, h2b⟩ := hy
      obtain ⟨hv0, hv1, hv2⟩ := mem_verts_iff.mp hv
      refine ⟨abs_le.mpr ?_, abs_le.mpr ?_, abs_le.mpr ?_⟩
      · rcases hv0 with h0 | h0 <;> rw [h0] <;> push_cast <;> constructor <;> linarith
      · rcases hv1 with h1 | h1 <;> rw [h1] <;> push_cast <;> constructor <;> linarith
      · rcases hv2 with h2 | h2 <;> rw [h2] <;> push_cast <;> constructor <;> linarith
    have hev_unit : ∀ q ∈ A, ∀ v ∈ verts q, dot3 (ev v) (ev v) = 1 := by
      intro q hq v hv
      have hex : ∃ q' ∈ A, v ∈ verts q' := ⟨q, hq, hv⟩
      dsimp only [ev]; rw [dif_pos hex]
      exact hxk_unit _
    have hev_near : ∀ q ∈ A, ∀ v ∈ verts q, (19 / 20 : ℝ) ^ 2 < (dot3 (ev v) (xq q)) ^ 2 := by
      intro q hq v hv
      have hex : ∃ q' ∈ A, v ∈ verts q' := ⟨q, hq, hv⟩
      obtain ⟨hq', hv'⟩ := hex.choose_spec
      have hev_eq : ev v = xk (kq hex.choose) := by dsimp only [ev, xq]; rw [dif_pos hex]
      rw [hev_eq]
      apply dot3_sq_bound (hxk_unit _) (hxk_unit _)
      intro i j
      rw [← hxk_P, ← hxk_P]
      apply hP_close_of_phi
      have d1v := hphi_vert hex.choose (φ (kq hex.choose)) (hkq_in _ hq') v hv'
      have d2v := hphi_vert q (φ (kq q)) (hkq_in _ hq) v hv
      intro r
      fin_cases r
      · change |φ (kq hex.choose) 0 - φ (kq q) 0| ≤ 2
        have a := abs_le.mp d1v.1; have b := abs_le.mp d2v.1
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · change |φ (kq hex.choose) 1 - φ (kq q) 1| ≤ 2
        have a := abs_le.mp d1v.2.1; have b := abs_le.mp d2v.2.1
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · change |φ (kq hex.choose) 2 - φ (kq q) 2| ≤ 2
        have a := abs_le.mp d1v.2.2; have b := abs_le.mp d2v.2.2
        exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hxk_near : ∀ q ∈ A, ∀ k : K, φ k ∈ cubeSet q → (19 / 20 : ℝ) ^ 2 < (dot3 (xk k) (xq q)) ^ 2 := by
      intro q hq k hk
      apply dot3_sq_bound (hxk_unit _) (hxk_unit _)
      intro i j
      rw [← hxk_P, ← hxk_P]
      apply hP_close_of_phi
      obtain ⟨a0, b0, a1, b1, a2, b2⟩ := hk
      obtain ⟨c0, d0, c1, d1', c2, d2'⟩ := hkq_in q hq
      intro r
      fin_cases r
      · change |φ k 0 - φ (kq q) 0| ≤ 2; exact abs_le.mpr ⟨by linarith, by linarith⟩
      · change |φ k 1 - φ (kq q) 1| ≤ 2; exact abs_le.mpr ⟨by linarith, by linarith⟩
      · change |φ k 2 - φ (kq q) 2| ≤ 2; exact abs_le.mpr ⟨by linarith, by linarith⟩
    let b0 : Cochain1 :=
      (fun i j k => bitOf (dot3 (ev (i, j, k)) (ev (i + 1, j, k))),
       fun i j k => bitOf (dot3 (ev (i, j, k)) (ev (i, j + 1, k))),
       fun i j k => bitOf (dot3 (ev (i, j, k)) (ev (i, j, k + 1))))
    have heven_xy : ∀ i j k, ActXY A i j k → 2 ∣ (d1 b0).1 i j k := by
      intro i j k hact
      obtain ⟨q, hq, hv00, hv10, hv11, hv01⟩ : ∃ q ∈ A,
          (i, j, k) ∈ verts q ∧ (i + 1, j, k) ∈ verts q ∧
          (i + 1, j + 1, k) ∈ verts q ∧ (i, j + 1, k) ∈ verts q := by
        rcases hact with h | ⟨hk0, h⟩
        · exact ⟨(i, j, k), h,
            mem_verts_iff.mpr ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩,
            mem_verts_iff.mpr ⟨Or.inr rfl, Or.inl rfl, Or.inl rfl⟩,
            mem_verts_iff.mpr ⟨Or.inr rfl, Or.inr rfl, Or.inl rfl⟩,
            mem_verts_iff.mpr ⟨Or.inl rfl, Or.inr rfl, Or.inl rfl⟩⟩
        · exact ⟨(i, j, k - 1), h,
            mem_verts_iff.mpr ⟨Or.inl rfl, Or.inl rfl, Or.inr (by dsimp; omega)⟩,
            mem_verts_iff.mpr ⟨Or.inr rfl, Or.inl rfl, Or.inr (by dsimp; omega)⟩,
            mem_verts_iff.mpr ⟨Or.inr rfl, Or.inr rfl, Or.inr (by dsimp; omega)⟩,
            mem_verts_iff.mpr ⟨Or.inl rfl, Or.inr rfl, Or.inr (by dsimp; omega)⟩⟩
      obtain ⟨⟨m1, hm1⟩, -⟩ := bitOf_edge_rel (hev_unit q hq _ hv00) (hev_unit q hq _ hv10)
        (hxk_unit _) (hev_near q hq _ hv00) (hev_near q hq _ hv10)
      obtain ⟨⟨m2, hm2⟩, -⟩ := bitOf_edge_rel (hev_unit q hq _ hv10) (hev_unit q hq _ hv11)
        (hxk_unit _) (hev_near q hq _ hv10) (hev_near q hq _ hv11)
      obtain ⟨⟨m3, hm3⟩, -⟩ := bitOf_edge_rel (hev_unit q hq _ hv01) (hev_unit q hq _ hv11)
        (hxk_unit _) (hev_near q hq _ hv01) (hev_near q hq _ hv11)
      obtain ⟨⟨m4, hm4⟩, -⟩ := bitOf_edge_rel (hev_unit q hq _ hv00) (hev_unit q hq _ hv01)
        (hxk_unit _) (hev_near q hq _ hv00) (hev_near q hq _ hv01)
      refine ⟨m1 + m2 - m3 - m4, ?_⟩
      simp only [d1, b0]
      linarith
    have heven_xz : ∀ i j k, ActXZ A i j k → 2 ∣ (d1 b0).2.1 i j k := by
      intro i j k hact
      obtain ⟨q, hq, hv00, hv10, hv11, hv01⟩ : ∃ q ∈ A,
          (i, j, k) ∈ verts q ∧ (i + 1, j, k) ∈ verts q ∧
          (i + 1, j, k + 1) ∈ verts q ∧ (i, j, k + 1) ∈ verts q := by
        rcases hact with h | ⟨hj0, h⟩
        · exact ⟨(i, j, k), h,
            mem_verts_iff.mpr ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩,
            mem_verts_iff.mpr ⟨Or.inr rfl, Or.inl rfl, Or.inl rfl⟩,
            mem_verts_iff.mpr ⟨Or.inr rfl, Or.inl rfl, Or.inr rfl⟩,
            mem_verts_iff.mpr ⟨Or.inl rfl, Or.inl rfl, Or.inr rfl⟩⟩
        · exact ⟨(i, j - 1, k), h,
            mem_verts_iff.mpr ⟨Or.inl rfl, Or.inr (by dsimp; omega), Or.inl rfl⟩,
            mem_verts_iff.mpr ⟨Or.inr rfl, Or.inr (by dsimp; omega), Or.inl rfl⟩,
            mem_verts_iff.mpr ⟨Or.inr rfl, Or.inr (by dsimp; omega), Or.inr rfl⟩,
            mem_verts_iff.mpr ⟨Or.inl rfl, Or.inr (by dsimp; omega), Or.inr rfl⟩⟩
      obtain ⟨⟨m1, hm1⟩, -⟩ := bitOf_edge_rel (hev_unit q hq _ hv00) (hev_unit q hq _ hv10)
        (hxk_unit _) (hev_near q hq _ hv00) (hev_near q hq _ hv10)
      obtain ⟨⟨m2, hm2⟩, -⟩ := bitOf_edge_rel (hev_unit q hq _ hv10) (hev_unit q hq _ hv11)
        (hxk_unit _) (hev_near q hq _ hv10) (hev_near q hq _ hv11)
      obtain ⟨⟨m3, hm3⟩, -⟩ := bitOf_edge_rel (hev_unit q hq _ hv01) (hev_unit q hq _ hv11)
        (hxk_unit _) (hev_near q hq _ hv01) (hev_near q hq _ hv11)
      obtain ⟨⟨m4, hm4⟩, -⟩ := bitOf_edge_rel (hev_unit q hq _ hv00) (hev_unit q hq _ hv01)
        (hxk_unit _) (hev_near q hq _ hv00) (hev_near q hq _ hv01)
      refine ⟨m1 + m2 - m3 - m4, ?_⟩
      simp only [d1, b0]
      linarith
    have heven_yz : ∀ i j k, ActYZ A i j k → 2 ∣ (d1 b0).2.2 i j k := by
      intro i j k hact
      obtain ⟨q, hq, hv00, hv10, hv11, hv01⟩ : ∃ q ∈ A,
          (i, j, k) ∈ verts q ∧ (i, j + 1, k) ∈ verts q ∧
          (i, j + 1, k + 1) ∈ verts q ∧ (i, j, k + 1) ∈ verts q := by
        rcases hact with h | ⟨hi0, h⟩
        · exact ⟨(i, j, k), h,
            mem_verts_iff.mpr ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩,
            mem_verts_iff.mpr ⟨Or.inl rfl, Or.inr rfl, Or.inl rfl⟩,
            mem_verts_iff.mpr ⟨Or.inl rfl, Or.inr rfl, Or.inr rfl⟩,
            mem_verts_iff.mpr ⟨Or.inl rfl, Or.inl rfl, Or.inr rfl⟩⟩
        · exact ⟨(i - 1, j, k), h,
            mem_verts_iff.mpr ⟨Or.inr (by dsimp; omega), Or.inl rfl, Or.inl rfl⟩,
            mem_verts_iff.mpr ⟨Or.inr (by dsimp; omega), Or.inr rfl, Or.inl rfl⟩,
            mem_verts_iff.mpr ⟨Or.inr (by dsimp; omega), Or.inr rfl, Or.inr rfl⟩,
            mem_verts_iff.mpr ⟨Or.inr (by dsimp; omega), Or.inl rfl, Or.inr rfl⟩⟩
      obtain ⟨⟨m1, hm1⟩, -⟩ := bitOf_edge_rel (hev_unit q hq _ hv00) (hev_unit q hq _ hv10)
        (hxk_unit _) (hev_near q hq _ hv00) (hev_near q hq _ hv10)
      obtain ⟨⟨m2, hm2⟩, -⟩ := bitOf_edge_rel (hev_unit q hq _ hv10) (hev_unit q hq _ hv11)
        (hxk_unit _) (hev_near q hq _ hv10) (hev_near q hq _ hv11)
      obtain ⟨⟨m3, hm3⟩, -⟩ := bitOf_edge_rel (hev_unit q hq _ hv01) (hev_unit q hq _ hv11)
        (hxk_unit _) (hev_near q hq _ hv01) (hev_near q hq _ hv11)
      obtain ⟨⟨m4, hm4⟩, -⟩ := bitOf_edge_rel (hev_unit q hq _ hv00) (hev_unit q hq _ hv01)
        (hxk_unit _) (hev_near q hq _ hv00) (hev_near q hq _ hv01)
      refine ⟨m1 + m2 - m3 - m4, ?_⟩
      simp only [d1, b0]
      linarith
    obtain ⟨a, hxy0, hxz0, hyz0⟩ := lift_mod2_cocycle hM4 hA_bounds b0 heven_xy heven_xz heven_yz
    let b := subC1 b0 (scaleC1 2 a)
    let F : ℕ × ℕ × ℕ → Set K := fun q => { k : K | φ k ∈ cubeSet q }
    have hF_closed : ∀ q ∈ A, IsClosed (F q) := by
      intro q _
      have c0 : Continuous (fun k : K => φ k 0) := (continuous_apply (0 : Fin 3)).comp hφ_cont
      have c1 : Continuous (fun k : K => φ k 1) := (continuous_apply (1 : Fin 3)).comp hφ_cont
      have c2 : Continuous (fun k : K => φ k 2) := (continuous_apply (2 : Fin 3)).comp hφ_cont
      have hFeq : F q = (({k : K | (q.1 : ℝ) ≤ φ k 0} ∩ {k : K | φ k 0 ≤ (q.1 : ℝ) + 1}) ∩
          ({k : K | (q.2.1 : ℝ) ≤ φ k 1} ∩ {k : K | φ k 1 ≤ (q.2.1 : ℝ) + 1})) ∩
          ({k : K | (q.2.2 : ℝ) ≤ φ k 2} ∩ {k : K | φ k 2 ≤ (q.2.2 : ℝ) + 1}) := by
        ext k; simp only [F, cubeSet, Set.mem_inter_iff]
        exact ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩,
               fun ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩ => ⟨a, b, c, d, e, f⟩⟩
      rw [hFeq]
      exact (((isClosed_le continuous_const c0).inter (isClosed_le c0 continuous_const)).inter
             ((isClosed_le continuous_const c1).inter (isClosed_le c1 continuous_const))).inter
            ((isClosed_le continuous_const c2).inter (isClosed_le c2 continuous_const))
    obtain ⟨uK, huK_cont, huK_eq⟩ := paste_closed_finset (0 : Fin 3 → ℂ) A F
      (fun q k => uq b ev q (φ k)) hF_closed
      (fun q _ => (continuous_uq b ev q).comp hφ_cont) hcover
      (fun q hq q' hq' k hkq hkq' => (uq_eq_on_inter hxy0 hxz0 hyz0 ev hq' hq hkq' hkq))
    let s : K → Fin 3 → ℂ := fun k i => ∑ j : Fin 3, (P k i j : ℂ) * uK k j
    have hs_cont : Continuous s := by
      refine continuous_pi fun i => continuous_finsetSum _ fun j _ => ?_
      have cP : Continuous (fun k : K => (P k i j : ℂ)) :=
        Complex.continuous_ofReal.comp ((continuous_apply j).comp ((continuous_apply i).comp hP))
      exact cP.mul ((continuous_apply j).comp huK_cont)
    refine ⟨s, hs_cont, fun k => ⟨?_, fun i => ?_⟩⟩
    · intro hs0
      obtain ⟨q, hqA, hkq⟩ := hcover k
      have huK_k : uK k = uq b ev q (φ k) := huK_eq q hqA k hkq
      have hpair_zero : ∑ i : Fin 3, (xk k i : ℂ) * s k i = 0 := by
        rw [hs0]; simp
      have hpair_eq : ∑ i : Fin 3, (xk k i : ℂ) * s k i =
          Complex.exp (↑(Real.pi * ∑ v ∈ verts q, tent (φ k) v * (mq b q v : ℝ)) * Complex.I) *
            ↑(∑ v ∈ verts q, tent (φ k) v * ((-1 : ℝ) ^ mq b q v * dot3 (ev v) (xk k))) := by
        have hunit := hxk_unit k
        have h1 : ∀ i : Fin 3, s k i = (xk k i : ℂ) * ∑ j : Fin 3, (xk k j : ℂ) * uK k j := by
          intro i
          simp only [s, hxk_P k, Fin.sum_univ_three]
          push_cast; ring
        have h2 : ∑ i : Fin 3, (xk k i : ℂ) * s k i = ∑ j : Fin 3, (xk k j : ℂ) * uK k j := by
          simp only [h1, Fin.sum_univ_three]
          have hunitR : xk k 0 ^ 2 + xk k 1 ^ 2 + xk k 2 ^ 2 = 1 := by
            unfold dot3 at hunit; linarith
          have hunitC : ((xk k 0 : ℂ) ^ 2 + (xk k 1 : ℂ) ^ 2 + (xk k 2 : ℂ) ^ 2) = 1 := by
            exact_mod_cast hunitR
          calc _ = ((xk k 0 : ℂ) ^ 2 + (xk k 1 : ℂ) ^ 2 + (xk k 2 : ℂ) ^ 2) *
                   ((xk k 0 : ℂ) * uK k 0 + (xk k 1 : ℂ) * uK k 1 + (xk k 2 : ℂ) * uK k 2) := by ring
               _ = _ := by rw [hunitC, one_mul]
        rw [h2, huK_k]
        simp only [uq, Fin.sum_univ_three, dot3]
        push_cast
        simp only [mul_sum]
        rw [← sum_add_distrib, ← sum_add_distrib]
        refine sum_congr rfl fun v _ => by ring
      rw [hpair_eq] at hpair_zero
      rcases mul_eq_zero.mp hpair_zero with hexp0 | hreal0
      · exact Complex.exp_ne_zero _ hexp0
      · have hr0 : ∑ v ∈ verts q, tent (φ k) v * ((-1 : ℝ) ^ mq b q v * dot3 (ev v) (xk k)) = 0 :=
          Complex.ofReal_eq_zero.mp hreal0
        let sq0 := sgnOf (dot3 (ev q) (xq q))
        let sk0 := sgnOf (dot3 (xk k) (xq q))
        have hmul0 : sq0 * sk0 *
            (∑ v ∈ verts q, tent (φ k) v * ((-1 : ℝ) ^ mq b q v * dot3 (ev v) (xk k))) = 0 := by
          rw [hr0, mul_zero]
        have hpos_sum : 4 / 5 ≤ sq0 * sk0 *
            (∑ v ∈ verts q, tent (φ k) v * ((-1 : ℝ) ^ mq b q v * dot3 (ev v) (xk k))) := by
          rw [mul_sum]
          have hterm : ∀ v ∈ verts q, tent (φ k) v * (4 / 5) ≤
              sq0 * sk0 * (tent (φ k) v * ((-1 : ℝ) ^ mq b q v * dot3 (ev v) (xk k))) := by
            intro v hv
            have hwalk := zpow_mq_walk hxy0 hxz0 hyz0 ev (xq q) hqA (hxk_unit _)
              (hev_unit q hqA) (hev_near q hqA)
              (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) hv
            rw [hwalk]
            have hsq0_2 : sq0 * sq0 = 1 := sgnOf_mul_self _
            have hrew : sq0 * sk0 * (tent (φ k) v * ((sq0 * sgnOf (dot3 (ev v) (xq q))) * dot3 (ev v) (xk k))) =
                tent (φ k) v * (sgnOf (dot3 (ev v) (xq q)) * sk0 * dot3 (ev v) (xk k)) := by
              calc _ = (sq0 * sq0) * (tent (φ k) v * (sgnOf (dot3 (ev v) (xq q)) * sk0 * dot3 (ev v) (xk k))) := by ring
                   _ = _ := by rw [hsq0_2, one_mul]
            rw [hrew]
            have hhd := same_hemi_dot (hev_unit q hqA v hv) (hxk_unit k) (hxk_unit _)
              (hev_near q hqA v hv) (hxk_near q hqA k hkq)
            exact mul_le_mul_of_nonneg_left hhd.le (tent_nonneg _ _)
          have hsum_le := sum_le_sum hterm
          rw [← sum_mul, sum_tent_verts hkq, one_mul] at hsum_le
          exact hsum_le
        linarith
    · simp only [s, hxk_P k, Fin.sum_univ_three]
      have hunitR : xk k 0 ^ 2 + xk k 1 ^ 2 + xk k 2 ^ 2 = 1 := by
        have hu := hxk_unit k; unfold dot3 at hu; linarith
      have hunitC : ((xk k 0 : ℂ) ^ 2 + (xk k 1 : ℂ) ^ 2 + (xk k 2 : ℂ) ^ 2) = 1 := by
        exact_mod_cast hunitR
      push_cast
      calc _ = ((xk k 0 : ℂ) ^ 2 + (xk k 1 : ℂ) ^ 2 + (xk k 2 : ℂ) ^ 2) *
               ((xk k i : ℂ) * uK k 0 * (xk k 0 : ℂ) +
                (xk k i : ℂ) * uK k 1 * (xk k 1 : ℂ) +
                (xk k i : ℂ) * uK k 2 * (xk k 2 : ℂ)) := by ring
           _ = _ := by rw [hunitC, one_mul]; ring
  · refine ⟨fun _ => 0, continuous_const, fun k => False.elim (hK_ne ⟨k.1, k.2⟩)⟩
