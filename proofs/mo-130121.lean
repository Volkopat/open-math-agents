import OMAStatements.S_mo_130121
import Mathlib

-- Problem: mo-130121, is the number of vertices of the unit n-cube in a ball of radius R
-- maximized by the centre (1/2, ..., 1/2, 0, ..., 0) with floor(4 R^2) coordinates 1/2?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Take n = 8 and R = 19/20, so floor(4 R^2) = floor(3.61) = 3. The centre
-- (1/2, 1/2, 1/2, 0, 0, 0, 0, 0) covers only the 8 vertices whose last five coordinates vanish
-- (a vertex with a 1 among them is at squared distance at least 1 > R^2). The centre
-- (1/8, ..., 1/8) covers the origin (squared distance 1/8) and the 8 unit vectors (squared
-- distance 49/64 + 7/64 = 7/8 <= 361/400), that is 9 vertices.

namespace MO130121

open OMA.S_mo_130121

noncomputable def c : Fin 8 → ℝ := fun _ => 1 / 8

noncomputable def R : ℝ := 19 / 20

def g : Option (Fin 8) → (Fin 8 → Bool)
  | none => fun _ => false
  | some i => fun j => decide (j = i)

theorem floor_eq : ⌊4 * R ^ 2⌋₊ = 3 := by
  have h0 : (0 : ℝ) ≤ 4 * R ^ 2 := by positivity
  rw [Nat.floor_eq_iff h0]
  constructor <;> norm_num [R]

theorem far (v : Fin 8 → Bool) (hv : sqDist v (halfCenter 8 3) ≤ R ^ 2) (i : Fin 8)
    (hi : 3 ≤ i.val) : v i = false := by
  by_contra hne
  have hvi : v i = true := by simpa using hne
  have hle : ((if v i then (1 : ℝ) else 0) - halfCenter 8 3 i) ^ 2 ≤
      sqDist v (halfCenter 8 3) := by
    unfold sqDist
    exact Finset.single_le_sum
      (f := fun j => ((if v j then (1 : ℝ) else 0) - halfCenter 8 3 j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hc : halfCenter 8 3 i = 0 := by
    unfold halfCenter
    rw [if_neg (by omega)]
  rw [hvi, hc] at hle
  have h1 : (1 : ℝ) ≤ sqDist v (halfCenter 8 3) := by
    have h2 : ((if true = true then (1 : ℝ) else 0) - 0) ^ 2 = 1 := by norm_num
    rw [h2] at hle
    exact hle
  have h3 : R ^ 2 < 1 := by norm_num [R]
  linarith

theorem upper : covered 8 (halfCenter 8 3) R ≤ 8 := by
  unfold covered
  have hcard : (Finset.univ.filter
      (fun v : Fin 8 → Bool => sqDist v (halfCenter 8 3) ≤ R ^ 2)).card ≤
      (Finset.univ : Finset (Fin 3 → Bool)).card := by
    apply Finset.card_le_card_of_injOn
      (fun v => fun k : Fin 3 => v (Fin.castLE (by norm_num) k))
    · intro v _
      simp
    · intro v hv w hw hvw
      have hv' : v ∈ Finset.univ.filter
          (fun v : Fin 8 → Bool => sqDist v (halfCenter 8 3) ≤ R ^ 2) := hv
      have hw' : w ∈ Finset.univ.filter
          (fun v : Fin 8 → Bool => sqDist v (halfCenter 8 3) ≤ R ^ 2) := hw
      rw [Finset.mem_filter] at hv' hw'
      funext i
      by_cases hi : i.val < 3
      · have h := congrFun hvw ⟨i.val, hi⟩
        exact h
      · rw [far v hv'.2 i (by omega), far w hw'.2 i (by omega)]
  have h8 : (Finset.univ : Finset (Fin 3 → Bool)).card = 8 := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    norm_num
  rw [h8] at hcard
  exact hcard

theorem sq_none : sqDist (g none) c = 1 / 8 := by
  unfold sqDist
  norm_num [g, c]

theorem sq_some (i : Fin 8) : sqDist (g (some i)) c = 7 / 8 := by
  have hterm : ∀ j : Fin 8, ((if g (some i) j then (1 : ℝ) else 0) - c j) ^ 2 =
      1 / 64 + (if j = i then 3 / 4 else 0) := by
    intro j
    by_cases h : j = i
    · norm_num [g, c, h]
    · norm_num [g, c, h]
  unfold sqDist
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem g_inj : Function.Injective g := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some j =>
      have h := congrFun hab j
      simp [g] at h
  | some i =>
    cases b with
    | none =>
      have h := congrFun hab i
      simp [g] at h
    | some j =>
      have h := congrFun hab i
      simp [g] at h
      rw [h]

theorem lower : 9 ≤ covered 8 c R := by
  unfold covered
  have hmem : ∀ o : Option (Fin 8),
      g o ∈ Finset.univ.filter (fun v : Fin 8 → Bool => sqDist v c ≤ R ^ 2) := by
    intro o
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    cases o with
    | none =>
      rw [sq_none]
      norm_num [R]
    | some i =>
      rw [sq_some]
      norm_num [R]
  have hcard : (Finset.univ : Finset (Option (Fin 8))).card ≤
      (Finset.univ.filter (fun v : Fin 8 → Bool => sqDist v c ≤ R ^ 2)).card :=
    Finset.card_le_card_of_injOn g (fun o _ => hmem o) g_inj.injOn
  have h9 : (Finset.univ : Finset (Option (Fin 8))).card = 9 := by
    rw [Finset.card_univ, Fintype.card_option, Fintype.card_fin]
  rw [h9] at hcard
  exact hcard

end MO130121

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_130121.main) := by
  intro h
  have h1 := h 8 MO130121.R (by norm_num [MO130121.R]) (by norm_num [MO130121.R]) MO130121.c
  rw [MO130121.floor_eq] at h1
  have h2 := MO130121.upper
  have h3 := MO130121.lower
  omega
