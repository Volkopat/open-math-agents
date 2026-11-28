import OMAStatements.S_mo_291073
import Mathlib

open Set

private theorem gridCover (N : ℕ) (hN : 2 ≤ N) :
    (Ioo 0 2 : Set ℝ) =
      ⋃ i : Fin (2 * N - 1), Metric.ball (((i : ℕ) + 1 : ℝ) / N) (1 / (N : ℝ)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  ext x
  simp only [mem_Ioo, mem_iUnion, Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor
  · intro hx
    let z := x * (N : ℝ)
    have hz0 : 0 < z := mul_pos hx.1 hn
    have hzN : z < 2 * (N : ℝ) := mul_lt_mul_of_pos_right hx.2 hn
    let j := max 1 ⌊z⌋₊
    have hj0 : 1 ≤ j := le_max_left _ _
    have hfloor : ⌊z⌋₊ < 2 * N := (Nat.floor_lt hz0.le).2 (by push_cast; exact hzN)
    have hjN : j < 2 * N := max_lt (by omega) hfloor
    have hcast : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
      rw [Nat.cast_sub hj0]
      push_cast
      ring
    refine ⟨⟨j - 1, by omega⟩, ?_⟩
    change -(1 / (N : ℝ)) < x - (((j - 1 : ℕ) : ℝ) + 1) / N ∧
      x - (((j - 1 : ℕ) : ℝ) + 1) / N < 1 / (N : ℝ)
    rw [hcast]
    have hlo : (j : ℝ) - 1 < z := by
      dsimp [j]
      rw [Nat.cast_max, Nat.cast_one]
      rcases le_total (1 : ℝ) (↑⌊z⌋₊ : ℝ) with h | h
      · rw [max_eq_right h]
        linarith [Nat.floor_le hz0.le]
      · rw [max_eq_left h]
        linarith
    have hhi : z < (j : ℝ) + 1 := by
      have hj : (⌊z⌋₊ : ℝ) ≤ (j : ℝ) := by exact_mod_cast le_max_right 1 ⌊z⌋₊
      linarith [Nat.lt_floor_add_one z]
    constructor <;> field_simp [hn.ne'] <;> dsimp [z] at hlo hhi <;> linarith
  · rintro ⟨i, h₁, h₂⟩
    have hi : ((i : ℕ) : ℝ) + 1 ≤ 2 * (N : ℝ) - 1 := by
      have h : (i : ℕ) + 2 ≤ 2 * N := by have := i.isLt; omega
      have h' : ((i : ℕ) : ℝ) + 2 ≤ 2 * (N : ℝ) := by exact_mod_cast h
      linarith
    have hi0 : 0 ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    field_simp [hn.ne'] at h₁ h₂
    constructor
    · by_contra! hx
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hx hn.le]
    · by_contra! hx
      nlinarith [mul_le_mul_of_nonneg_right hx hn.le]

private theorem separated (N : ℕ) (hN : 2 ≤ N) :
    OMA.S_mo_291073.HasLayer (Ioo (0 : ℝ) 2) (Ioo 0 2 ∪ Ioo 4 6) (1 / (N : ℝ)) (1/2) := by
  classical
  let I := Fin (2 * N - 1) × Fin 2
  let x : I → ℝ := fun i => ((i.1 : ℕ) + 1 : ℝ) / N
  let d : Fin 2 → ℝ := fun j => if j = 0 then 0 else 4
  let y : I → ℝ := fun i => x i + d i.2
  have grid := gridCover N hN
  refine ⟨I, inferInstance, x, y, {0, 4}, ∅, ?_, ?_, ?_, ?_⟩
  · rw [grid]
    ext t
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨(i, 0), hi⟩
    · rintro ⟨⟨i, j⟩, hi⟩
      exact ⟨i, hi⟩
  · have gridAt (t : ℝ) :
        t ∈ (Ioo (0 : ℝ) 2) ↔
          ∃ i : Fin (2 * N - 1), t ∈ Metric.ball (((i : ℕ) + 1 : ℝ) / N) (1 / (N : ℝ)) := by
      rw [grid, mem_iUnion]
    have ballShift (t c a : ℝ) :
        t ∈ Metric.ball (c + a) (1 / (N : ℝ)) ↔
        t - a ∈ Metric.ball c (1 / (N : ℝ)) := by
      simp only [Metric.mem_ball, Real.dist_eq]
      rw [show t - (c + a) = (t - a) - c by ring]
    ext t
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro (ht | ht)
      · obtain ⟨i, hi⟩ := (gridAt t).mp ht
        exact ⟨(i, 0), by simpa [y, d, x] using hi⟩
      · have hs : t - 4 ∈ Ioo (0 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
        obtain ⟨i, hi⟩ := (gridAt (t - 4)).mp hs
        refine ⟨(i, 1), ?_⟩
        simpa [y, d, x] using (ballShift t _ 4).mpr hi
    · rintro ⟨⟨i, j⟩, hj⟩
      fin_cases j
      · exact Or.inl ((gridAt t).mpr ⟨i, by simpa [y, d, x] using hj⟩)
      · have hb : t - 4 ∈ Ioo (0 : ℝ) 2 :=
          (gridAt (t - 4)).mpr ⟨i, (ballShift t _ 4).mp (by simpa [y, d, x] using hj)⟩
        exact Or.inr ⟨by linarith [hb.1], by linarith [hb.2]⟩
  · rintro ⟨i, j⟩
    exact Or.inl ⟨d j, by by_cases h : j = 0 <;> simp [d, h], rfl⟩
  · have hc : 4 < Fintype.card I := by
      simp only [I, Fintype.card_prod, Fintype.card_fin]
      omega
    simp only [Finset.card_empty, max_eq_left (Nat.zero_le _), Finset.card_insert_of_notMem (by simp : (0 : ℝ) ∉ ({4} : Finset ℝ)),
      Finset.card_singleton]
    change (2 : ℝ) < (Fintype.card I : ℝ) ^ (1/2 : ℝ)
    rw [← Real.sqrt_eq_rpow]
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    exact_mod_cast hc

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_291073.main) := by
  intro h
  let δ : ℕ → ℝ := fun m => 1 / ((m + 2 : ℕ) : ℝ)
  have hδ : StrictAnti δ := by
    intro i j hij
    exact one_div_lt_one_div_of_lt (by positivity) (by exact_mod_cast (show i + 2 < j + 2 by omega))
  have hpos (m : ℕ) : 0 < δ m := by dsimp [δ]; positivity
  let A : Set ℝ := Ioo 0 2
  let B : Set ℝ := A ∪ Ioo 4 6
  have ha : Convex ℝ A := convex_Ioo 0 2
  have p : (1 : ℝ) ∈ B := Or.inl (by norm_num [A])
  have q : (5 : ℝ) ∈ B := Or.inr (by norm_num)
  have r : (3 : ℝ) ∉ B := by norm_num [A, B]
  rcases h ℝ A B δ hδ hpos ⟨1/2, by norm_num, by norm_num, fun m => separated (m+2) (by omega)⟩ with ⟨d, hd⟩ | ⟨s, hs⟩
  · rw [hd] at p q
    obtain ⟨u, hu, he⟩ := p
    obtain ⟨v, hv, hf⟩ := q
    apply r
    rw [hd]
    refine ⟨(1/2 : ℝ) • u + (1/2 : ℝ) • v, ha hu hv (by norm_num) (by norm_num) (by norm_num), ?_⟩
    simp only [smul_eq_mul]
    linarith
  · rw [hs] at p q
    obtain ⟨u, hu, he⟩ := p
    obtain ⟨v, hv, hf⟩ := q
    apply r
    rw [hs]
    refine ⟨(1/2 : ℝ) • u + (1/2 : ℝ) • v, ha hu hv (by norm_num) (by norm_num) (by norm_num), ?_⟩
    change s * u = 1 at he
    change s * v = 5 at hf
    change s * (1/2 * u + 1/2 * v) = 3
    calc
      _ = (s * u) / 2 + (s * v) / 2 := by ring
      _ = 3 := by rw [he, hf]; norm_num