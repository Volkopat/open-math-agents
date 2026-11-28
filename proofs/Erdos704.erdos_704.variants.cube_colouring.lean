import FormalConjectures.ErdosProblems.«704»

/-! A pair of points at unit distance has a scaled coordinate gap of at least one. -/

open Erdos704 SimpleGraph

/-- Floors in the same residue class must agree if the inputs are close enough. -/
private lemma floor_eq_of_close {m : ℕ} {u v : ℝ} (h : |u - v| + 1 ≤ (m : ℝ))
    (hc : (⌊u⌋ : ZMod m) = (⌊v⌋ : ZMod m)) : ⌊u⌋ = ⌊v⌋ := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ m).mp hc
  have hr : |(⌊v⌋ : ℝ) - (⌊u⌋ : ℝ)| < (m : ℝ) := by
    apply abs_lt.mpr
    constructor <;>
      linarith [Int.floor_le u, Int.floor_le v, Int.lt_floor_add_one u,
        Int.lt_floor_add_one v, le_abs_self (u - v), neg_le_abs (u - v)]
  have hz : (⌊v⌋ - ⌊u⌋).natAbs < m := by
    exact_mod_cast (show ((⌊v⌋ - ⌊u⌋).natAbs : ℝ) < (m : ℝ) by
      simpa only [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub] using hr)
  exact (sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using hz))).symm

theorem OMA.solution : type_of% @Erdos704.erdos_704.variants.cube_colouring := by
  intro n
  let s := Real.sqrt (n : ℝ)
  let m := ⌈s⌉₊ + 1
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hmlo : s + 1 ≤ (m : ℝ) := by simpa [m] using add_le_add_left (Nat.le_ceil s) 1
  have hmhi : (m : ℝ) ≤ 2 + s := by
    simp only [m, Nat.cast_add, Nat.cast_one]
    linarith [Nat.ceil_lt_add_one hs]
  let : NeZero m := ⟨by simp [m]⟩
  let c (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) : ZMod m := ⌊s * x i⌋
  have coloring : (unitDistanceGraph n).Coloring (Fin n → ZMod m) := by
    apply Coloring.mk c
    intro x y hxy hc
    change dist x y = 1 at hxy
    have hdist : ∑ i, (x i - y i) ^ 2 = 1 := by
      simpa [hxy, Real.dist_eq, sq_abs] using (EuclideanSpace.dist_sq_eq x y).symm
    have hn : 0 < n := by
      by_contra! h
      obtain rfl : n = 0 := by omega
      simp at hdist
    let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hsum : ∑ i : Fin n, (1 : ℝ) ≤ ∑ i, (s * (x i - y i)) ^ 2 := by
      simp [mul_pow, ← Finset.mul_sum, hdist, s, Real.sq_sqrt (Nat.cast_nonneg n)]
    obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
    have hcoord : |x i - y i| ≤ 1 := by
      simpa [Real.dist_eq, hxy] using PiLp.dist_apply_le x y i
    have hclose : |s * x i - s * y i| + 1 ≤ (m : ℝ) := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hs]
      exact (add_le_add_left (mul_le_of_le_one_right hs hcoord) _).trans hmlo
    have hf : (⌊s * x i⌋ : ℝ) = ⌊s * y i⌋ := by
      exact_mod_cast floor_eq_of_close hclose (congrFun hc i)
    have hsmall : |s * x i - s * y i| < 1 := by
      apply abs_lt.mpr
      constructor <;> linarith [Int.floor_le (s * x i), Int.floor_le (s * y i),
        Int.lt_floor_add_one (s * x i), Int.lt_floor_add_one (s * y i)]
    rw [mul_sub] at hi
    apply (not_lt_of_ge hi)
    simpa only [one_pow] using sq_lt_sq.mpr (by simpa only [abs_one] using hsmall :
      |s * x i - s * y i| < |(1 : ℝ)|)
  refine ⟨Fintype.card (Fin n → ZMod m), coloring.colorable, ?_⟩
  simpa [Fintype.card_fun, ZMod.card] using pow_le_pow_left₀ (Nat.cast_nonneg m) hmhi n
