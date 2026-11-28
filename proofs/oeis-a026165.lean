import OMAStatements.S_oeis_a026165
import Mathlib

-- Credit: @hermitokatt (Lean proof with Claude Code)

/-!
Proof of R. J. Mathar's recurrence for A026165 (walks from 2 with first step ±1, free end).

1. Splitting a walk at its last step gives Pascal-like recursions for the number `x k L h y` of
   nonnegative walks of length `L` from `h` to `y` (the first `k` steps are ±1, later steps are
   in {-1, 0, 1}); after the first step the walks are Motzkin walks from `1` or `3`.
2. Trinomial coefficients `T L d` give the reflection principle `x 0 L h y = T(L, y-h) - T(L, y+h+2)`.
   Summing over the free end, `P(L+1) + x 0 L h 0 = 3 P(L)`, so
   `P(L, h) = T(L,0) + 2 T(L,1) + … + 2 T(L,h) + T(L,h+1)`, and
   `a(L+1) = 2 T(L,0) + 4 T(L,1) + 3 T(L,2) + 2 T(L,3) + T(L,4)`.
3. The row relation `(L+d+1) T(L,d+1) + d T(L,d) - (L-d+1) T(L,d-1) = 0` expresses all values
   through `T(m,0)` and `T(m,1)`; the recurrence, multiplied by a positive polynomial `D(m)`, is
   an explicit linear combination of these relations (checked by `linear_combination`).
   The case `n = 4` involves `a(0)` and is checked numerically.
-/

namespace OMA.A026165Proof

open OMA.S_oeis_a026165

/-- Walks on `N` positions from `h` to `y`, staying nonnegative; steps with index `≤ k` are
`±1`, later steps are in `{-1, 0, 1}`. -/
def X (k N h y : ℕ) : Set (Fin N → ℕ) :=
  {s | (∀ i : Fin N, i.val = 0 → s i = h) ∧
       (∀ i : Fin N, i.val = N - 1 → s i = y) ∧
       (∀ i j : Fin N, j.val = i.val + 1 → j.val ≤ k → |(s j : ℤ) - (s i : ℤ)| = 1) ∧
       (∀ i j : Fin N, j.val = i.val + 1 → k < j.val → |(s j : ℤ) - (s i : ℤ)| ≤ 1)}

/-- Extend a walk on `L+1` positions by a last value `y`. -/
def ext (L y : ℕ) (t : Fin (L + 1) → ℕ) : Fin (L + 2) → ℕ :=
  fun i => if h : i.val < L + 1 then t ⟨i.val, h⟩ else y

theorem ext_inj (L y : ℕ) : Function.Injective (ext L y) := by
  intro t t' h
  funext i
  have := congrFun h ⟨i.val, by omega⟩
  simpa [ext, i.isLt] using this

/-- Values grow by at most one per step. -/
theorem step_le (k N h y : ℕ) (s : Fin N → ℕ) (hs : s ∈ X k N h y) :
    ∀ v (hv : v < N), s ⟨v, hv⟩ ≤ h + v := by
  intro v
  induction v with
  | zero => intro hv; have := hs.1 ⟨0, hv⟩ rfl; omega
  | succ v ih =>
    intro hv
    have e := ih (by omega)
    have d : (s ⟨v + 1, hv⟩ : ℤ) - s ⟨v, by omega⟩ ≤ 1 := by
      by_cases hk : v + 1 ≤ k
      · exact (le_abs_self _).trans (hs.2.2.1 ⟨v, by omega⟩ ⟨v + 1, hv⟩ rfl hk).le
      · exact (le_abs_self _).trans
          (hs.2.2.2 ⟨v, by omega⟩ ⟨v + 1, hv⟩ rfl (show k < v + 1 by omega))
    omega

theorem step_le' (k N h y : ℕ) (s : Fin N → ℕ) (hs : s ∈ X k N h y) (i : Fin N) :
    s i ≤ h + i.val := by
  have := step_le k N h y s hs i.val i.isLt
  simpa using this

theorem X_finite (k N h y : ℕ) : (X k N h y).Finite := by
  apply (Set.Finite.pi (t := fun _ : Fin N => Set.Iic (h + N)) (fun _ => Set.finite_Iic _)).subset
  intro s hs
  simp only [Set.mem_univ_pi, Set.mem_Iic]
  intro i
  have := step_le' k N h y s hs i
  have hi := i.isLt
  omega

theorem X_top (k L h y : ℕ) (hy : h + L < y) : X k (L + 1) h y = ∅ := by
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hs
  have e1 : s ⟨L, by omega⟩ ≤ h + L := step_le k (L + 1) h y s hs L (by omega)
  rw [hs.2.1 ⟨L, by omega⟩ (by simp)] at e1
  omega

theorem X_one (k h y : ℕ) : (X k 1 h y).ncard = if y = h then 1 else 0 := by
  split_ifs with hy
  · have : X k 1 h y = {fun _ => h} := by
      ext s
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hs; funext i; exact hs.1 i (by have := i.isLt; omega)
      · rintro rfl
        exact ⟨fun _ _ => rfl, fun _ _ => hy.symm,
          fun i j hij _ => absurd hij (by have := j.isLt; omega),
          fun i j hij _ => absurd hij (by have := j.isLt; omega)⟩
    rw [this, Set.ncard_singleton]
  · have : X k 1 h y = ∅ := by
      ext s
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hs
      exact hy ((hs.2.1 0 (by simp)).symm.trans (hs.1 0 rfl))
    rw [this, Set.ncard_empty]

theorem mem_X_succ (k L h y : ℕ) (hk : k < L + 1) (s : Fin (L + 2) → ℕ) :
    s ∈ X k (L + 2) h y ↔ ∃ z t, t ∈ X k (L + 1) h z ∧ |(y : ℤ) - z| ≤ 1 ∧ ext L y t = s := by
  constructor
  · rintro ⟨h0, hN, h1, h2⟩
    refine ⟨s ⟨L, by omega⟩, fun i => s ⟨i.val, by omega⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro i hi; exact h0 _ hi
    · intro i hi; exact congrArg s (Fin.ext (by simp at hi ⊢; omega))
    · intro i j hij hj; exact h1 _ _ hij hj
    · intro i j hij hj; exact h2 _ _ hij hj
    · have e := h2 ⟨L, by omega⟩ ⟨L + 1, by omega⟩ rfl hk
      rw [hN ⟨L + 1, by omega⟩ (by simp)] at e
      exact e
    · funext i
      by_cases hi : i.val < L + 1
      · simp [ext, hi]
      · simp only [ext, hi, dite_false]
        exact (hN i (by omega)).symm
  · rintro ⟨z, t, ⟨h0, hN, h1, h2⟩, hz, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      simp only [ext, show i.val < L + 1 by omega, dite_true]
      exact h0 _ hi
    · intro i hi
      simp only [ext, show ¬ i.val < L + 1 by omega, dite_false]
    · intro i j hij hj
      simp only [ext, show j.val < L + 1 by omega, show i.val < L + 1 by omega, dite_true]
      exact h1 ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij hj
    · intro i j hij hj
      by_cases hjl : j.val < L + 1
      · simp only [ext, hjl, show i.val < L + 1 by omega, dite_true]
        exact h2 ⟨i.val, by omega⟩ ⟨j.val, hjl⟩ hij hj
      · simp only [ext, hjl, show i.val < L + 1 by omega, dite_true, dite_false]
        rw [hN ⟨i.val, by omega⟩ (by simp; omega)]
        exact hz

theorem X_zero (k L h : ℕ) (hk : k < L + 1) :
    X k (L + 2) h 0 = ext L 0 '' X k (L + 1) h 0 ∪ ext L 0 '' X k (L + 1) h 1 := by
  ext s
  rw [mem_X_succ k L h 0 hk]
  constructor
  · rintro ⟨z, t, ht, hz, rfl⟩
    have : z = 0 ∨ z = 1 := by rw [abs_le] at hz; omega
    rcases this with rfl | rfl
    · exact Or.inl ⟨t, ht, rfl⟩
    · exact Or.inr ⟨t, ht, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨0, t, ht, by rw [abs_le]; omega, rfl⟩
    · exact ⟨1, t, ht, by rw [abs_le]; omega, rfl⟩

theorem X_pos (k L h y : ℕ) (hk : k < L + 1) :
    X k (L + 2) h (y + 1) = ext L (y + 1) '' X k (L + 1) h y ∪
      ext L (y + 1) '' X k (L + 1) h (y + 1) ∪ ext L (y + 1) '' X k (L + 1) h (y + 2) := by
  ext s
  rw [mem_X_succ k L h (y + 1) hk]
  constructor
  · rintro ⟨z, t, ht, hz, rfl⟩
    have : z = y ∨ z = y + 1 ∨ z = y + 2 := by rw [abs_le] at hz; omega
    rcases this with rfl | rfl | rfl
    · exact Or.inl (Or.inl ⟨t, ht, rfl⟩)
    · exact Or.inl (Or.inr ⟨t, ht, rfl⟩)
    · exact Or.inr ⟨t, ht, rfl⟩
  · rintro ((⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩)
    · exact ⟨y, t, ht, by rw [abs_le]; omega, rfl⟩
    · exact ⟨y + 1, t, ht, by rw [abs_le]; omega, rfl⟩
    · exact ⟨y + 2, t, ht, by rw [abs_le]; omega, rfl⟩

theorem disj (k L h y z w : ℕ) (hzw : z ≠ w) :
    Disjoint (ext L y '' X k (L + 1) h z) (ext L y '' X k (L + 1) h w) := by
  rw [Set.disjoint_left]
  rintro s ⟨t, ht, rfl⟩ ⟨t', ht', e⟩
  have e1 := congrFun e ⟨L, by omega⟩
  simp only [ext, show L < L + 1 by omega, dite_true] at e1
  rw [ht.2.1 ⟨L, by omega⟩ (by simp), ht'.2.1 ⟨L, by omega⟩ (by simp)] at e1
  exact hzw e1.symm

/-- `x k L h y`: the number of walks of length `L` from `h` to `y`. -/
noncomputable def x (k L h y : ℕ) : ℕ := (X k (L + 1) h y).ncard

theorem x_len0 (k h y : ℕ) : x k 0 h y = if y = h then 1 else 0 := X_one k h y

theorem x_top (k L h y : ℕ) (hy : h + L < y) : x k L h y = 0 := by
  unfold x; rw [X_top k L h y hy, Set.ncard_empty]

theorem xr0 (k L h : ℕ) (hk : k < L + 1) : x k (L + 1) h 0 = x k L h 0 + x k L h 1 := by
  unfold x
  rw [X_zero k L h hk, Set.ncard_union_eq (disj k L h 0 0 1 (by omega))
    ((X_finite _ _ _ _).image _) ((X_finite _ _ _ _).image _),
    Set.ncard_image_of_injective _ (ext_inj _ _), Set.ncard_image_of_injective _ (ext_inj _ _)]

theorem xrp (k L h y : ℕ) (hk : k < L + 1) :
    x k (L + 1) h (y + 1) = x k L h y + x k L h (y + 1) + x k L h (y + 2) := by
  unfold x
  have fA := (X_finite k (L + 1) h y).image (ext L (y + 1))
  have fB := (X_finite k (L + 1) h (y + 1)).image (ext L (y + 1))
  have fC := (X_finite k (L + 1) h (y + 2)).image (ext L (y + 1))
  have dAB := disj k L h (y + 1) y (y + 1) (by omega)
  have dAC := disj k L h (y + 1) y (y + 2) (by omega)
  have dBC := disj k L h (y + 1) (y + 1) (y + 2) (by omega)
  rw [X_pos k L h y hk,
    Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨dAC, dBC⟩) (fA.union fB) fC,
    Set.ncard_union_eq dAB fA fB, Set.ncard_image_of_injective _ (ext_inj _ _),
    Set.ncard_image_of_injective _ (ext_inj _ _), Set.ncard_image_of_injective _ (ext_inj _ _)]

theorem X_two (h y : ℕ) :
    (X 1 2 h y).ncard = (if y + 1 = h then 1 else 0) + (if y = h + 1 then 1 else 0) := by
  by_cases hy : y + 1 = h ∨ y = h + 1
  · have : X 1 2 h y = {fun i : Fin 2 => if i.val = 0 then h else y} := by
      ext s
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hs
        funext i
        show s i = if i.val = 0 then h else y
        by_cases hi : i.val = 0
        · rw [if_pos hi]; exact hs.1 i hi
        · rw [if_neg hi]; exact hs.2.1 i (by have := i.isLt; omega)
      · rintro rfl
        refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
        · show (if i.val = 0 then h else y) = h
          rw [if_pos hi]
        · show (if i.val = 0 then h else y) = y
          rw [if_neg (show ¬ i.val = 0 by omega)]
        · intro i j hij hj
          have hi0 : i.val = 0 := by omega
          show |((if j.val = 0 then h else y : ℕ) : ℤ) - ((if i.val = 0 then h else y : ℕ) : ℤ)| = 1
          rw [if_pos hi0, if_neg (show ¬ j.val = 0 by omega), abs_eq zero_le_one]
          omega
        · intro i j hij hj
          exact absurd hj (by have := j.isLt; omega)
    rw [this, Set.ncard_singleton]
    split_ifs <;> omega
  · have : X 1 2 h y = ∅ := by
      ext s
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hs
      have e := hs.2.2.1 ⟨0, by omega⟩ ⟨1, by omega⟩ rfl le_rfl
      rw [hs.1 ⟨0, by omega⟩ rfl, hs.2.1 ⟨1, by omega⟩ rfl, abs_eq zero_le_one] at e
      omega
    rw [this, Set.ncard_empty]
    split_ifs <;> omega

/-- After a first step `±1` from `h + 1`, the walks are Motzkin walks from `h` or `h + 2`. -/
theorem G (h L : ℕ) : ∀ y, x 1 (L + 1) (h + 1) y = x 0 L h y + x 0 L (h + 2) y := by
  induction L with
  | zero =>
    intro y
    show (X 1 2 (h + 1) y).ncard = x 0 0 h y + x 0 0 (h + 2) y
    rw [X_two, x_len0, x_len0]
    split_ifs <;> omega
  | succ L ih =>
    intro y
    cases y with
    | zero =>
      rw [xr0 1 (L + 1) (h + 1) (by omega), ih 0, ih 1, xr0 0 L h (by omega),
        xr0 0 L (h + 2) (by omega)]
      ring
    | succ y =>
      rw [xrp 1 (L + 1) (h + 1) y (by omega), ih y, ih (y + 1), ih (y + 2), xrp 0 L h y (by omega),
        xrp 0 L (h + 2) y (by omega)]
      ring

/-- Trinomial coefficients: `T L d` is the coefficient of `x^d` in `(x⁻¹ + 1 + x)^L`. -/
def T : ℕ → ℤ → ℤ
  | 0, d => if d = 0 then 1 else 0
  | L + 1, d => T L (d - 1) + T L d + T L (d + 1)

theorem T_zero (d : ℤ) : T 0 d = if d = 0 then 1 else 0 := rfl

theorem T_succ (L : ℕ) (d : ℤ) : T (L + 1) d = T L (d - 1) + T L d + T L (d + 1) := rfl

theorem T_succ' (L : ℕ) (d a b : ℤ) (ha : a = d - 1) (hb : b = d + 1) :
    T (L + 1) d = T L a + T L d + T L b := by
  subst ha hb; exact T_succ L d

theorem T_symm (L : ℕ) : ∀ d, T L (-d) = T L d := by
  induction L with
  | zero => intro d; simp [T_zero]
  | succ L ih =>
    intro d
    rw [T_succ, T_succ, show -d - 1 = -(d + 1) by ring, show -d + 1 = -(d - 1) by ring, ih, ih, ih]
    ring

theorem T_symm' (L : ℕ) (d e : ℤ) (h : e = -d) : T L e = T L d := by rw [h, T_symm]

/-- The row relation `(L+d+1) T(L,d+1) + d T(L,d) - (L-d+1) T(L,d-1) = 0`. -/
theorem T_rel (L : ℕ) : ∀ d : ℤ,
    ((L : ℤ) + d + 1) * T L (d + 1) + d * T L d - ((L : ℤ) - d + 1) * T L (d - 1) = 0 := by
  induction L with
  | zero =>
    intro d
    simp only [T_zero]
    split_ifs <;> omega
  | succ L ih =>
    intro d
    have h1 := ih (d + 1)
    have h0 := ih d
    have hm := ih (d - 1)
    rw [T_succ' L (d + 1) d (d + 2) (by ring) (by ring), T_succ' L d (d - 1) (d + 1) rfl rfl,
      T_succ' L (d - 1) (d - 2) d (by ring) (by ring)]
    rw [show d + 1 + 1 = d + 2 by ring, show d + 1 - 1 = d by ring] at h1
    rw [show d - 1 + 1 = d by ring, show d - 1 - 1 = d - 2 by ring] at hm
    push_cast
    linear_combination h1 + h0 + hm

theorem T_rel' (L : ℕ) (d e f : ℤ) (he : e = d + 1) (hf : f = d - 1) :
    ((L : ℤ) + d + 1) * T L e + d * T L d - ((L : ℤ) - d + 1) * T L f = 0 := by
  subst he hf; exact T_rel L d

/-- The reflection principle for Motzkin walks: `x 0 L h y = T(L, y-h) - T(L, y+h+2)`. -/
theorem x0_closed (L : ℕ) : ∀ (h y : ℕ) (a b : ℤ), a = (y : ℤ) - h → b = (y : ℤ) + h + 2 →
    (x 0 L h y : ℤ) = T L a - T L b := by
  induction L with
  | zero =>
    intro h y a b ha hb
    rw [x_len0, T_zero, T_zero]
    split_ifs <;> omega
  | succ L ih =>
    intro h y a b ha hb
    cases y with
    | zero =>
      rw [xr0 0 L h (by omega), Nat.cast_add, ih h 0 a b (by omega) (by omega),
        ih h 1 (a + 1) (b + 1) (by omega) (by omega), T_succ L a, T_succ L b,
        T_symm' L (b - 1) (a - 1) (by omega)]
      ring
    | succ y =>
      rw [xrp 0 L h y (by omega), Nat.cast_add, Nat.cast_add,
        ih h y (a - 1) (b - 1) (by omega) (by omega), ih h (y + 1) a b ha hb,
        ih h (y + 2) (a + 1) (b + 1) (by omega) (by omega), T_succ L a, T_succ L b]
      ring

theorem TU (l : ℕ) : T (l + 1) 0 = T l 0 + 2 * T l 1 := by
  rw [T_succ' l 0 (-1) 1 (by norm_num) (by norm_num), T_symm' l 1 (-1) (by norm_num)]; ring

theorem TV (l : ℕ) : T (l + 1) 1 = T l 0 + T l 1 + T l 2 :=
  T_succ' l 1 0 2 (by norm_num) (by norm_num)

theorem T_relZ (l : ℕ) (L : ℤ) (hL : L = l) (c d e : ℤ) (hd : d = c + 1) (he : e = c - 1) :
    (L + c + 1) * T l d + c * T l c - (L - c + 1) * T l e = 0 := by
  subst hL; exact T_rel' l c d e hd he

theorem xr00 (L h : ℕ) : x 0 (L + 1) h 0 = x 0 L h 0 + x 0 L h 1 := xr0 0 L h (by omega)

theorem xrp0 (L h y : ℕ) :
    x 0 (L + 1) h (y + 1) = x 0 L h y + x 0 L h (y + 1) + x 0 L h (y + 2) :=
  xrp 0 L h y (by omega)

/-- Free end: every walk extends in three ways, except those ending at `0` (two ways). -/
theorem P_succN (L h : ℕ) (hh : h ≤ 4) :
    ∑ y ∈ Finset.range (L + 1 + 5), x 0 (L + 1) h y + x 0 L h 0 =
      3 * ∑ y ∈ Finset.range (L + 5), x 0 L h y := by
  rw [show L + 1 + 5 = L + 5 + 1 by omega, Finset.sum_range_succ']
  simp only [xrp0, xr00, Finset.sum_add_distrib]
  have e1 : ∑ y ∈ Finset.range (L + 6), x 0 L h y =
      ∑ y ∈ Finset.range (L + 5), x 0 L h (y + 1) + x 0 L h 0 := Finset.sum_range_succ' _ _
  have e2 : ∑ y ∈ Finset.range (L + 6), x 0 L h (y + 1) =
      ∑ y ∈ Finset.range (L + 5), x 0 L h (y + 2) + x 0 L h 1 := Finset.sum_range_succ' _ _
  have e3 : ∑ y ∈ Finset.range (L + 6), x 0 L h y =
      ∑ y ∈ Finset.range (L + 5), x 0 L h y + x 0 L h (L + 5) := Finset.sum_range_succ _ _
  have e4 : ∑ y ∈ Finset.range (L + 7), x 0 L h y =
      ∑ y ∈ Finset.range (L + 6), x 0 L h y + x 0 L h (L + 6) := Finset.sum_range_succ _ _
  have e5 : ∑ y ∈ Finset.range (L + 7), x 0 L h y =
      ∑ y ∈ Finset.range (L + 6), x 0 L h (y + 1) + x 0 L h 0 := Finset.sum_range_succ' _ _
  rw [x_top 0 L h (L + 5) (by omega)] at e3
  rw [x_top 0 L h (L + 6) (by omega)] at e4
  omega

/-- The number of Motzkin prefixes of length `L` from `h` (for `h ≤ 4`). -/
noncomputable def P (L h : ℕ) : ℤ := ∑ y ∈ Finset.range (L + 5), (x 0 L h y : ℤ)

theorem P_succ (L h : ℕ) (hh : h ≤ 4) : P (L + 1) h + (x 0 L h 0 : ℤ) = 3 * P L h := by
  unfold P
  exact_mod_cast P_succN L h hh

theorem P1 (L : ℕ) : P L 1 = T L 0 + 2 * T L 1 + T L 2 := by
  induction L with
  | zero => simp [P, x_len0, T_zero]
  | succ L ih =>
    have e := P_succ L 1 (by omega)
    have c := x0_closed L 1 0 (-1) 3 (by norm_num) (by norm_num)
    have p0 := T_succ' L 0 (-1) 1 (by norm_num) (by norm_num)
    have p1 := T_succ' L 1 0 2 (by norm_num) (by norm_num)
    have p2 := T_succ' L 2 1 3 (by norm_num) (by norm_num)
    have s1 := T_symm' L 1 (-1) (by norm_num)
    linarith

theorem P3 (L : ℕ) : P L 3 = T L 0 + 2 * T L 1 + 2 * T L 2 + 2 * T L 3 + T L 4 := by
  induction L with
  | zero => simp [P, x_len0, T_zero]
  | succ L ih =>
    have e := P_succ L 3 (by omega)
    have c := x0_closed L 3 0 (-3) 5 (by norm_num) (by norm_num)
    have p0 := T_succ' L 0 (-1) 1 (by norm_num) (by norm_num)
    have p1 := T_succ' L 1 0 2 (by norm_num) (by norm_num)
    have p2 := T_succ' L 2 1 3 (by norm_num) (by norm_num)
    have p3 := T_succ' L 3 2 4 (by norm_num) (by norm_num)
    have p4 := T_succ' L 4 3 5 (by norm_num) (by norm_num)
    have s1 := T_symm' L 1 (-1) (by norm_num)
    have s3 := T_symm' L 3 (-3) (by norm_num)
    linarith

theorem mem_X_last (n : ℕ) (s : Fin (n + 1) → ℕ) (hs : s ∈ walks n) :
    s ∈ X 1 (n + 1) 2 (s (Fin.last n)) :=
  ⟨hs.1, fun i hi => congrArg s (Fin.ext (by rw [Fin.val_last]; omega)), hs.2.1, hs.2.2⟩

theorem last_lt (n : ℕ) (s : Fin (n + 1) → ℕ) (hs : s ∈ walks n) : s (Fin.last n) < n + 4 := by
  have := step_le' 1 (n + 1) 2 _ s (mem_X_last n s hs) (Fin.last n)
  rw [Fin.val_last] at this
  omega

theorem walks_finite (n : ℕ) : (walks n).Finite := by
  apply ((Finset.range (n + 4)).finite_toSet.biUnion (fun y _ => X_finite 1 (n + 1) 2 y)).subset
  intro s hs
  simp only [Finset.coe_range, Set.mem_Iio, Set.mem_iUnion, exists_prop]
  exact ⟨_, last_lt n s hs, mem_X_last n s hs⟩

/-- Sorting the walks by their last value. -/
theorem a_sum (n : ℕ) : a n = ∑ y ∈ Finset.range (n + 4), (x 1 n 2 y : ℤ) := by
  unfold a
  rw [← Nat.cast_sum]
  congr 1
  rw [Set.ncard_eq_toFinset_card _ (walks_finite n),
    Finset.card_eq_sum_card_fiberwise (f := fun s => s (Fin.last n)) (t := Finset.range (n + 4))
      (fun s hs => Finset.mem_range.2 (last_lt n s ((walks_finite n).mem_toFinset.1 hs)))]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  unfold x
  rw [Set.ncard_eq_toFinset_card _ (X_finite 1 (n + 1) 2 y)]
  congr 1
  ext s
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨hs, rfl⟩; exact mem_X_last n s hs
  · intro hs
    exact ⟨⟨hs.1, hs.2.2.1, hs.2.2.2⟩, hs.2.1 _ (by simp)⟩

/-- `a (L+1) = 2 T(L,0) + 4 T(L,1) + 3 T(L,2) + 2 T(L,3) + T(L,4)`. -/
theorem a_closed (L : ℕ) : a (L + 1) = 2 * T L 0 + 4 * T L 1 + 3 * T L 2 + 2 * T L 3 + T L 4 := by
  have e : a (L + 1) = P L 1 + P L 3 := by
    rw [a_sum, show L + 1 + 4 = L + 5 by omega]
    unfold P
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [show x 1 (L + 1) 2 y = x 0 L 1 y + x 0 L 3 y from G 1 L y, Nat.cast_add]
  rw [e, P1, P3]
  ring

theorem a_zero : a 0 = 1 := by
  rw [a_sum]
  simp [x_len0]

end OMA.A026165Proof

open OMA.S_oeis_a026165 OMA.A026165Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a026165.main := by
  intro n hn
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · obtain rfl : n = 4 := by omega
    have e4 : a 4 = 49 := by rw [a_closed 3]; decide
    have e3 : a 3 = 17 := by rw [a_closed 2]; decide
    have e2 : a 2 = 6 := by rw [a_closed 1]; decide
    have e1 : a 1 = 2 := by rw [a_closed 0]; decide
    norm_num [e4, e3, e2, e1, a_zero]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have h0 : a (m + 5) = 2 * T (m + 4) 0 + 4 * T (m + 4) 1 + 3 * T (m + 4) 2 + 2 * T (m + 4) 3 + T (m + 4) 4 := a_closed (m + 4)
    have h1 : a (m + 5 - 1) = 2 * T (m + 3) 0 + 4 * T (m + 3) 1 + 3 * T (m + 3) 2 + 2 * T (m + 3) 3 + T (m + 3) 4 := by
      rw [show m + 5 - 1 = m + 3 + 1 by omega]; exact a_closed (m + 3)
    have h2 : a (m + 5 - 2) = 2 * T (m + 2) 0 + 4 * T (m + 2) 1 + 3 * T (m + 2) 2 + 2 * T (m + 2) 3 + T (m + 2) 4 := by
      rw [show m + 5 - 2 = m + 2 + 1 by omega]; exact a_closed (m + 2)
    have h3 : a (m + 5 - 3) = 2 * T (m + 1) 0 + 4 * T (m + 1) 1 + 3 * T (m + 1) 2 + 2 * T (m + 1) 3 + T (m + 1) 4 := by
      rw [show m + 5 - 3 = m + 1 + 1 by omega]; exact a_closed (m + 1)
    have h4 : a (m + 5 - 4) = 2 * T m 0 + 4 * T m 1 + 3 * T m 2 + 2 * T m 3 + T m 4 := by
      rw [show m + 5 - 4 = m + 1 by omega]; exact a_closed (m)
    rw [h0, h1, h2, h3, h4]
    have r0_2 := T_relZ (m) (m : ℤ) (by omega) 1 2 0 (by norm_num) (by norm_num)
    have r0_3 := T_relZ (m) (m : ℤ) (by omega) 2 3 1 (by norm_num) (by norm_num)
    have r0_4 := T_relZ (m) (m : ℤ) (by omega) 3 4 2 (by norm_num) (by norm_num)
    have u1 : T (m + 1) 0 = T m 0 + 2 * T m 1 := TU (m)
    have v1 : T (m + 1) 1 = T m 0 + T m 1 + T m 2 := TV (m)
    have r1_2 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 1 2 0 (by norm_num) (by norm_num)
    have r1_3 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 2 3 1 (by norm_num) (by norm_num)
    have r1_4 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 3 4 2 (by norm_num) (by norm_num)
    have u2 : T (m + 2) 0 = T (m + 1) 0 + 2 * T (m + 1) 1 := TU (m + 1)
    have v2 : T (m + 2) 1 = T (m + 1) 0 + T (m + 1) 1 + T (m + 1) 2 := TV (m + 1)
    have r2_2 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 1 2 0 (by norm_num) (by norm_num)
    have r2_3 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 2 3 1 (by norm_num) (by norm_num)
    have r2_4 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 3 4 2 (by norm_num) (by norm_num)
    have u3 : T (m + 3) 0 = T (m + 2) 0 + 2 * T (m + 2) 1 := TU (m + 2)
    have v3 : T (m + 3) 1 = T (m + 2) 0 + T (m + 2) 1 + T (m + 2) 2 := TV (m + 2)
    have r3_2 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 1 2 0 (by norm_num) (by norm_num)
    have r3_3 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 2 3 1 (by norm_num) (by norm_num)
    have r3_4 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 3 4 2 (by norm_num) (by norm_num)
    have u4 : T (m + 4) 0 = T (m + 3) 0 + 2 * T (m + 3) 1 := TU (m + 3)
    have v4 : T (m + 4) 1 = T (m + 3) 0 + T (m + 3) 1 + T (m + 3) 2 := TV (m + 3)
    have r4_2 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 1 2 0 (by norm_num) (by norm_num)
    have r4_3 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 2 3 1 (by norm_num) (by norm_num)
    have r4_4 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 3 4 2 (by norm_num) (by norm_num)
    push_cast
    have hD : (1 * ((m : ℤ) + 3) * ((m : ℤ) + 4) * ((m : ℤ) + 5) * ((m : ℤ) + 6) * ((m : ℤ) + 7) : ℤ) ≠ 0 := by positivity
    refine (mul_eq_zero.mp ?_).resolve_left hD
    linear_combination (-12600 - 17760 * (m : ℤ) - 9378 * (m : ℤ) ^ 2 - 2316 * (m : ℤ) ^ 3 - 270 * (m : ℤ) ^ 4 - 12 * (m : ℤ) ^ 5) * r0_2
        + (-12600 - 17760 * (m : ℤ) - 9378 * (m : ℤ) ^ 2 - 2316 * (m : ℤ) ^ 3 - 270 * (m : ℤ) ^ 4 - 12 * (m : ℤ) ^ 5) * r0_3
        + (-7560 - 10152 * (m : ℤ) - 5118 * (m : ℤ) ^ 2 - 1218 * (m : ℤ) ^ 3 - 138 * (m : ℤ) ^ 4 - 6 * (m : ℤ) ^ 5) * r0_4
        + (35280 + 60816 * (m : ℤ) + 42492 * (m : ℤ) ^ 2 + 15348 * (m : ℤ) ^ 3 + 3000 * (m : ℤ) ^ 4 + 300 * (m : ℤ) ^ 5 + 12 * (m : ℤ) ^ 6) * u1
        + (25200 + 48120 * (m : ℤ) + 36516 * (m : ℤ) ^ 2 + 14010 * (m : ℤ) ^ 3 + 2856 * (m : ℤ) ^ 4 + 294 * (m : ℤ) ^ 5 + 12 * (m : ℤ) ^ 6) * v1
        + (25200 + 29262 * (m : ℤ) + 13417 * (m : ℤ) ^ 2 + 3010 * (m : ℤ) ^ 3 + 329 * (m : ℤ) ^ 4 + 14 * (m : ℤ) ^ 5) * r1_2
        + (17640 + 20790 * (m : ℤ) + 9575 * (m : ℤ) ^ 2 + 2150 * (m : ℤ) ^ 3 + 235 * (m : ℤ) ^ 4 + 10 * (m : ℤ) ^ 5) * r1_3
        + (10080 + 11520 * (m : ℤ) + 5150 * (m : ℤ) ^ 2 + 1125 * (m : ℤ) ^ 3 + 120 * (m : ℤ) ^ 4 + 5 * (m : ℤ) ^ 5) * r1_4
        + (-60480 - 81972 * (m : ℤ) - 45210 * (m : ℤ) ^ 2 - 13026 * (m : ℤ) ^ 3 - 2076 * (m : ℤ) ^ 4 - 174 * (m : ℤ) ^ 5 - 6 * (m : ℤ) ^ 6) * u2
        + (-30240 - 47034 * (m : ℤ) - 29517 * (m : ℤ) ^ 2 - 9603 * (m : ℤ) ^ 3 - 1713 * (m : ℤ) ^ 4 - 159 * (m : ℤ) ^ 5 - 6 * (m : ℤ) ^ 6) * v2
        + (9576 + 12792 * (m : ℤ) + 6476 * (m : ℤ) ^ 2 + 1560 * (m : ℤ) ^ 3 + 180 * (m : ℤ) ^ 4 + 8 * (m : ℤ) ^ 5) * r2_2
        + (19656 + 22422 * (m : ℤ) + 10033 * (m : ℤ) ^ 2 + 2202 * (m : ℤ) ^ 3 + 237 * (m : ℤ) ^ 4 + 10 * (m : ℤ) ^ 5) * r2_3
        + (10920 + 12214 * (m : ℤ) + 5351 * (m : ℤ) ^ 2 + 1149 * (m : ℤ) ^ 3 + 121 * (m : ℤ) ^ 4 + 5 * (m : ℤ) ^ 5) * r2_4
        + (-91728 - 127596 * (m : ℤ) - 73182 * (m : ℤ) ^ 2 - 22146 * (m : ℤ) ^ 3 - 3726 * (m : ℤ) ^ 4 - 330 * (m : ℤ) ^ 5 - 12 * (m : ℤ) ^ 6) * u3
        + (-118944 - 157944 * (m : ℤ) - 86412 * (m : ℤ) ^ 2 - 24966 * (m : ℤ) ^ 3 - 4020 * (m : ℤ) ^ 4 - 342 * (m : ℤ) ^ 5 - 12 * (m : ℤ) ^ 6) * v3
        + (-27816 - 31718 * (m : ℤ) - 14175 * (m : ℤ) ^ 2 - 3104 * (m : ℤ) ^ 3 - 333 * (m : ℤ) ^ 4 - 14 * (m : ℤ) ^ 5) * r3_2
        + (-22440 - 24958 * (m : ℤ) - 10869 * (m : ℤ) ^ 2 - 2320 * (m : ℤ) ^ 3 - 243 * (m : ℤ) ^ 4 - 10 * (m : ℤ) ^ 5) * r3_3
        + (-12240 - 13428 * (m : ℤ) - 5756 * (m : ℤ) ^ 2 - 1207 * (m : ℤ) ^ 3 - 124 * (m : ℤ) ^ 4 - 5 * (m : ℤ) ^ 5) * r3_4
        + (77760 + 99792 * (m : ℤ) + 52488 * (m : ℤ) ^ 2 + 14508 * (m : ℤ) ^ 3 + 2226 * (m : ℤ) ^ 4 + 180 * (m : ℤ) ^ 5 + 6 * (m : ℤ) ^ 6) * u4
        + (85320 + 108054 * (m : ℤ) + 56013 * (m : ℤ) ^ 2 + 15243 * (m : ℤ) ^ 3 + 2301 * (m : ℤ) ^ 4 + 183 * (m : ℤ) ^ 5 + 6 * (m : ℤ) ^ 6) * v4
        + (9360 + 10332 * (m : ℤ) + 4462 * (m : ℤ) ^ 2 + 944 * (m : ℤ) ^ 3 + 98 * (m : ℤ) ^ 4 + 4 * (m : ℤ) ^ 5) * r4_2
        + (4680 + 5166 * (m : ℤ) + 2231 * (m : ℤ) ^ 2 + 472 * (m : ℤ) ^ 3 + 49 * (m : ℤ) ^ 4 + 2 * (m : ℤ) ^ 5) * r4_3
        + (2520 + 2754 * (m : ℤ) + 1175 * (m : ℤ) ^ 2 + 245 * (m : ℤ) ^ 3 + 25 * (m : ℤ) ^ 4 + (m : ℤ) ^ 5) * r4_4
