import OMAStatements.S_oeis_a026329
import Mathlib

-- Credit: @hermitokatt (Lean proof with Claude Code)

/-!
Proof of R. J. Mathar's recurrence for A026329 (Motzkin walks from 2 to 6).

1. Splitting a walk at its last step gives Pascal-like recursions for the number `x k L h y` of
   nonnegative walks of length `L` from `h` to `y` (the first `k` steps are ±1, later steps are
   in {-1, 0, 1}).
2. Trinomial coefficients `T L d` (with `T (L+1) d = T L (d-1) + T L d + T L (d+1)`) give the
   reflection principle `x 0 L h y = T(L, y-h) - T(L, y+h+2)`, hence a closed form for `a`.
3. The row relation `(L+d+1) T(L,d+1) + d T(L,d) - (L-d+1) T(L,d-1) = 0` expresses all values
   through `T(m,0)` and `T(m,1)`; the recurrence, multiplied by a positive polynomial `D(m)`, is
   an explicit linear combination of these relations (checked by `linear_combination`).
-/

namespace OMA.A026329Proof

open OMA.S_oeis_a026329

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

theorem walks_eq (n : ℕ) : walks n = X 0 (n + 1) 2 6 := by
  ext s
  constructor
  · rintro ⟨h0, hN, h1⟩
    exact ⟨h0, fun i hi => hN i (by omega), fun i j hij hj => absurd hij (by omega),
      fun i j hij _ => h1 i j hij⟩
  · rintro ⟨h0, hN, h1, h2⟩
    exact ⟨h0, fun i hi => hN i (by omega), fun i j hij => h2 i j hij (by omega)⟩

theorem a_closed (L : ℕ) : a L = T L 4 - T L 10 := by
  unfold a
  rw [walks_eq]
  exact x0_closed L 2 6 (4) (10) (by omega) (by omega)

end OMA.A026329Proof

open OMA.S_oeis_a026329 OMA.A026329Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a026329.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h0 : a (m + 4) = T (m + 4) 4 - T (m + 4) 10 := a_closed (m + 4)
  have h1 : a (m + 4 - 1) = T (m + 3) 4 - T (m + 3) 10 := by
    rw [show m + 4 - 1 = m + 3 by omega]; exact a_closed (m + 3)
  have h2 : a (m + 4 - 2) = T (m + 2) 4 - T (m + 2) 10 := by
    rw [show m + 4 - 2 = m + 2 by omega]; exact a_closed (m + 2)
  have h3 : a (m + 4 - 3) = T (m + 1) 4 - T (m + 1) 10 := by
    rw [show m + 4 - 3 = m + 1 by omega]; exact a_closed (m + 1)
  have h4 : a (m + 4 - 4) = T m 4 - T m 10 := by
    rw [show m + 4 - 4 = m by omega]; exact a_closed (m)
  rw [h0, h1, h2, h3, h4]
  have r0_2 := T_relZ (m) (m : ℤ) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r0_3 := T_relZ (m) (m : ℤ) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have r0_4 := T_relZ (m) (m : ℤ) (by omega) 3 4 2 (by norm_num) (by norm_num)
  have r0_5 := T_relZ (m) (m : ℤ) (by omega) 4 5 3 (by norm_num) (by norm_num)
  have r0_6 := T_relZ (m) (m : ℤ) (by omega) 5 6 4 (by norm_num) (by norm_num)
  have r0_7 := T_relZ (m) (m : ℤ) (by omega) 6 7 5 (by norm_num) (by norm_num)
  have r0_8 := T_relZ (m) (m : ℤ) (by omega) 7 8 6 (by norm_num) (by norm_num)
  have r0_9 := T_relZ (m) (m : ℤ) (by omega) 8 9 7 (by norm_num) (by norm_num)
  have r0_10 := T_relZ (m) (m : ℤ) (by omega) 9 10 8 (by norm_num) (by norm_num)
  have u1 : T (m + 1) 0 = T m 0 + 2 * T m 1 := TU (m)
  have v1 : T (m + 1) 1 = T m 0 + T m 1 + T m 2 := TV (m)
  have r1_2 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r1_3 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have r1_4 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 3 4 2 (by norm_num) (by norm_num)
  have r1_5 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 4 5 3 (by norm_num) (by norm_num)
  have r1_6 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 5 6 4 (by norm_num) (by norm_num)
  have r1_7 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 6 7 5 (by norm_num) (by norm_num)
  have r1_8 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 7 8 6 (by norm_num) (by norm_num)
  have r1_9 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 8 9 7 (by norm_num) (by norm_num)
  have r1_10 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 9 10 8 (by norm_num) (by norm_num)
  have u2 : T (m + 2) 0 = T (m + 1) 0 + 2 * T (m + 1) 1 := TU (m + 1)
  have v2 : T (m + 2) 1 = T (m + 1) 0 + T (m + 1) 1 + T (m + 1) 2 := TV (m + 1)
  have r2_2 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r2_3 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have r2_4 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 3 4 2 (by norm_num) (by norm_num)
  have r2_5 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 4 5 3 (by norm_num) (by norm_num)
  have r2_6 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 5 6 4 (by norm_num) (by norm_num)
  have r2_7 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 6 7 5 (by norm_num) (by norm_num)
  have r2_8 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 7 8 6 (by norm_num) (by norm_num)
  have r2_9 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 8 9 7 (by norm_num) (by norm_num)
  have r2_10 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 9 10 8 (by norm_num) (by norm_num)
  have u3 : T (m + 3) 0 = T (m + 2) 0 + 2 * T (m + 2) 1 := TU (m + 2)
  have v3 : T (m + 3) 1 = T (m + 2) 0 + T (m + 2) 1 + T (m + 2) 2 := TV (m + 2)
  have r3_2 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r3_3 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have r3_4 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 3 4 2 (by norm_num) (by norm_num)
  have r3_5 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 4 5 3 (by norm_num) (by norm_num)
  have r3_6 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 5 6 4 (by norm_num) (by norm_num)
  have r3_7 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 6 7 5 (by norm_num) (by norm_num)
  have r3_8 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 7 8 6 (by norm_num) (by norm_num)
  have r3_9 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 8 9 7 (by norm_num) (by norm_num)
  have r3_10 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 9 10 8 (by norm_num) (by norm_num)
  have u4 : T (m + 4) 0 = T (m + 3) 0 + 2 * T (m + 3) 1 := TU (m + 3)
  have v4 : T (m + 4) 1 = T (m + 3) 0 + T (m + 3) 1 + T (m + 3) 2 := TV (m + 3)
  have r4_2 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r4_3 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have r4_4 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 3 4 2 (by norm_num) (by norm_num)
  have r4_5 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 4 5 3 (by norm_num) (by norm_num)
  have r4_6 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 5 6 4 (by norm_num) (by norm_num)
  have r4_7 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 6 7 5 (by norm_num) (by norm_num)
  have r4_8 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 7 8 6 (by norm_num) (by norm_num)
  have r4_9 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 8 9 7 (by norm_num) (by norm_num)
  have r4_10 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 9 10 8 (by norm_num) (by norm_num)
  push_cast
  have hD : (1 * ((m : ℤ) + 4) * ((m : ℤ) + 5) * ((m : ℤ) + 6) * ((m : ℤ) + 7) * ((m : ℤ) + 8) * ((m : ℤ) + 9) * ((m : ℤ) + 10) * ((m : ℤ) + 11) * ((m : ℤ) + 12) * ((m : ℤ) + 13) : ℤ) ≠ 0 := by positivity
  refine (mul_eq_zero.mp ?_).resolve_left hD
  linear_combination (3736212480 + 1779055488 * (m : ℤ) + 267037344 * (m : ℤ) ^ 2 + 719029584 * (m : ℤ) ^ 3 + 475001352 * (m : ℤ) ^ 4 + 131553828 * (m : ℤ) ^ 5 + 21953484 * (m : ℤ) ^ 6 + 2680776 * (m : ℤ) ^ 7 + 232848 * (m : ℤ) ^ 8 + 11844 * (m : ℤ) ^ 9 + 252 * (m : ℤ) ^ 10) * r0_2
      + (-11208637440 - 24723957888 * (m : ℤ) - 19923363936 * (m : ℤ) ^ 2 - 8105167728 * (m : ℤ) ^ 3 - 1989276408 * (m : ℤ) ^ 4 - 323623692 * (m : ℤ) ^ 5 - 32952276 * (m : ℤ) ^ 6 - 1427832 * (m : ℤ) ^ 7 + 61488 * (m : ℤ) ^ 8 + 8820 * (m : ℤ) ^ 9 + 252 * (m : ℤ) ^ 10) * r0_3
      + (11208637440 + 28813034880 * (m : ℤ) + 28860445152 * (m : ℤ) ^ 2 + 15147191808 * (m : ℤ) ^ 3 + 4713880248 * (m : ℤ) ^ 4 + 937904688 * (m : ℤ) ^ 5 + 126307944 * (m : ℤ) ^ 6 + 11868192 * (m : ℤ) ^ 7 + 757512 * (m : ℤ) ^ 8 + 29232 * (m : ℤ) ^ 9 + 504 * (m : ℤ) ^ 10) * r0_4
      + (-352864512 * (m : ℤ) - 813383424 * (m : ℤ) ^ 2 - 672030576 * (m : ℤ) ^ 3 - 246891456 * (m : ℤ) ^ 4 - 33486012 * (m : ℤ) ^ 5 + 3356892 * (m : ℤ) ^ 6 + 1662696 * (m : ℤ) ^ 7 + 211176 * (m : ℤ) ^ 8 + 11844 * (m : ℤ) ^ 9 + 252 * (m : ℤ) ^ 10) * r0_5
      + (7472424960 + 11332991232 * (m : ℤ) + 6645863808 * (m : ℤ) ^ 2 + 1849516272 * (m : ℤ) ^ 3 + 203380752 * (m : ℤ) ^ 4 - 18475620 * (m : ℤ) ^ 5 - 9498384 * (m : ℤ) ^ 6 - 1634580 * (m : ℤ) ^ 7 - 183312 * (m : ℤ) ^ 8 - 13932 * (m : ℤ) ^ 9 - 624 * (m : ℤ) ^ 10 - 12 * (m : ℤ) ^ 11) * r0_6
      + (-7472424960 - 12474611712 * (m : ℤ) - 8256829824 * (m : ℤ) ^ 2 - 2666174976 * (m : ℤ) ^ 3 - 355318176 * (m : ℤ) ^ 4 + 30276288 * (m : ℤ) ^ 5 + 18893952 * (m : ℤ) ^ 6 + 3079296 * (m : ℤ) ^ 7 + 255456 * (m : ℤ) ^ 8 + 10944 * (m : ℤ) ^ 9 + 192 * (m : ℤ) ^ 10) * r0_7
      + (-103783680 * (m : ℤ) - 295163136 * (m : ℤ) ^ 2 - 340179120 * (m : ℤ) ^ 3 - 213011808 * (m : ℤ) ^ 4 - 81199428 * (m : ℤ) ^ 5 - 19849536 * (m : ℤ) ^ 6 - 3169908 * (m : ℤ) ^ 7 - 328032 * (m : ℤ) ^ 8 - 21132 * (m : ℤ) ^ 9 - 768 * (m : ℤ) ^ 10 - 12 * (m : ℤ) ^ 11) * r0_8
      + (7472424960 + 14713373952 * (m : ℤ) + 12435990912 * (m : ℤ) ^ 2 + 5962471344 * (m : ℤ) ^ 3 + 1800993744 * (m : ℤ) ^ 4 + 358967700 * (m : ℤ) ^ 5 + 47911500 * (m : ℤ) ^ 6 + 4235976 * (m : ℤ) ^ 7 + 237816 * (m : ℤ) ^ 8 + 7668 * (m : ℤ) ^ 9 + 108 * (m : ℤ) ^ 10) * r0_9
      + (-7472424960 - 15543643392 * (m : ℤ) - 14070810240 * (m : ℤ) ^ 2 - 7344248112 * (m : ℤ) ^ 3 - 2463490560 * (m : ℤ) ^ 4 - 559078116 * (m : ℤ) ^ 5 - 87796800 * (m : ℤ) ^ 6 - 9559476 * (m : ℤ) ^ 7 - 708480 * (m : ℤ) ^ 8 - 34092 * (m : ℤ) ^ 9 - 960 * (m : ℤ) ^ 10 - 12 * (m : ℤ) ^ 11) * r0_10
      + (-7472424960 - 8000052480 * (m : ℤ) + 6846686784 * (m : ℤ) ^ 2 + 12804263136 * (m : ℤ) ^ 3 + 7309922256 * (m : ℤ) ^ 4 + 2272207896 * (m : ℤ) ^ 5 + 444178728 * (m : ℤ) ^ 6 + 56158704 * (m : ℤ) ^ 7 + 4402944 * (m : ℤ) ^ 8 + 192024 * (m : ℤ) ^ 9 + 3528 * (m : ℤ) ^ 10) * u1
      + (7472424960 + 4263840000 * (m : ℤ) - 8625742272 * (m : ℤ) ^ 2 - 13071300480 * (m : ℤ) ^ 3 - 8028951840 * (m : ℤ) ^ 4 - 2747209248 * (m : ℤ) ^ 5 - 575732556 * (m : ℤ) ^ 6 - 78112188 * (m : ℤ) ^ 7 - 7083720 * (m : ℤ) ^ 8 - 424872 * (m : ℤ) ^ 9 - 15372 * (m : ℤ) ^ 10 - 252 * (m : ℤ) ^ 11) * v1
      + (-5094835200 - 2949706368 * (m : ℤ) + 3076442208 * (m : ℤ) ^ 2 + 3289396320 * (m : ℤ) ^ 3 + 1329346872 * (m : ℤ) ^ 4 + 303441264 * (m : ℤ) ^ 5 + 42234192 * (m : ℤ) ^ 6 + 3517920 * (m : ℤ) ^ 7 + 159768 * (m : ℤ) ^ 8 + 3024 * (m : ℤ) ^ 9) * r1_2
      + (12630159360 + 19470624768 * (m : ℤ) + 12374298048 * (m : ℤ) ^ 2 + 4353252624 * (m : ℤ) ^ 3 + 955072272 * (m : ℤ) ^ 4 + 134633268 * (m : ℤ) ^ 5 + 11101356 * (m : ℤ) ^ 6 + 281736 * (m : ℤ) ^ 7 - 35112 * (m : ℤ) ^ 8 - 3276 * (m : ℤ) ^ 9 - 84 * (m : ℤ) ^ 10) * r1_3
      + (-17108582400 - 30700873728 * (m : ℤ) - 23269263360 * (m : ℤ) ^ 2 - 9887348352 * (m : ℤ) ^ 3 - 2639714112 * (m : ℤ) ^ 4 - 470971536 * (m : ℤ) ^ 5 - 58179912 * (m : ℤ) ^ 6 - 5022528 * (m : ℤ) ^ 7 - 293328 * (m : ℤ) ^ 8 - 10416 * (m : ℤ) ^ 9 - 168 * (m : ℤ) ^ 10) * r1_4
      + (402554880 + 996258816 * (m : ℤ) + 918115968 * (m : ℤ) ^ 2 + 396426240 * (m : ℤ) ^ 3 + 71013432 * (m : ℤ) ^ 4 - 4838652 * (m : ℤ) ^ 5 - 4668804 * (m : ℤ) ^ 6 - 914760 * (m : ℤ) ^ 7 - 88032 * (m : ℤ) ^ 8 - 4284 * (m : ℤ) ^ 9 - 84 * (m : ℤ) ^ 10) * r1_5
      + (-5233213440 - 6151661568 * (m : ℤ) - 2779742976 * (m : ℤ) ^ 2 - 534880640 * (m : ℤ) ^ 3 + 5054640 * (m : ℤ) ^ 4 + 25334480 * (m : ℤ) ^ 5 + 6309828 * (m : ℤ) ^ 6 + 902436 * (m : ℤ) ^ 7 + 87720 * (m : ℤ) ^ 8 + 5768 * (m : ℤ) ^ 9 + 228 * (m : ℤ) ^ 10 + 4 * (m : ℤ) ^ 11) * r1_6
      + (5937684480 + 7578971136 * (m : ℤ) + 3743182848 * (m : ℤ) ^ 2 + 780228160 * (m : ℤ) ^ 3 - 16887968 * (m : ℤ) ^ 4 - 46385472 * (m : ℤ) ^ 5 - 11270784 * (m : ℤ) ^ 6 - 1406400 * (m : ℤ) ^ 7 - 100512 * (m : ℤ) ^ 8 - 3904 * (m : ℤ) ^ 9 - 64 * (m : ℤ) ^ 10) * r1_7
      + (201277440 + 604459008 * (m : ℤ) + 751044864 * (m : ℤ) ^ 2 + 518716672 * (m : ℤ) ^ 3 + 223908528 * (m : ℤ) ^ 4 + 63965072 * (m : ℤ) ^ 5 + 12417300 * (m : ℤ) ^ 6 + 1645764 * (m : ℤ) ^ 7 + 146472 * (m : ℤ) ^ 8 + 8360 * (m : ℤ) ^ 9 + 276 * (m : ℤ) ^ 10 + 4 * (m : ℤ) ^ 11) * r1_8
      + (-8151736320 - 13158733824 * (m : ℤ) - 9323413632 * (m : ℤ) ^ 2 - 3823239744 * (m : ℤ) ^ 3 - 1005953976 * (m : ℤ) ^ 4 - 177622956 * (m : ℤ) ^ 5 - 21332052 * (m : ℤ) ^ 6 - 1721736 * (m : ℤ) ^ 7 - 89424 * (m : ℤ) ^ 8 - 2700 * (m : ℤ) ^ 9 - 36 * (m : ℤ) ^ 10) * r1_9
      + (9057484800 + 15526563840 * (m : ℤ) + 11821430016 * (m : ℤ) ^ 2 + 5283979008 * (m : ℤ) ^ 3 + 1542531056 * (m : ℤ) ^ 4 + 309131504 * (m : ℤ) ^ 5 + 43438164 * (m : ℤ) ^ 6 + 4283268 * (m : ℤ) ^ 7 + 290664 * (m : ℤ) ^ 8 + 12936 * (m : ℤ) ^ 9 + 340 * (m : ℤ) ^ 10 + 4 * (m : ℤ) ^ 11) * r1_10
      + (4755179520 - 11360514816 * (m : ℤ) - 31739875776 * (m : ℤ) ^ 2 - 28594626816 * (m : ℤ) ^ 3 - 13744036656 * (m : ℤ) ^ 4 - 4038260016 * (m : ℤ) ^ 5 - 766634904 * (m : ℤ) ^ 6 - 96102216 * (m : ℤ) ^ 7 - 7930944 * (m : ℤ) ^ 8 - 415968 * (m : ℤ) ^ 9 - 12600 * (m : ℤ) ^ 10 - 168 * (m : ℤ) ^ 11) * u2
      + (-7132769280 + 11405003904 * (m : ℤ) + 38459826720 * (m : ℤ) ^ 2 + 35033051424 * (m : ℤ) ^ 3 + 16435215720 * (m : ℤ) ^ 4 + 4677679776 * (m : ℤ) ^ 5 + 865138176 * (m : ℤ) ^ 6 + 106508808 * (m : ℤ) ^ 7 + 8656200 * (m : ℤ) ^ 8 + 445200 * (m : ℤ) ^ 9 + 13104 * (m : ℤ) ^ 10 + 168 * (m : ℤ) ^ 11) * v2
      + (2377589760 - 4489890048 * (m : ℤ) - 10575218304 * (m : ℤ) ^ 2 - 7737162216 * (m : ℤ) ^ 3 - 2946324066 * (m : ℤ) ^ 4 - 671154141 * (m : ℤ) ^ 5 - 97319649 * (m : ℤ) ^ 6 - 9232734 * (m : ℤ) ^ 7 - 568344 * (m : ℤ) ^ 8 - 21021 * (m : ℤ) ^ 9 - 357 * (m : ℤ) ^ 10) * r2_2
      + (-4755179520 + 2408386176 * (m : ℤ) + 6579609120 * (m : ℤ) ^ 2 + 3819035304 * (m : ℤ) ^ 3 + 1113491862 * (m : ℤ) ^ 4 + 189146223 * (m : ℤ) ^ 5 + 18156159 * (m : ℤ) ^ 6 + 608706 * (m : ℤ) ^ 7 - 56952 * (m : ℤ) ^ 8 - 6489 * (m : ℤ) ^ 9 - 189 * (m : ℤ) ^ 10) * r2_3
      + (8013358080 - 2535833664 * (m : ℤ) - 11898383616 * (m : ℤ) ^ 2 - 8510657652 * (m : ℤ) ^ 3 - 3049505298 * (m : ℤ) ^ 4 - 661921344 * (m : ℤ) ^ 5 - 93887766 * (m : ℤ) ^ 6 - 8960868 * (m : ℤ) ^ 7 - 566622 * (m : ℤ) ^ 8 - 21672 * (m : ℤ) ^ 9 - 378 * (m : ℤ) ^ 10) * r2_4
      + (-264176640 + 56572992 * (m : ℤ) + 445292064 * (m : ℤ) ^ 2 + 302479380 * (m : ℤ) ^ 3 + 64500660 * (m : ℤ) ^ 4 - 8958285 * (m : ℤ) ^ 5 - 7222005 * (m : ℤ) ^ 6 - 1539090 * (m : ℤ) ^ 7 - 163170 * (m : ℤ) ^ 8 - 8757 * (m : ℤ) ^ 9 - 189 * (m : ℤ) ^ 10) * r2_5
      + (1396362240 - 1186805952 * (m : ℤ) - 1629761760 * (m : ℤ) ^ 2 - 511019916 * (m : ℤ) ^ 3 - 4760760 * (m : ℤ) ^ 4 + 34222851 * (m : ℤ) ^ 5 + 10105200 * (m : ℤ) ^ 6 + 1601127 * (m : ℤ) ^ 7 + 165960 * (m : ℤ) ^ 8 + 11481 * (m : ℤ) ^ 9 + 480 * (m : ℤ) ^ 10 + 9 * (m : ℤ) ^ 11) * r2_6
      + (-1710858240 + 1363779072 * (m : ℤ) + 2112990144 * (m : ℤ) ^ 2 + 701814000 * (m : ℤ) ^ 3 - 9455400 * (m : ℤ) ^ 4 - 60787440 * (m : ℤ) ^ 5 - 17267040 * (m : ℤ) ^ 6 - 2425680 * (m : ℤ) ^ 7 - 191400 * (m : ℤ) ^ 8 - 8112 * (m : ℤ) ^ 9 - 144 * (m : ℤ) ^ 10) * r2_7
      + (-226437120 - 77756544 * (m : ℤ) + 367300656 * (m : ℤ) ^ 2 + 468584436 * (m : ℤ) ^ 3 + 268605708 * (m : ℤ) ^ 4 + 91077075 * (m : ℤ) ^ 5 + 19903716 * (m : ℤ) ^ 6 + 2885895 * (m : ℤ) ^ 7 + 276372 * (m : ℤ) ^ 8 + 16809 * (m : ℤ) ^ 9 + 588 * (m : ℤ) ^ 10 + 9 * (m : ℤ) ^ 11) * r2_8
      + (3396556800 - 1324460160 * (m : ℤ) - 4855251024 * (m : ℤ) ^ 2 - 3312931644 * (m : ℤ) ^ 3 - 1161977400 * (m : ℤ) ^ 4 - 248594913 * (m : ℤ) ^ 5 - 34346025 * (m : ℤ) ^ 6 - 3089826 * (m : ℤ) ^ 7 - 175230 * (m : ℤ) ^ 8 - 5697 * (m : ℤ) ^ 9 - 81 * (m : ℤ) ^ 10) * r2_9
      + (-4151347200 + 1241389440 * (m : ℤ) + 6081357936 * (m : ℤ) ^ 2 + 4588611012 * (m : ℤ) ^ 3 + 1788298116 * (m : ℤ) ^ 4 + 432946827 * (m : ℤ) ^ 5 + 69600132 * (m : ℤ) ^ 6 + 7592679 * (m : ℤ) ^ 7 + 557484 * (m : ℤ) ^ 8 + 26433 * (m : ℤ) ^ 9 + 732 * (m : ℤ) ^ 10 + 9 * (m : ℤ) ^ 11) * r2_10
      + (14020231680 * (m : ℤ) + 24996162240 * (m : ℤ) ^ 2 + 19442328864 * (m : ℤ) ^ 3 + 8670590796 * (m : ℤ) ^ 4 + 2453515218 * (m : ℤ) ^ 5 + 461357610 * (m : ℤ) ^ 6 + 58828308 * (m : ℤ) ^ 7 + 5097624 * (m : ℤ) ^ 8 + 293202 * (m : ℤ) ^ 9 + 10290 * (m : ℤ) ^ 10 + 168 * (m : ℤ) ^ 11) * u3
      + (-18778556160 * (m : ℤ) - 31095711360 * (m : ℤ) ^ 2 - 21987412944 * (m : ℤ) ^ 3 - 8784817104 * (m : ℤ) ^ 4 - 2203142886 * (m : ℤ) ^ 5 - 362199075 * (m : ℤ) ^ 6 - 39145407 * (m : ℤ) ^ 7 - 2659146 * (m : ℤ) ^ 8 - 98784 * (m : ℤ) ^ 9 - 1155 * (m : ℤ) ^ 10 + 21 * (m : ℤ) ^ 11) * v3
      + (4757074560 * (m : ℤ) + 7116264960 * (m : ℤ) ^ 2 + 4557472248 * (m : ℤ) ^ 3 + 1640367288 * (m : ℤ) ^ 4 + 367107720 * (m : ℤ) ^ 5 + 53536749 * (m : ℤ) ^ 6 + 5187462 * (m : ℤ) ^ 7 + 330372 * (m : ℤ) ^ 8 + 12810 * (m : ℤ) ^ 9 + 231 * (m : ℤ) ^ 10) * r3_2
      + (-5132937600 * (m : ℤ) - 5920780320 * (m : ℤ) ^ 2 - 2893607640 * (m : ℤ) ^ 3 - 778135806 * (m : ℤ) ^ 4 - 122965353 * (m : ℤ) ^ 5 - 10586016 * (m : ℤ) ^ 6 - 219240 * (m : ℤ) ^ 7 + 47376 * (m : ℤ) ^ 8 + 4473 * (m : ℤ) ^ 9 + 126 * (m : ℤ) ^ 10) * r3_3
      + (10265875200 * (m : ℤ) + 13445429760 * (m : ℤ) ^ 2 + 7641741744 * (m : ℤ) ^ 3 + 2482691400 * (m : ℤ) ^ 4 + 511665588 * (m : ℤ) ^ 5 + 70149618 * (m : ℤ) ^ 6 + 6494166 * (m : ℤ) ^ 7 + 397530 * (m : ℤ) ^ 8 + 14742 * (m : ℤ) ^ 9 + 252 * (m : ℤ) ^ 10) * r3_4
      + (-321330240 * (m : ℤ) - 357200928 * (m : ℤ) ^ 2 - 114348276 * (m : ℤ) ^ 3 + 19068840 * (m : ℤ) ^ 4 + 23967405 * (m : ℤ) ^ 5 + 7581042 * (m : ℤ) ^ 6 + 1257606 * (m : ℤ) ^ 7 + 118440 * (m : ℤ) ^ 8 + 5985 * (m : ℤ) ^ 9 + 126 * (m : ℤ) ^ 10) * r3_5
      + (1034933760 * (m : ℤ) + 752248512 * (m : ℤ) ^ 2 + 93562272 * (m : ℤ) ^ 3 - 78762876 * (m : ℤ) ^ 4 - 40219992 * (m : ℤ) ^ 5 - 9375009 * (m : ℤ) ^ 6 - 1351266 * (m : ℤ) ^ 7 - 130614 * (m : ℤ) ^ 8 - 8448 * (m : ℤ) ^ 9 - 333 * (m : ℤ) ^ 10 - 6 * (m : ℤ) ^ 11) * r3_6
      + (-1302013440 * (m : ℤ) - 942159168 * (m : ℤ) ^ 2 - 68991696 * (m : ℤ) ^ 3 + 143310120 * (m : ℤ) ^ 4 + 66801000 * (m : ℤ) ^ 5 + 14530152 * (m : ℤ) ^ 6 + 1822296 * (m : ℤ) ^ 7 + 135120 * (m : ℤ) ^ 8 + 5520 * (m : ℤ) ^ 9 + 96 * (m : ℤ) ^ 10) * r3_7
      + (-500774400 * (m : ℤ) - 884329920 * (m : ℤ) ^ 2 - 688229568 * (m : ℤ) ^ 3 - 310928892 * (m : ℤ) ^ 4 - 90330696 * (m : ℤ) ^ 5 - 17638845 * (m : ℤ) ^ 6 - 2345406 * (m : ℤ) ^ 7 - 209778 * (m : ℤ) ^ 8 - 12084 * (m : ℤ) ^ 9 - 405 * (m : ℤ) ^ 10 - 6 * (m : ℤ) ^ 11) * r3_8
      + (4131388800 * (m : ℤ) + 5261325840 * (m : ℤ) ^ 2 + 2927752236 * (m : ℤ) ^ 3 + 935036244 * (m : ℤ) ^ 4 + 189007749 * (m : ℤ) ^ 5 + 25094286 * (m : ℤ) ^ 6 + 2189754 * (m : ℤ) ^ 7 + 121176 * (m : ℤ) ^ 8 + 3861 * (m : ℤ) ^ 9 + 54 * (m : ℤ) ^ 10) * r3_9
      + (-5508518400 * (m : ℤ) - 7474144320 * (m : ℤ) ^ 2 - 4488261408 * (m : ℤ) ^ 3 - 1572020796 * (m : ℤ) ^ 4 - 355903248 * (m : ℤ) ^ 5 - 54459909 * (m : ℤ) ^ 6 - 5707926 * (m : ℤ) ^ 7 - 404874 * (m : ℤ) ^ 8 - 18612 * (m : ℤ) ^ 9 - 501 * (m : ℤ) ^ 10 - 6 * (m : ℤ) ^ 11) * r3_10
      + (-3504614400 * (m : ℤ) - 5895240960 * (m : ℤ) ^ 2 - 4375592256 * (m : ℤ) ^ 3 - 1886587248 * (m : ℤ) ^ 4 - 523793424 * (m : ℤ) ^ 5 - 98164584 * (m : ℤ) ^ 6 - 12662622 * (m : ℤ) ^ 7 - 1123332 * (m : ℤ) ^ 8 - 66696 * (m : ℤ) ^ 9 - 2436 * (m : ℤ) ^ 10 - 42 * (m : ℤ) ^ 11) * u4
      + (3253622400 * (m : ℤ) + 4785533760 * (m : ℤ) ^ 2 + 3029239416 * (m : ℤ) ^ 3 + 1078603932 * (m : ℤ) ^ 4 + 235618194 * (m : ℤ) ^ 5 + 31804227 * (m : ℤ) ^ 6 + 2391795 * (m : ℤ) ^ 7 + 42378 * (m : ℤ) ^ 8 - 8904 * (m : ℤ) ^ 9 - 777 * (m : ℤ) ^ 10 - 21 * (m : ℤ) ^ 11) * v4
      + (-876153600 * (m : ℤ) - 1254771840 * (m : ℤ) ^ 2 - 780205104 * (m : ℤ) ^ 3 - 276595536 * (m : ℤ) ^ 4 - 61799472 * (m : ℤ) ^ 5 - 9091278 * (m : ℤ) ^ 6 - 892836 * (m : ℤ) ^ 7 - 57624 * (m : ℤ) ^ 8 - 2268 * (m : ℤ) ^ 9 - 42 * (m : ℤ) ^ 10) * r4_2
      + (792489600 * (m : ℤ) + 912757440 * (m : ℤ) ^ 2 + 445425624 * (m : ℤ) ^ 3 + 118860924 * (m : ℤ) ^ 4 + 18319266 * (m : ℤ) ^ 5 + 1464561 * (m : ℤ) ^ 6 + 11466 * (m : ℤ) ^ 7 - 8904 * (m : ℤ) ^ 8 - 756 * (m : ℤ) ^ 9 - 21 * (m : ℤ) ^ 10) * r4_3
      + (-1835971200 * (m : ℤ) - 2371649280 * (m : ℤ) ^ 2 - 1336750968 * (m : ℤ) ^ 3 - 432652752 * (m : ℤ) ^ 4 - 89050542 * (m : ℤ) ^ 5 - 12183738 * (m : ℤ) ^ 6 - 1120812 * (m : ℤ) ^ 7 - 67788 * (m : ℤ) ^ 8 - 2478 * (m : ℤ) ^ 9 - 42 * (m : ℤ) ^ 10) * r4_4
      + (39513600 * (m : ℤ) + 27330240 * (m : ℤ) ^ 2 - 6846336 * (m : ℤ) ^ 3 - 13659828 * (m : ℤ) ^ 4 - 6396012 * (m : ℤ) ^ 5 - 1584009 * (m : ℤ) ^ 6 - 233604 * (m : ℤ) ^ 7 - 20622 * (m : ℤ) ^ 8 - 1008 * (m : ℤ) ^ 9 - 21 * (m : ℤ) ^ 10) * r4_5
      + (-93381120 * (m : ℤ) - 41807424 * (m : ℤ) ^ 2 + 23584480 * (m : ℤ) ^ 3 + 24286884 * (m : ℤ) ^ 4 + 8934008 * (m : ℤ) ^ 5 + 1892457 * (m : ℤ) ^ 6 + 260169 * (m : ℤ) ^ 7 + 24186 * (m : ℤ) ^ 8 + 1502 * (m : ℤ) ^ 9 + 57 * (m : ℤ) ^ 10 + (m : ℤ) ^ 11) * r4_6
      + (111283200 * (m : ℤ) + 34834560 * (m : ℤ) ^ 2 - 48801056 * (m : ℤ) ^ 3 - 40450688 * (m : ℤ) ^ 4 - 13896792 * (m : ℤ) ^ 5 - 2706984 * (m : ℤ) ^ 6 - 321384 * (m : ℤ) ^ 7 - 23112 * (m : ℤ) ^ 8 - 928 * (m : ℤ) ^ 9 - 16 * (m : ℤ) ^ 10) * r4_7
      + (133056000 * (m : ℤ) + 217752000 * (m : ℤ) ^ 2 + 158260480 * (m : ℤ) ^ 3 + 67255644 * (m : ℤ) ^ 4 + 18504716 * (m : ℤ) ^ 5 + 3444021 * (m : ℤ) ^ 6 + 439089 * (m : ℤ) ^ 7 + 37866 * (m : ℤ) ^ 8 + 2114 * (m : ℤ) ^ 9 + 69 * (m : ℤ) ^ 10 + (m : ℤ) ^ 11) * r4_8
      + (-718502400 * (m : ℤ) - 912409920 * (m : ℤ) ^ 2 - 506085408 * (m : ℤ) ^ 3 - 161038764 * (m : ℤ) ^ 4 - 32418792 * (m : ℤ) ^ 5 - 4284441 * (m : ℤ) ^ 6 - 371952 * (m : ℤ) ^ 7 - 20466 * (m : ℤ) ^ 8 - 648 * (m : ℤ) ^ 9 - 9 * (m : ℤ) ^ 10) * r4_9
      + (1037836800 * (m : ℤ) + 1397759040 * (m : ℤ) ^ 2 + 832391136 * (m : ℤ) ^ 3 + 288843260 * (m : ℤ) ^ 4 + 64720340 * (m : ℤ) ^ 5 + 9790725 * (m : ℤ) ^ 6 + 1013313 * (m : ℤ) ^ 7 + 70890 * (m : ℤ) ^ 8 + 3210 * (m : ℤ) ^ 9 + 85 * (m : ℤ) ^ 10 + (m : ℤ) ^ 11) * r4_10
