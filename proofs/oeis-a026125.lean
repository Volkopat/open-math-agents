import OMAStatements.S_oeis_a026125
import Mathlib

-- Credit: @hermitokatt (Lean proof with Claude Code)

/-!
Proof of R. J. Mathar's recurrence for A026125 (walks from 1 to 4, first step ±1).

1. Splitting a walk at its last step gives Pascal-like recursions for the number `x k L h y` of
   nonnegative walks of length `L` from `h` to `y` (the first `k` steps are ±1, later steps are
   in {-1, 0, 1}).
2. Trinomial coefficients `T L d` (with `T (L+1) d = T L (d-1) + T L d + T L (d+1)`) give the
   reflection principle `x 0 L h y = T(L, y-h) - T(L, y+h+2)`, hence a closed form for `a`.
3. The row relation `(L+d+1) T(L,d+1) + d T(L,d) - (L-d+1) T(L,d-1) = 0` expresses all values
   through `T(m,0)` and `T(m,1)`; the recurrence, multiplied by a positive polynomial `D(m)`, is
   an explicit linear combination of these relations (checked by `linear_combination`).
-/

namespace OMA.A026125Proof

open OMA.S_oeis_a026125

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

theorem walks_eq (n : ℕ) : walks n = X 1 (n + 1) 1 4 := by
  ext s
  constructor
  · rintro ⟨h0, hN, h1, h2⟩
    exact ⟨h0, fun i hi => hN i (by omega), h1, h2⟩
  · rintro ⟨h0, hN, h1, h2⟩
    exact ⟨h0, fun i hi => hN i (by omega), h1, h2⟩

theorem a_closed (L : ℕ) : a (L + 1) = T L 4 - T L 6 + T L 2 - T L 8 := by
  unfold a
  rw [walks_eq]
  change ((x 1 (L + 1) 1 4 : ℕ) : ℤ) = _
  rw [show x 1 (L + 1) 1 4 = x 0 L 0 4 + x 0 L 2 4 from G 0 L 4, Nat.cast_add,
    x0_closed L 0 4 (4) (6) (by omega) (by omega),
    x0_closed L 2 4 (2) (8) (by omega) (by omega)]
  ring

end OMA.A026125Proof

open OMA.S_oeis_a026125 OMA.A026125Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a026125.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have h0 : a (m + 5) = T (m + 4) 4 - T (m + 4) 6 + T (m + 4) 2 - T (m + 4) 8 := a_closed (m + 4)
  have h1 : a (m + 5 - 1) = T (m + 3) 4 - T (m + 3) 6 + T (m + 3) 2 - T (m + 3) 8 := by
    rw [show m + 5 - 1 = m + 3 + 1 by omega]; exact a_closed (m + 3)
  have h2 : a (m + 5 - 2) = T (m + 2) 4 - T (m + 2) 6 + T (m + 2) 2 - T (m + 2) 8 := by
    rw [show m + 5 - 2 = m + 2 + 1 by omega]; exact a_closed (m + 2)
  have h3 : a (m + 5 - 3) = T (m + 1) 4 - T (m + 1) 6 + T (m + 1) 2 - T (m + 1) 8 := by
    rw [show m + 5 - 3 = m + 1 + 1 by omega]; exact a_closed (m + 1)
  have h4 : a (m + 5 - 4) = T m 4 - T m 6 + T m 2 - T m 8 := by
    rw [show m + 5 - 4 = m + 1 by omega]; exact a_closed (m)
  rw [h0, h1, h2, h3, h4]
  have r0_2 := T_relZ (m) (m : ℤ) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r0_3 := T_relZ (m) (m : ℤ) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have r0_4 := T_relZ (m) (m : ℤ) (by omega) 3 4 2 (by norm_num) (by norm_num)
  have r0_5 := T_relZ (m) (m : ℤ) (by omega) 4 5 3 (by norm_num) (by norm_num)
  have r0_6 := T_relZ (m) (m : ℤ) (by omega) 5 6 4 (by norm_num) (by norm_num)
  have r0_7 := T_relZ (m) (m : ℤ) (by omega) 6 7 5 (by norm_num) (by norm_num)
  have r0_8 := T_relZ (m) (m : ℤ) (by omega) 7 8 6 (by norm_num) (by norm_num)
  have u1 : T (m + 1) 0 = T m 0 + 2 * T m 1 := TU (m)
  have v1 : T (m + 1) 1 = T m 0 + T m 1 + T m 2 := TV (m)
  have r1_2 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r1_3 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have r1_4 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 3 4 2 (by norm_num) (by norm_num)
  have r1_5 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 4 5 3 (by norm_num) (by norm_num)
  have r1_6 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 5 6 4 (by norm_num) (by norm_num)
  have r1_7 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 6 7 5 (by norm_num) (by norm_num)
  have r1_8 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 7 8 6 (by norm_num) (by norm_num)
  have u2 : T (m + 2) 0 = T (m + 1) 0 + 2 * T (m + 1) 1 := TU (m + 1)
  have v2 : T (m + 2) 1 = T (m + 1) 0 + T (m + 1) 1 + T (m + 1) 2 := TV (m + 1)
  have r2_2 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r2_3 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have r2_4 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 3 4 2 (by norm_num) (by norm_num)
  have r2_5 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 4 5 3 (by norm_num) (by norm_num)
  have r2_6 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 5 6 4 (by norm_num) (by norm_num)
  have r2_7 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 6 7 5 (by norm_num) (by norm_num)
  have r2_8 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 7 8 6 (by norm_num) (by norm_num)
  have u3 : T (m + 3) 0 = T (m + 2) 0 + 2 * T (m + 2) 1 := TU (m + 2)
  have v3 : T (m + 3) 1 = T (m + 2) 0 + T (m + 2) 1 + T (m + 2) 2 := TV (m + 2)
  have r3_2 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r3_3 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have r3_4 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 3 4 2 (by norm_num) (by norm_num)
  have r3_5 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 4 5 3 (by norm_num) (by norm_num)
  have r3_6 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 5 6 4 (by norm_num) (by norm_num)
  have r3_7 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 6 7 5 (by norm_num) (by norm_num)
  have r3_8 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 7 8 6 (by norm_num) (by norm_num)
  have u4 : T (m + 4) 0 = T (m + 3) 0 + 2 * T (m + 3) 1 := TU (m + 3)
  have v4 : T (m + 4) 1 = T (m + 3) 0 + T (m + 3) 1 + T (m + 3) 2 := TV (m + 3)
  have r4_2 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r4_3 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have r4_4 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 3 4 2 (by norm_num) (by norm_num)
  have r4_5 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 4 5 3 (by norm_num) (by norm_num)
  have r4_6 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 5 6 4 (by norm_num) (by norm_num)
  have r4_7 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 6 7 5 (by norm_num) (by norm_num)
  have r4_8 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 7 8 6 (by norm_num) (by norm_num)
  push_cast
  have hD : (1 * ((m : ℤ) + 3) * ((m : ℤ) + 4) * ((m : ℤ) + 5) * ((m : ℤ) + 6) * ((m : ℤ) + 7) * ((m : ℤ) + 8) * ((m : ℤ) + 9) * ((m : ℤ) + 10) * ((m : ℤ) + 11) : ℤ) ≠ 0 := by positivity
  refine (mul_eq_zero.mp ?_).resolve_left hD
  linear_combination (59875200 + 96610320 * (m : ℤ) + 74239080 * (m : ℤ) ^ 2 + 36247980 * (m : ℤ) ^ 3 + 12015630 * (m : ℤ) ^ 4 + 2787660 * (m : ℤ) ^ 5 + 445140 * (m : ℤ) ^ 6 + 45180 * (m : ℤ) ^ 7 + 2550 * (m : ℤ) ^ 8 + 60 * (m : ℤ) ^ 9) * r0_2
      + (-49896000 - 113198400 * (m : ℤ) - 93994080 * (m : ℤ) ^ 2 - 37626720 * (m : ℤ) ^ 3 - 7375140 * (m : ℤ) ^ 4 - 318420 * (m : ℤ) ^ 5 + 149400 * (m : ℤ) ^ 6 + 29880 * (m : ℤ) ^ 7 + 2220 * (m : ℤ) ^ 8 + 60 * (m : ℤ) ^ 9) * r0_3
      + (44906400 + 113390280 * (m : ℤ) + 111189924 * (m : ℤ) ^ 2 + 57194526 * (m : ℤ) ^ 3 + 17444793 * (m : ℤ) ^ 4 + 3316824 * (m : ℤ) ^ 5 + 382239 * (m : ℤ) ^ 6 + 21654 * (m : ℤ) ^ 7 - 153 * (m : ℤ) ^ 8 - 84 * (m : ℤ) ^ 9 - 3 * (m : ℤ) ^ 10) * r0_4
      + (4989600 + 18103320 * (m : ℤ) + 26571396 * (m : ℤ) ^ 2 + 20620686 * (m : ℤ) ^ 3 + 9346149 * (m : ℤ) ^ 4 + 2575359 * (m : ℤ) ^ 5 + 432954 * (m : ℤ) ^ 6 + 42984 * (m : ℤ) ^ 7 + 2301 * (m : ℤ) ^ 8 + 51 * (m : ℤ) ^ 9) * r0_5
      + (-19958400 - 57301920 * (m : ℤ) - 67245888 * (m : ℤ) ^ 2 - 43480608 * (m : ℤ) ^ 3 - 17462928 * (m : ℤ) ^ 4 - 4614462 * (m : ℤ) ^ 5 - 819846 * (m : ℤ) ^ 6 - 97092 * (m : ℤ) ^ 7 - 7332 * (m : ℤ) ^ 8 - 318 * (m : ℤ) ^ 9 - 6 * (m : ℤ) ^ 10) * r0_6
      + (14968800 + 41194440 * (m : ℤ) + 45292716 * (m : ℤ) ^ 2 + 26604186 * (m : ℤ) ^ 3 + 9313479 * (m : ℤ) ^ 4 + 2032569 * (m : ℤ) ^ 5 + 278334 * (m : ℤ) ^ 6 + 23184 * (m : ℤ) ^ 7 + 1071 * (m : ℤ) ^ 8 + 21 * (m : ℤ) ^ 9) * r0_7
      + (-14968800 - 43332840 * (m : ℤ) - 51177636 * (m : ℤ) ^ 2 - 33074574 * (m : ℤ) ^ 3 - 13114077 * (m : ℤ) ^ 4 - 3363066 * (m : ℤ) ^ 5 - 568701 * (m : ℤ) ^ 6 - 62946 * (m : ℤ) ^ 7 - 4383 * (m : ℤ) ^ 8 - 174 * (m : ℤ) ^ 9 - 3 * (m : ℤ) ^ 10) * r0_8
      + (9979200 + 93183120 * (m : ℤ) + 190053720 * (m : ℤ) ^ 2 + 166854420 * (m : ℤ) ^ 3 + 78515190 * (m : ℤ) ^ 4 + 21860010 * (m : ℤ) ^ 5 + 3700620 * (m : ℤ) ^ 6 + 370800 * (m : ℤ) ^ 7 + 20070 * (m : ℤ) ^ 8 + 450 * (m : ℤ) ^ 9) * u1
      + (-9979200 - 153058320 * (m : ℤ) - 286664040 * (m : ℤ) ^ 2 - 241093500 * (m : ℤ) ^ 3 - 114763170 * (m : ℤ) ^ 4 - 33875640 * (m : ℤ) ^ 5 - 6488280 * (m : ℤ) ^ 6 - 815940 * (m : ℤ) ^ 7 - 65250 * (m : ℤ) ^ 8 - 3000 * (m : ℤ) ^ 9 - 60 * (m : ℤ) ^ 10) * v1
      + (-191030400 - 251814240 * (m : ℤ) - 138798720 * (m : ℤ) ^ 2 - 45256560 * (m : ℤ) ^ 3 - 10861980 * (m : ℤ) ^ 4 - 2213760 * (m : ℤ) ^ 5 - 361860 * (m : ℤ) ^ 6 - 39540 * (m : ℤ) ^ 7 - 2400 * (m : ℤ) ^ 8 - 60 * (m : ℤ) ^ 9) * r1_2
      + (209880000 + 324448800 * (m : ℤ) + 196866880 * (m : ℤ) ^ 2 + 57461480 * (m : ℤ) ^ 3 + 6392940 * (m : ℤ) ^ 4 - 848400 * (m : ℤ) ^ 5 - 373560 * (m : ℤ) ^ 6 - 50760 * (m : ℤ) ^ 7 - 3220 * (m : ℤ) ^ 8 - 80 * (m : ℤ) ^ 9) * r1_3
      + (-241560000 - 432519600 * (m : ℤ) - 326579600 * (m : ℤ) ^ 2 - 137240064 * (m : ℤ) ^ 3 - 35412664 * (m : ℤ) ^ 4 - 5746749 * (m : ℤ) ^ 5 - 555174 * (m : ℤ) ^ 6 - 23556 * (m : ℤ) ^ 7 + 794 * (m : ℤ) ^ 8 + 129 * (m : ℤ) ^ 9 + 4 * (m : ℤ) ^ 10) * r1_4
      + (-57420000 - 133768200 * (m : ℤ) - 132972860 * (m : ℤ) ^ 2 - 73982734 * (m : ℤ) ^ 3 - 25388991 * (m : ℤ) ^ 4 - 5574042 * (m : ℤ) ^ 5 - 782940 * (m : ℤ) ^ 6 - 67836 * (m : ℤ) ^ 7 - 3289 * (m : ℤ) ^ 8 - 68 * (m : ℤ) ^ 9) * r1_5
      + (146520000 + 303469200 * (m : ℤ) + 273665560 * (m : ℤ) ^ 2 + 142344724 * (m : ℤ) ^ 3 + 47540254 * (m : ℤ) ^ 4 + 10698282 * (m : ℤ) ^ 5 + 1647852 * (m : ℤ) ^ 6 + 171816 * (m : ℤ) ^ 7 + 11606 * (m : ℤ) ^ 8 + 458 * (m : ℤ) ^ 9 + 8 * (m : ℤ) ^ 10) * r1_6
      + (-97020000 - 188584200 * (m : ℤ) - 156326660 * (m : ℤ) ^ 2 - 72795254 * (m : ℤ) ^ 3 - 21044961 * (m : ℤ) ^ 4 - 3925782 * (m : ℤ) ^ 5 - 473340 * (m : ℤ) ^ 6 - 35616 * (m : ℤ) ^ 7 - 1519 * (m : ℤ) ^ 8 - 28 * (m : ℤ) ^ 9) * r1_7
      + (110880000 + 229384800 * (m : ℤ) + 205599640 * (m : ℤ) ^ 2 + 105526956 * (m : ℤ) ^ 3 + 34450706 * (m : ℤ) ^ 4 + 7493031 * (m : ℤ) ^ 5 + 1101786 * (m : ℤ) ^ 6 + 108324 * (m : ℤ) ^ 7 + 6824 * (m : ℤ) ^ 8 + 249 * (m : ℤ) ^ 9 + 4 * (m : ℤ) ^ 10) * r1_8
      + (-402019200 - 1150780320 * (m : ℤ) - 1330578240 * (m : ℤ) ^ 2 - 834126640 * (m : ℤ) ^ 3 - 317720360 * (m : ℤ) ^ 4 - 77418090 * (m : ℤ) ^ 5 - 12277980 * (m : ℤ) ^ 6 - 1254120 * (m : ℤ) ^ 7 - 78900 * (m : ℤ) ^ 8 - 2750 * (m : ℤ) ^ 9 - 40 * (m : ℤ) ^ 10) * u2
      + (603028800 + 1686808080 * (m : ℤ) + 1911244920 * (m : ℤ) ^ 2 + 1185036340 * (m : ℤ) ^ 3 + 452354090 * (m : ℤ) ^ 4 + 112353840 * (m : ℤ) ^ 5 + 18554220 * (m : ℤ) ^ 6 + 2026320 * (m : ℤ) ^ 7 + 140910 * (m : ℤ) ^ 8 + 5660 * (m : ℤ) ^ 9 + 100 * (m : ℤ) ^ 10) * v2
      + (-52557120 - 286357680 * (m : ℤ) - 338361600 * (m : ℤ) ^ 2 - 187857140 * (m : ℤ) ^ 3 - 59745780 * (m : ℤ) ^ 4 - 11765700 * (m : ℤ) ^ 5 - 1470240 * (m : ℤ) ^ 6 - 114420 * (m : ℤ) ^ 7 - 5100 * (m : ℤ) ^ 8 - 100 * (m : ℤ) ^ 9) * r2_2
      + (-95800320 - 72576000 * (m : ℤ) - 7342560 * (m : ℤ) ^ 2 + 7718280 * (m : ℤ) ^ 3 + 2600860 * (m : ℤ) ^ 4 + 124640 * (m : ℤ) ^ 5 - 76640 * (m : ℤ) ^ 6 - 16480 * (m : ℤ) ^ 7 - 1340 * (m : ℤ) ^ 8 - 40 * (m : ℤ) ^ 9) * r2_3
      + (142369920 + 146475504 * (m : ℤ) + 48302724 * (m : ℤ) ^ 2 - 406176 * (m : ℤ) ^ 3 - 4477417 * (m : ℤ) ^ 4 - 1331047 * (m : ℤ) ^ 5 - 183356 * (m : ℤ) ^ 6 - 11134 * (m : ℤ) ^ 7 + 127 * (m : ℤ) ^ 8 + 53 * (m : ℤ) ^ 9 + 2 * (m : ℤ) ^ 10) * r2_4
      + (51891840 + 71145648 * (m : ℤ) + 35526276 * (m : ℤ) ^ 2 + 5495964 * (m : ℤ) ^ 3 - 1794365 * (m : ℤ) ^ 4 - 1025284 * (m : ℤ) ^ 5 - 216656 * (m : ℤ) ^ 6 - 24214 * (m : ℤ) ^ 7 - 1415 * (m : ℤ) ^ 8 - 34 * (m : ℤ) ^ 9) * r2_5
      + (-111767040 - 141619968 * (m : ℤ) - 66592512 * (m : ℤ) ^ 2 - 10096680 * (m : ℤ) ^ 3 + 3075792 * (m : ℤ) ^ 4 + 1851602 * (m : ℤ) ^ 5 + 430048 * (m : ℤ) ^ 6 + 57320 * (m : ℤ) ^ 7 + 4588 * (m : ℤ) ^ 8 + 206 * (m : ℤ) ^ 9 + 4 * (m : ℤ) ^ 10) * r2_6
      + (65197440 + 74461968 * (m : ℤ) + 29198316 * (m : ℤ) ^ 2 + 1894564 * (m : ℤ) ^ 3 - 2139935 * (m : ℤ) ^ 4 - 808864 * (m : ℤ) ^ 5 - 139076 * (m : ℤ) ^ 6 - 13174 * (m : ℤ) ^ 7 - 665 * (m : ℤ) ^ 8 - 14 * (m : ℤ) ^ 9) * r2_7
      + (-83825280 - 105050736 * (m : ℤ) - 48178116 * (m : ℤ) ^ 2 - 6607056 * (m : ℤ) ^ 3 + 2480693 * (m : ℤ) ^ 4 + 1345673 * (m : ℤ) ^ 5 + 294364 * (m : ℤ) ^ 6 + 36806 * (m : ℤ) ^ 7 + 2737 * (m : ℤ) ^ 8 + 113 * (m : ℤ) ^ 9 + 2 * (m : ℤ) ^ 10) * r2_8
      + (943176960 + 2094334560 * (m : ℤ) + 2020299240 * (m : ℤ) ^ 2 + 1116854240 * (m : ℤ) ^ 3 + 392660830 * (m : ℤ) ^ 4 + 92003550 * (m : ℤ) ^ 5 + 14607780 * (m : ℤ) ^ 6 + 1560060 * (m : ℤ) ^ 7 + 107910 * (m : ℤ) ^ 8 + 4390 * (m : ℤ) ^ 9 + 80 * (m : ℤ) ^ 10) * u3
      + (-1240081920 - 2619842400 * (m : ℤ) - 2387796600 * (m : ℤ) ^ 2 - 1236905000 * (m : ℤ) ^ 3 - 403032490 * (m : ℤ) ^ 4 - 86144460 * (m : ℤ) ^ 5 - 12179580 * (m : ℤ) ^ 6 - 1115100 * (m : ℤ) ^ 7 - 62190 * (m : ℤ) ^ 8 - 1840 * (m : ℤ) ^ 9 - 20 * (m : ℤ) ^ 10) * v3
      + (399064320 + 765746880 * (m : ℤ) + 626811200 * (m : ℤ) ^ 2 + 288920200 * (m : ℤ) ^ 3 + 83134860 * (m : ℤ) ^ 4 + 15587520 * (m : ℤ) ^ 5 + 1918260 * (m : ℤ) ^ 6 + 150540 * (m : ℤ) ^ 7 + 6880 * (m : ℤ) ^ 8 + 140 * (m : ℤ) ^ 9) * r3_2
      + (-92707200 - 140540640 * (m : ℤ) - 78004640 * (m : ℤ) ^ 2 - 15725360 * (m : ℤ) ^ 3 + 2254620 * (m : ℤ) ^ 4 + 1878600 * (m : ℤ) ^ 5 + 432000 * (m : ℤ) ^ 6 + 51000 * (m : ℤ) ^ 7 + 3140 * (m : ℤ) ^ 8 + 80 * (m : ℤ) ^ 9) * r3_3
      + (185414400 + 342069120 * (m : ℤ) + 265778688 * (m : ℤ) ^ 2 + 114140548 * (m : ℤ) ^ 3 + 29683192 * (m : ℤ) ^ 4 + 4746123 * (m : ℤ) ^ 5 + 433356 * (m : ℤ) ^ 6 + 14262 * (m : ℤ) ^ 7 - 1152 * (m : ℤ) ^ 8 - 133 * (m : ℤ) ^ 9 - 4 * (m : ℤ) ^ 10) * r3_4
      + (90256320 + 188767584 * (m : ℤ) + 170064844 * (m : ℤ) ^ 2 + 86851936 * (m : ℤ) ^ 3 + 27764589 * (m : ℤ) ^ 4 + 5770668 * (m : ℤ) ^ 5 + 780786 * (m : ℤ) ^ 6 + 66384 * (m : ℤ) ^ 7 + 3221 * (m : ℤ) ^ 8 + 68 * (m : ℤ) ^ 9) * r3_5
      + (-182004480 - 374105376 * (m : ℤ) - 333611896 * (m : ℤ) ^ 2 - 170834240 * (m : ℤ) ^ 3 - 55889098 * (m : ℤ) ^ 4 - 12258498 * (m : ℤ) ^ 5 - 1832796 * (m : ℤ) ^ 6 - 185100 * (m : ℤ) ^ 7 - 12122 * (m : ℤ) ^ 8 - 466 * (m : ℤ) ^ 9 - 8 * (m : ℤ) ^ 10) * r3_6
      + (93985920 + 182057904 * (m : ℤ) + 150415524 * (m : ℤ) ^ 2 + 69853196 * (m : ℤ) ^ 3 + 20165019 * (m : ℤ) ^ 4 + 3763788 * (m : ℤ) ^ 5 + 455406 * (m : ℤ) ^ 6 + 34524 * (m : ℤ) ^ 7 + 1491 * (m : ℤ) ^ 8 + 28 * (m : ℤ) ^ 9) * r3_7
      + (-134265600 - 273509280 * (m : ℤ) - 240887592 * (m : ℤ) ^ 2 - 121278212 * (m : ℤ) ^ 3 - 38786198 * (m : ℤ) ^ 4 - 8257557 * (m : ℤ) ^ 5 - 1188264 * (m : ℤ) ^ 6 - 114378 * (m : ℤ) ^ 7 - 7062 * (m : ℤ) ^ 8 - 253 * (m : ℤ) ^ 9 - 4 * (m : ℤ) ^ 10) * r3_8
      + (-401587200 - 878336640 * (m : ℤ) - 838554240 * (m : ℤ) ^ 2 - 461811880 * (m : ℤ) ^ 3 - 163017560 * (m : ℤ) ^ 4 - 38674890 * (m : ℤ) ^ 5 - 6269400 * (m : ℤ) ^ 6 - 688740 * (m : ℤ) ^ 7 - 49320 * (m : ℤ) ^ 8 - 2090 * (m : ℤ) ^ 9 - 40 * (m : ℤ) ^ 10) * u4
      + (147571200 + 276366240 * (m : ℤ) + 212673000 * (m : ℤ) ^ 2 + 85094320 * (m : ℤ) ^ 3 + 17353610 * (m : ℤ) ^ 4 + 781020 * (m : ℤ) ^ 5 - 465120 * (m : ℤ) ^ 6 - 121080 * (m : ℤ) ^ 7 - 13950 * (m : ℤ) ^ 8 - 820 * (m : ℤ) ^ 9 - 20 * (m : ℤ) ^ 10) * v4
      + (-100396800 - 194484960 * (m : ℤ) - 161017320 * (m : ℤ) ^ 2 - 75198640 * (m : ℤ) ^ 3 - 21954730 * (m : ℤ) ^ 4 - 4180040 * (m : ℤ) ^ 5 - 522340 * (m : ℤ) ^ 6 - 41600 * (m : ℤ) ^ 7 - 1930 * (m : ℤ) ^ 8 - 40 * (m : ℤ) ^ 9) * r4_2
      + (15724800 + 22052160 * (m : ℤ) + 9867840 * (m : ℤ) ^ 2 + 9280 * (m : ℤ) ^ 3 - 1536800 * (m : ℤ) ^ 4 - 620740 * (m : ℤ) ^ 5 - 122240 * (m : ℤ) ^ 6 - 13480 * (m : ℤ) ^ 7 - 800 * (m : ℤ) ^ 8 - 20 * (m : ℤ) ^ 9) * r4_3
      + (-45964800 - 84898080 * (m : ℤ) - 65918424 * (m : ℤ) ^ 2 - 28187780 * (m : ℤ) ^ 3 - 7251310 * (m : ℤ) ^ 4 - 1132605 * (m : ℤ) ^ 5 - 97827 * (m : ℤ) ^ 6 - 2370 * (m : ℤ) ^ 7 + 360 * (m : ℤ) ^ 8 + 35 * (m : ℤ) ^ 9 + (m : ℤ) ^ 10) * r4_4
      + (-27820800 - 56783520 * (m : ℤ) - 49844712 * (m : ℤ) ^ 2 - 24785828 * (m : ℤ) ^ 3 - 7716422 * (m : ℤ) ^ 4 - 1563373 * (m : ℤ) ^ 5 - 206528 * (m : ℤ) ^ 6 - 17182 * (m : ℤ) ^ 7 - 818 * (m : ℤ) ^ 8 - 17 * (m : ℤ) ^ 9) * r4_5
      + (55157760 + 112493952 * (m : ℤ) + 99332640 * (m : ℤ) ^ 2 + 50246272 * (m : ℤ) ^ 3 + 16194288 * (m : ℤ) ^ 4 + 3488968 * (m : ℤ) ^ 5 + 510818 * (m : ℤ) ^ 6 + 50368 * (m : ℤ) ^ 7 + 3212 * (m : ℤ) ^ 8 + 120 * (m : ℤ) ^ 9 + 2 * (m : ℤ) ^ 10) * r4_6
      + (-25401600 - 48998880 * (m : ℤ) - 40276152 * (m : ℤ) ^ 2 - 18590348 * (m : ℤ) ^ 3 - 5328162 * (m : ℤ) ^ 4 - 986223 * (m : ℤ) ^ 5 - 118188 * (m : ℤ) ^ 6 - 8862 * (m : ℤ) ^ 7 - 378 * (m : ℤ) ^ 8 - 7 * (m : ℤ) ^ 9) * r4_7
      + (39916800 + 80627040 * (m : ℤ) + 70290936 * (m : ℤ) ^ 2 + 34967140 * (m : ℤ) ^ 3 + 11028590 * (m : ℤ) ^ 4 + 2310945 * (m : ℤ) ^ 5 + 326613 * (m : ℤ) ^ 6 + 30810 * (m : ℤ) ^ 7 + 1860 * (m : ℤ) ^ 8 + 65 * (m : ℤ) ^ 9 + (m : ℤ) ^ 10) * r4_8
