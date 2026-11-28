import OMAStatements.S_oeis_a025181
import Mathlib

-- Credit: @hermitokatt (Lean proof with Claude Code)

/-!
Proof of R. J. Mathar's recurrences for A025181 (integer walks from 0 to 3, first step ±1).

1. Splitting an integer walk at its last step gives the recursions
   `xz (L+1) y = xz L (y-1) + xz L (y+1)` (a `±1` step) and
   `xz (L+1) y = xz L (y-1) + xz L y + xz L (y+1)` (a step in {-1, 0, 1}).
2. Hence, after the first 1 step(s) `±1`, the count is a binomially weighted sum of trinomial
   coefficients `T L d` (with `T (L+1) d = T L (d-1) + T L d + T L (d+1)`).
3. The row relation `(L+d+1) T(L,d+1) + d T(L,d) - (L-d+1) T(L,d-1) = 0` expresses all values
   through `T(m,0)` and `T(m,1)`; each recurrence, multiplied by a positive polynomial `D(m)`, is
   an explicit linear combination of these relations (checked by `linear_combination`).
-/

namespace OMA.A025181Proof

open OMA.S_oeis_a025181

/-- Integer walks on `N` positions from `h` to `y`: steps with index `≤ k` are `±1`, later steps
are in `{-1, 0, 1}`. -/
def Y (k N : ℕ) (h y : ℤ) : Set (Fin N → ℤ) :=
  {s | (∀ i : Fin N, i.val = 0 → s i = h) ∧
       (∀ i : Fin N, i.val = N - 1 → s i = y) ∧
       (∀ i j : Fin N, j.val = i.val + 1 → j.val ≤ k → |s j - s i| = 1) ∧
       (∀ i j : Fin N, j.val = i.val + 1 → k < j.val → |s j - s i| ≤ 1)}

/-- Extend a walk on `L+1` positions by a last value `y`. -/
def ext (L : ℕ) (y : ℤ) (t : Fin (L + 1) → ℤ) : Fin (L + 2) → ℤ :=
  fun i => if h : i.val < L + 1 then t ⟨i.val, h⟩ else y

theorem ext_inj (L : ℕ) (y : ℤ) : Function.Injective (ext L y) := by
  intro t t' h
  funext i
  have := congrFun h ⟨i.val, by omega⟩
  simpa [ext, i.isLt] using this

theorem stepY (k N : ℕ) (h y : ℤ) (s : Fin N → ℤ) (hs : s ∈ Y k N h y) :
    ∀ v (hv : v < N), h - v ≤ s ⟨v, hv⟩ ∧ s ⟨v, hv⟩ ≤ h + v := by
  intro v
  induction v with
  | zero => intro hv; have := hs.1 ⟨0, hv⟩ rfl; omega
  | succ v ih =>
    intro hv
    have e := ih (by omega)
    have d : |s ⟨v + 1, hv⟩ - s ⟨v, by omega⟩| ≤ 1 := by
      by_cases hk : v + 1 ≤ k
      · exact (hs.2.2.1 ⟨v, by omega⟩ ⟨v + 1, hv⟩ rfl hk).le
      · exact hs.2.2.2 ⟨v, by omega⟩ ⟨v + 1, hv⟩ rfl (show k < v + 1 by omega)
    rw [abs_le] at d
    omega

theorem Y_finite (k N : ℕ) (h y : ℤ) : (Y k N h y).Finite := by
  apply (Set.Finite.pi (t := fun _ : Fin N => Set.Icc (h - N) (h + N))
    (fun _ => Set.finite_Icc _ _)).subset
  intro s hs
  simp only [Set.mem_univ_pi, Set.mem_Icc]
  intro i
  have := stepY k N h y s hs i.val i.isLt
  simp only [Fin.eta] at this
  have hi := i.isLt
  omega

theorem Y_one (k : ℕ) (h y : ℤ) : (Y k 1 h y).ncard = if y = h then 1 else 0 := by
  split_ifs with hy
  · have : Y k 1 h y = {fun _ => h} := by
      ext s
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hs; funext i; exact hs.1 i (by have := i.isLt; omega)
      · rintro rfl
        exact ⟨fun _ _ => rfl, fun _ _ => hy.symm,
          fun i j hij _ => absurd hij (by have := j.isLt; omega),
          fun i j hij _ => absurd hij (by have := j.isLt; omega)⟩
    rw [this, Set.ncard_singleton]
  · have : Y k 1 h y = ∅ := by
      ext s
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hs
      exact hy ((hs.2.1 0 (by simp)).symm.trans (hs.1 0 rfl))
    rw [this, Set.ncard_empty]

theorem mem_Y_succ (k L : ℕ) (h y : ℤ) (s : Fin (L + 2) → ℤ) :
    s ∈ Y k (L + 2) h y ↔ ∃ z t, t ∈ Y k (L + 1) h z ∧
      (L + 1 ≤ k → |y - z| = 1) ∧ (k < L + 1 → |y - z| ≤ 1) ∧ ext L y t = s := by
  constructor
  · rintro ⟨h0, hN, h1, h2⟩
    refine ⟨s ⟨L, by omega⟩, fun i => s ⟨i.val, by omega⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro i hi; exact h0 _ hi
    · intro i hi; exact congrArg s (Fin.ext (by simp at hi ⊢; omega))
    · intro i j hij hj; exact h1 _ _ hij hj
    · intro i j hij hj; exact h2 _ _ hij hj
    · intro hk
      have e := h1 ⟨L, by omega⟩ ⟨L + 1, by omega⟩ rfl hk
      rwa [hN ⟨L + 1, by omega⟩ (by simp)] at e
    · intro hk
      have e := h2 ⟨L, by omega⟩ ⟨L + 1, by omega⟩ rfl hk
      rwa [hN ⟨L + 1, by omega⟩ (by simp)] at e
    · funext i
      by_cases hi : i.val < L + 1
      · simp [ext, hi]
      · simp only [ext, hi, dite_false]
        exact (hN i (by omega)).symm
  · rintro ⟨z, t, ⟨h0, hN, h1, h2⟩, hz1, hz2, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      simp only [ext, show i.val < L + 1 by omega, dite_true]
      exact h0 _ hi
    · intro i hi
      simp only [ext, show ¬ i.val < L + 1 by omega, dite_false]
    · intro i j hij hj
      by_cases hjl : j.val < L + 1
      · simp only [ext, hjl, show i.val < L + 1 by omega, dite_true]
        exact h1 ⟨i.val, by omega⟩ ⟨j.val, hjl⟩ hij hj
      · simp only [ext, hjl, show i.val < L + 1 by omega, dite_true, dite_false]
        rw [hN ⟨i.val, by omega⟩ (by simp; omega)]
        exact hz1 (by omega)
    · intro i j hij hj
      by_cases hjl : j.val < L + 1
      · simp only [ext, hjl, show i.val < L + 1 by omega, dite_true]
        exact h2 ⟨i.val, by omega⟩ ⟨j.val, hjl⟩ hij hj
      · simp only [ext, hjl, show i.val < L + 1 by omega, dite_true, dite_false]
        rw [hN ⟨i.val, by omega⟩ (by simp; omega)]
        exact hz2 (by omega)

theorem Y_M (k L : ℕ) (hk : k < L + 1) (h y : ℤ) :
    Y k (L + 2) h y = ext L y '' Y k (L + 1) h (y - 1) ∪ ext L y '' Y k (L + 1) h y ∪
      ext L y '' Y k (L + 1) h (y + 1) := by
  ext s
  rw [mem_Y_succ]
  constructor
  · rintro ⟨z, t, ht, -, hz, rfl⟩
    have : z = y - 1 ∨ z = y ∨ z = y + 1 := by
      have := hz hk; rw [abs_le] at this; omega
    rcases this with rfl | rfl | rfl
    · exact Or.inl (Or.inl ⟨t, ht, rfl⟩)
    · exact Or.inl (Or.inr ⟨t, ht, rfl⟩)
    · exact Or.inr ⟨t, ht, rfl⟩
  · rintro ((⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩)
    · exact ⟨y - 1, t, ht, fun h' => absurd h' (by omega), fun _ => by rw [abs_le]; omega, rfl⟩
    · exact ⟨y, t, ht, fun h' => absurd h' (by omega), fun _ => by rw [abs_le]; omega, rfl⟩
    · exact ⟨y + 1, t, ht, fun h' => absurd h' (by omega), fun _ => by rw [abs_le]; omega, rfl⟩

theorem Y_P (k L : ℕ) (hk : L + 1 ≤ k) (h y : ℤ) :
    Y k (L + 2) h y = ext L y '' Y k (L + 1) h (y - 1) ∪ ext L y '' Y k (L + 1) h (y + 1) := by
  ext s
  rw [mem_Y_succ]
  constructor
  · rintro ⟨z, t, ht, hz, -, rfl⟩
    have : z = y - 1 ∨ z = y + 1 := by
      have := hz hk; rw [abs_eq zero_le_one] at this; omega
    rcases this with rfl | rfl
    · exact Or.inl ⟨t, ht, rfl⟩
    · exact Or.inr ⟨t, ht, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨y - 1, t, ht, fun _ => by rw [abs_eq zero_le_one]; omega,
        fun h' => absurd h' (by omega), rfl⟩
    · exact ⟨y + 1, t, ht, fun _ => by rw [abs_eq zero_le_one]; omega,
        fun h' => absurd h' (by omega), rfl⟩

theorem disjY (k L : ℕ) (h y z w : ℤ) (hzw : z ≠ w) :
    Disjoint (ext L y '' Y k (L + 1) h z) (ext L y '' Y k (L + 1) h w) := by
  rw [Set.disjoint_left]
  rintro s ⟨t, ht, rfl⟩ ⟨t', ht', e⟩
  have e1 := congrFun e ⟨L, by omega⟩
  simp only [ext, show L < L + 1 by omega, dite_true] at e1
  rw [ht.2.1 ⟨L, by omega⟩ (by simp), ht'.2.1 ⟨L, by omega⟩ (by simp)] at e1
  exact hzw e1.symm

/-- `xz k L h y`: the number of integer walks of length `L` from `h` to `y`. -/
noncomputable def xz (k L : ℕ) (h y : ℤ) : ℕ := (Y k (L + 1) h y).ncard

theorem zlen0 (k : ℕ) (h y : ℤ) : xz k 0 h y = if y = h then 1 else 0 := Y_one k h y

theorem zM (k L : ℕ) (hk : k < L + 1) (h y : ℤ) :
    xz k (L + 1) h y = xz k L h (y - 1) + xz k L h y + xz k L h (y + 1) := by
  unfold xz
  have fA := (Y_finite k (L + 1) h (y - 1)).image (ext L y)
  have fB := (Y_finite k (L + 1) h y).image (ext L y)
  have fC := (Y_finite k (L + 1) h (y + 1)).image (ext L y)
  have dAB := disjY k L h y (y - 1) y (by omega)
  have dAC := disjY k L h y (y - 1) (y + 1) (by omega)
  have dBC := disjY k L h y y (y + 1) (by omega)
  rw [Y_M k L hk h y,
    Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨dAC, dBC⟩) (fA.union fB) fC,
    Set.ncard_union_eq dAB fA fB, Set.ncard_image_of_injective _ (ext_inj _ _),
    Set.ncard_image_of_injective _ (ext_inj _ _), Set.ncard_image_of_injective _ (ext_inj _ _)]

theorem zP (k L : ℕ) (hk : L + 1 ≤ k) (h y : ℤ) :
    xz k (L + 1) h y = xz k L h (y - 1) + xz k L h (y + 1) := by
  unfold xz
  rw [Y_P k L hk h y, Set.ncard_union_eq (disjY k L h y (y - 1) (y + 1) (by omega))
    ((Y_finite _ _ _ _).image _) ((Y_finite _ _ _ _).image _),
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

theorem TU (l : ℕ) : T (l + 1) 0 = T l 0 + 2 * T l 1 := by
  rw [T_succ' l 0 (-1) 1 (by norm_num) (by norm_num), T_symm' l 1 (-1) (by norm_num)]; ring

theorem TV (l : ℕ) : T (l + 1) 1 = T l 0 + T l 1 + T l 2 :=
  T_succ' l 1 0 2 (by norm_num) (by norm_num)

theorem T_relZ (l : ℕ) (L : ℤ) (hL : L = l) (c d e : ℤ) (hd : d = c + 1) (he : e = c - 1) :
    (L + c + 1) * T l d + c * T l c - (L - c + 1) * T l e = 0 := by
  subst hL; exact T_rel' l c d e hd he

theorem Zb1 (k : ℕ) (hk : 1 ≤ k) : ∀ (y a b : ℤ), a = y - 1 → b = y + 1 →
    (xz k 1 0 y : ℤ) = T 0 a + T 0 b := by
  intro y a b ha hb
  rw [zP k 0 (by omega) 0 y, Nat.cast_add, zlen0, zlen0, T_zero, T_zero]
  split_ifs <;> omega

/-- After the first step `±1`, the walks grow like trinomial rows. -/
theorem ZK (L : ℕ) : ∀ (y a b : ℤ), a = y - 1 → b = y + 1 →
    (xz 1 (L + 1) 0 y : ℤ) = T L a + T L b := by
  induction L with
  | zero => exact Zb1 1 le_rfl
  | succ L ih =>
    intro y a b ha hb
    rw [zM 1 (L + 1) (by omega) 0 y, Nat.cast_add, Nat.cast_add,
      ih (y - 1) (a - 1) (b - 1) (by omega) (by omega), ih y a b ha hb,
      ih (y + 1) (a + 1) (b + 1) (by omega) (by omega), T_succ L a, T_succ L b]
    ring

theorem walks_eq (n : ℕ) : walks n = Y 1 (n + 1) 0 3 := by
  ext s
  constructor
  · rintro ⟨h0, hN, h1, h2⟩
    exact ⟨h0, fun i hi => hN i (by omega), h1, h2⟩
  · rintro ⟨h0, hN, h1, h2⟩
    exact ⟨h0, fun i hi => hN i (by omega), h1, h2⟩

theorem a_closed (L : ℕ) : a (L + 1) = T L 2 + T L 4 := by
  unfold a
  rw [walks_eq]
  change ((xz 1 (L + 1) 0 3 : ℕ) : ℤ) = _
  exact ZK L 3 2 4 (by norm_num) (by norm_num)

end OMA.A025181Proof

open OMA.S_oeis_a025181 OMA.A025181Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a025181.main := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    have h0 : a (m + 6) = T (m + 5) 2 + T (m + 5) 4 := a_closed (m + 5)
    have h1 : a (m + 6 - 1) = T (m + 4) 2 + T (m + 4) 4 := by
      rw [show m + 6 - 1 = m + 4 + 1 by omega]; exact a_closed (m + 4)
    have h2 : a (m + 6 - 2) = T (m + 3) 2 + T (m + 3) 4 := by
      rw [show m + 6 - 2 = m + 3 + 1 by omega]; exact a_closed (m + 3)
    have h3 : a (m + 6 - 3) = T (m + 2) 2 + T (m + 2) 4 := by
      rw [show m + 6 - 3 = m + 2 + 1 by omega]; exact a_closed (m + 2)
    have h4 : a (m + 6 - 4) = T (m + 1) 2 + T (m + 1) 4 := by
      rw [show m + 6 - 4 = m + 1 + 1 by omega]; exact a_closed (m + 1)
    have h5 : a (m + 6 - 5) = T m 2 + T m 4 := by
      rw [show m + 6 - 5 = m + 1 by omega]; exact a_closed (m)
    rw [h0, h1, h2, h3, h4, h5]
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
    have u5 : T (m + 5) 0 = T (m + 4) 0 + 2 * T (m + 4) 1 := TU (m + 4)
    have v5 : T (m + 5) 1 = T (m + 4) 0 + T (m + 4) 1 + T (m + 4) 2 := TV (m + 4)
    have r5_2 := T_relZ (m + 5) ((m : ℤ) + 5) (by omega) 1 2 0 (by norm_num) (by norm_num)
    have r5_3 := T_relZ (m + 5) ((m : ℤ) + 5) (by omega) 2 3 1 (by norm_num) (by norm_num)
    have r5_4 := T_relZ (m + 5) ((m : ℤ) + 5) (by omega) 3 4 2 (by norm_num) (by norm_num)
    push_cast
    have hD : (1 * ((m : ℤ) + 3) * ((m : ℤ) + 4) * ((m : ℤ) + 5) * ((m : ℤ) + 6) * ((m : ℤ) + 7) * ((m : ℤ) + 8) : ℤ) ≠ 0 := by positivity
    refine (mul_eq_zero.mp ?_).resolve_left hD
    linear_combination (-50400 - 48780 * (m : ℤ) - 24910 * (m : ℤ) ^ 2 - 7554 * (m : ℤ) ^ 3 - 1294 * (m : ℤ) ^ 4 - 114 * (m : ℤ) ^ 5 - 4 * (m : ℤ) ^ 6) * r0_2
        + (30240 + 49428 * (m : ℤ) + 23706 * (m : ℤ) ^ 2 + 4986 * (m : ℤ) ^ 3 + 486 * (m : ℤ) ^ 4 + 18 * (m : ℤ) ^ 5) * r0_3
        + (-30240 - 59508 * (m : ℤ) - 40182 * (m : ℤ) ^ 2 - 12888 * (m : ℤ) ^ 3 - 2148 * (m : ℤ) ^ 4 - 180 * (m : ℤ) ^ 5 - 6 * (m : ℤ) ^ 6) * r0_4
        + (-20160 - 79992 * (m : ℤ) - 99412 * (m : ℤ) ^ 2 - 51184 * (m : ℤ) ^ 3 - 13348 * (m : ℤ) ^ 4 - 1876 * (m : ℤ) ^ 5 - 136 * (m : ℤ) ^ 6 - 4 * (m : ℤ) ^ 7) * u1
        + (20160 + 130392 * (m : ℤ) + 148192 * (m : ℤ) ^ 2 + 76094 * (m : ℤ) ^ 3 + 20902 * (m : ℤ) ^ 4 + 3170 * (m : ℤ) ^ 5 + 250 * (m : ℤ) ^ 6 + 8 * (m : ℤ) ^ 7) * v1
        + (-10080 - 58140 * (m : ℤ) - 46166 * (m : ℤ) ^ 2 - 15714 * (m : ℤ) ^ 3 - 2714 * (m : ℤ) ^ 4 - 234 * (m : ℤ) ^ 5 - 8 * (m : ℤ) ^ 6) * r1_2
        + (12096 * (m : ℤ) + 9288 * (m : ℤ) ^ 2 + 2508 * (m : ℤ) ^ 3 + 288 * (m : ℤ) ^ 4 + 12 * (m : ℤ) ^ 5) * r1_3
        + (-16128 * (m : ℤ) - 16416 * (m : ℤ) ^ 2 - 6440 * (m : ℤ) ^ 3 - 1220 * (m : ℤ) ^ 4 - 112 * (m : ℤ) ^ 5 - 4 * (m : ℤ) ^ 6) * r1_4
        + (20160 + 84024 * (m : ℤ) + 85036 * (m : ℤ) ^ 2 + 40396 * (m : ℤ) ^ 3 + 10600 * (m : ℤ) ^ 4 + 1576 * (m : ℤ) ^ 5 + 124 * (m : ℤ) ^ 6 + 4 * (m : ℤ) ^ 7) * u2
        + (-30240 - 95796 * (m : ℤ) - 80142 * (m : ℤ) ^ 2 - 29700 * (m : ℤ) ^ 3 - 5520 * (m : ℤ) ^ 4 - 504 * (m : ℤ) ^ 5 - 18 * (m : ℤ) ^ 6) * v2
        + (153216 + 186360 * (m : ℤ) + 94413 * (m : ℤ) ^ 2 + 25517 * (m : ℤ) ^ 3 + 3857 * (m : ℤ) ^ 4 + 307 * (m : ℤ) ^ 5 + 10 * (m : ℤ) ^ 6) * r2_2
        + (-118944 - 123420 * (m : ℤ) - 49497 * (m : ℤ) ^ 2 - 9603 * (m : ℤ) ^ 3 - 903 * (m : ℤ) ^ 4 - 33 * (m : ℤ) ^ 5) * r2_3
        + (198240 + 245348 * (m : ℤ) + 123635 * (m : ℤ) ^ 2 + 32504 * (m : ℤ) ^ 3 + 4706 * (m : ℤ) ^ 4 + 356 * (m : ℤ) ^ 5 + 11 * (m : ℤ) ^ 6) * r2_4
        + (528192 + 774840 * (m : ℤ) + 477338 * (m : ℤ) ^ 2 + 159968 * (m : ℤ) ^ 3 + 31474 * (m : ℤ) ^ 4 + 3634 * (m : ℤ) ^ 5 + 228 * (m : ℤ) ^ 6 + 6 * (m : ℤ) ^ 7) * u3
        + (-814464 - 1216752 * (m : ℤ) - 767488 * (m : ℤ) ^ 2 - 265019 * (m : ℤ) ^ 3 - 54105 * (m : ℤ) ^ 4 - 6529 * (m : ℤ) ^ 5 - 431 * (m : ℤ) ^ 6 - 12 * (m : ℤ) ^ 7) * v3
        + (177024 + 218704 * (m : ℤ) + 110076 * (m : ℤ) ^ 2 + 28944 * (m : ℤ) ^ 3 + 4202 * (m : ℤ) ^ 4 + 320 * (m : ℤ) ^ 5 + 10 * (m : ℤ) ^ 6) * r3_2
        + (-15840 - 18708 * (m : ℤ) - 8643 * (m : ℤ) ^ 2 - 1947 * (m : ℤ) ^ 3 - 213 * (m : ℤ) ^ 4 - 9 * (m : ℤ) ^ 5) * r3_3
        + (31680 + 42696 * (m : ℤ) + 23522 * (m : ℤ) ^ 2 + 6775 * (m : ℤ) ^ 3 + 1075 * (m : ℤ) ^ 4 + 89 * (m : ℤ) ^ 5 + 3 * (m : ℤ) ^ 6) * r3_4
        + (-602880 - 886496 * (m : ℤ) - 549824 * (m : ℤ) ^ 2 - 186598 * (m : ℤ) ^ 3 - 37454 * (m : ℤ) ^ 4 - 4450 * (m : ℤ) ^ 5 - 290 * (m : ℤ) ^ 6 - 8 * (m : ℤ) ^ 7) * u4
        + (600000 + 828200 * (m : ℤ) + 478230 * (m : ℤ) ^ 2 + 149658 * (m : ℤ) ^ 3 + 27378 * (m : ℤ) ^ 4 + 2922 * (m : ℤ) ^ 5 + 168 * (m : ℤ) ^ 6 + 4 * (m : ℤ) ^ 7) * v4
        + (-179880 - 220646 * (m : ℤ) - 110379 * (m : ℤ) ^ 2 - 28899 * (m : ℤ) ^ 3 - 4187 * (m : ℤ) ^ 4 - 319 * (m : ℤ) ^ 5 - 10 * (m : ℤ) ^ 6) * r4_2
        + (39960 + 43362 * (m : ℤ) + 18339 * (m : ℤ) ^ 2 + 3783 * (m : ℤ) ^ 3 + 381 * (m : ℤ) ^ 4 + 15 * (m : ℤ) ^ 5) * r4_3
        + (-93240 - 114498 * (m : ℤ) - 57245 * (m : ℤ) ^ 2 - 14940 * (m : ℤ) ^ 3 - 2150 * (m : ℤ) ^ 4 - 162 * (m : ℤ) ^ 5 - 5 * (m : ℤ) ^ 6) * r4_4
        + (183600 + 261540 * (m : ℤ) + 157134 * (m : ℤ) ^ 2 + 51694 * (m : ℤ) ^ 3 + 10072 * (m : ℤ) ^ 4 + 1164 * (m : ℤ) ^ 5 + 74 * (m : ℤ) ^ 6 + 2 * (m : ℤ) ^ 7) * u5
        + (-66960 - 85572 * (m : ℤ) - 44796 * (m : ℤ) ^ 2 - 12317 * (m : ℤ) ^ 3 - 1879 * (m : ℤ) ^ 4 - 151 * (m : ℤ) ^ 5 - 5 * (m : ℤ) ^ 6) * v5
        + (36720 + 44964 * (m : ℤ) + 22434 * (m : ℤ) ^ 2 + 5852 * (m : ℤ) ^ 3 + 844 * (m : ℤ) ^ 4 + 64 * (m : ℤ) ^ 5 + 2 * (m : ℤ) ^ 6) * r5_2
        + (-7560 - 8262 * (m : ℤ) - 3525 * (m : ℤ) ^ 2 - 735 * (m : ℤ) ^ 3 - 75 * (m : ℤ) ^ 4 - 3 * (m : ℤ) ^ 5) * r5_3
        + (20160 + 24552 * (m : ℤ) + 12154 * (m : ℤ) ^ 2 + 3135 * (m : ℤ) ^ 3 + 445 * (m : ℤ) ^ 4 + 33 * (m : ℤ) ^ 5 + (m : ℤ) ^ 6) * r5_4
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have h0 : a (m + 3) = T (m + 2) 2 + T (m + 2) 4 := a_closed (m + 2)
    have h1 : a (m + 3 - 1) = T (m + 1) 2 + T (m + 1) 4 := by
      rw [show m + 3 - 1 = m + 1 + 1 by omega]; exact a_closed (m + 1)
    have h2 : a (m + 3 - 2) = T m 2 + T m 4 := by
      rw [show m + 3 - 2 = m + 1 by omega]; exact a_closed (m)
    rw [h0, h1, h2]
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
    push_cast
    have hD : (1 * ((m : ℤ) + 3) * ((m : ℤ) + 4) * ((m : ℤ) + 5) : ℤ) ≠ 0 := by positivity
    refine (mul_eq_zero.mp ?_).resolve_left hD
    linear_combination (4950 + 8115 * (m : ℤ) + 6010 * (m : ℤ) ^ 2 + 2647 * (m : ℤ) ^ 3 + 726 * (m : ℤ) ^ 4 + 116 * (m : ℤ) ^ 5 + 8 * (m : ℤ) ^ 6) * r0_2
        + (-2970 - 6849 * (m : ℤ) - 5796 * (m : ℤ) ^ 2 - 2349 * (m : ℤ) ^ 3 - 468 * (m : ℤ) ^ 4 - 36 * (m : ℤ) ^ 5) * r0_3
        + (2970 + 7839 * (m : ℤ) + 8079 * (m : ℤ) ^ 2 + 4281 * (m : ℤ) ^ 3 + 1251 * (m : ℤ) ^ 4 + 192 * (m : ℤ) ^ 5 + 12 * (m : ℤ) ^ 6) * r0_4
        + (1980 + 9186 * (m : ℤ) + 15178 * (m : ℤ) ^ 2 + 12104 * (m : ℤ) ^ 3 + 5254 * (m : ℤ) ^ 4 + 1274 * (m : ℤ) ^ 5 + 160 * (m : ℤ) ^ 6 + 8 * (m : ℤ) ^ 7) * u1
        + (-1980 - 14136 * (m : ℤ) - 23293 * (m : ℤ) ^ 2 - 18114 * (m : ℤ) ^ 3 - 7901 * (m : ℤ) ^ 4 - 2000 * (m : ℤ) ^ 5 - 276 * (m : ℤ) ^ 6 - 16 * (m : ℤ) ^ 7) * v1
        + (1980 + 8430 * (m : ℤ) + 9907 * (m : ℤ) ^ 2 + 5499 * (m : ℤ) ^ 3 + 1636 * (m : ℤ) ^ 4 + 252 * (m : ℤ) ^ 5 + 16 * (m : ℤ) ^ 6) * r1_2
        + (-810 - 2943 * (m : ℤ) - 2961 * (m : ℤ) ^ 2 - 1302 * (m : ℤ) ^ 3 - 276 * (m : ℤ) ^ 4 - 24 * (m : ℤ) ^ 5) * r1_3
        + (1080 + 4194 * (m : ℤ) + 4929 * (m : ℤ) ^ 2 + 2723 * (m : ℤ) ^ 3 + 802 * (m : ℤ) ^ 4 + 124 * (m : ℤ) ^ 5 + 8 * (m : ℤ) ^ 6) * r1_4
        + (-3672 * (m : ℤ) - 7284 * (m : ℤ) ^ 2 - 6352 * (m : ℤ) ^ 3 - 3082 * (m : ℤ) ^ 4 - 858 * (m : ℤ) ^ 5 - 128 * (m : ℤ) ^ 6 - 8 * (m : ℤ) ^ 7) * u2
        + (2448 * (m : ℤ) + 4125 * (m : ℤ) ^ 2 + 3050 * (m : ℤ) ^ 3 + 1201 * (m : ℤ) ^ 4 + 244 * (m : ℤ) ^ 5 + 20 * (m : ℤ) ^ 6) * v2
        + (-1836 * (m : ℤ) - 2724 * (m : ℤ) ^ 2 - 1814 * (m : ℤ) ^ 3 - 634 * (m : ℤ) ^ 4 - 112 * (m : ℤ) ^ 5 - 8 * (m : ℤ) ^ 6) * r2_2
        + (612 * (m : ℤ) + 789 * (m : ℤ) ^ 2 + 447 * (m : ℤ) ^ 3 + 120 * (m : ℤ) ^ 4 + 12 * (m : ℤ) ^ 5) * r2_3
        + (-1020 * (m : ℤ) - 1519 * (m : ℤ) ^ 2 - 1008 * (m : ℤ) ^ 3 - 349 * (m : ℤ) ^ 4 - 60 * (m : ℤ) ^ 5 - 4 * (m : ℤ) ^ 6) * r2_4
