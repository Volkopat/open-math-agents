import OMAStatements.S_oeis_a026070
import Mathlib

-- Credit: @hermitokatt (Lean proof with Claude Code)

/-!
Proof of R. J. Mathar's recurrence for A026070 (integer walks from 0 to 3, first two steps ±1).

1. Splitting an integer walk at its last step gives the recursions
   `xz (L+1) y = xz L (y-1) + xz L (y+1)` (a `±1` step) and
   `xz (L+1) y = xz L (y-1) + xz L y + xz L (y+1)` (a step in {-1, 0, 1}).
2. Hence, after the first 2 step(s) `±1`, the count is a binomially weighted sum of trinomial
   coefficients `T L d` (with `T (L+1) d = T L (d-1) + T L d + T L (d+1)`).
3. The row relation `(L+d+1) T(L,d+1) + d T(L,d) - (L-d+1) T(L,d-1) = 0` expresses all values
   through `T(m,0)` and `T(m,1)`; each recurrence, multiplied by a positive polynomial `D(m)`, is
   an explicit linear combination of these relations (checked by `linear_combination`).
-/

namespace OMA.A026070Proof

open OMA.S_oeis_a026070

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

theorem Zb2 (k : ℕ) (hk : 2 ≤ k) : ∀ (y a c b : ℤ), a = y - 2 → c = y → b = y + 2 →
    (xz k 2 0 y : ℤ) = T 0 a + 2 * T 0 c + T 0 b := by
  intro y a c b ha hc hb
  rw [zP k 1 (by omega) 0 y, Nat.cast_add, Zb1 k (by omega) (y - 1) a c (by omega) (by omega),
    Zb1 k (by omega) (y + 1) c b (by omega) (by omega)]
  ring

/-- After the first two steps `±1`, the walks grow like trinomial rows. -/
theorem ZK (L : ℕ) : ∀ (y a c b : ℤ), a = y - 2 → c = y → b = y + 2 →
    (xz 2 (L + 2) 0 y : ℤ) = T L a + 2 * T L c + T L b := by
  induction L with
  | zero => exact Zb2 2 le_rfl
  | succ L ih =>
    intro y a c b ha hc hb
    show (xz 2 (L + 2 + 1) 0 y : ℤ) = _
    rw [zM 2 (L + 2) (by omega) 0 y, Nat.cast_add, Nat.cast_add,
      ih (y - 1) (a - 1) (c - 1) (b - 1) (by omega) (by omega) (by omega), ih y a c b ha hc hb,
      ih (y + 1) (a + 1) (c + 1) (b + 1) (by omega) (by omega) (by omega),
      T_succ L a, T_succ L c, T_succ L b]
    ring

theorem walks_eq (n : ℕ) : walks n = Y 2 (n + 1) 0 3 := by
  ext s
  constructor
  · rintro ⟨h0, hN, h1, h2⟩
    exact ⟨h0, fun i hi => hN i (by omega), h1, h2⟩
  · rintro ⟨h0, hN, h1, h2⟩
    exact ⟨h0, fun i hi => hN i (by omega), h1, h2⟩

theorem a_closed (L : ℕ) : a (L + 2) = T L 1 + 2 * T L 3 + T L 5 := by
  unfold a
  rw [walks_eq]
  change ((xz 2 (L + 2) 0 3 : ℕ) : ℤ) = _
  exact ZK L 3 1 3 5 (by norm_num) (by norm_num) (by norm_num)

end OMA.A026070Proof

open OMA.S_oeis_a026070 OMA.A026070Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a026070.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have h0 : a (m + 7) = T (m + 5) 1 + 2 * T (m + 5) 3 + T (m + 5) 5 := a_closed (m + 5)
  have h1 : a (m + 7 - 1) = T (m + 4) 1 + 2 * T (m + 4) 3 + T (m + 4) 5 := by
    rw [show m + 7 - 1 = m + 4 + 2 by omega]; exact a_closed (m + 4)
  have h2 : a (m + 7 - 2) = T (m + 3) 1 + 2 * T (m + 3) 3 + T (m + 3) 5 := by
    rw [show m + 7 - 2 = m + 3 + 2 by omega]; exact a_closed (m + 3)
  have h3 : a (m + 7 - 3) = T (m + 2) 1 + 2 * T (m + 2) 3 + T (m + 2) 5 := by
    rw [show m + 7 - 3 = m + 2 + 2 by omega]; exact a_closed (m + 2)
  have h4 : a (m + 7 - 4) = T (m + 1) 1 + 2 * T (m + 1) 3 + T (m + 1) 5 := by
    rw [show m + 7 - 4 = m + 1 + 2 by omega]; exact a_closed (m + 1)
  have h5 : a (m + 7 - 5) = T m 1 + 2 * T m 3 + T m 5 := by
    rw [show m + 7 - 5 = m + 2 by omega]; exact a_closed (m)
  rw [h0, h1, h2, h3, h4, h5]
  have r0_2 := T_relZ (m) (m : ℤ) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r0_3 := T_relZ (m) (m : ℤ) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have r0_4 := T_relZ (m) (m : ℤ) (by omega) 3 4 2 (by norm_num) (by norm_num)
  have r0_5 := T_relZ (m) (m : ℤ) (by omega) 4 5 3 (by norm_num) (by norm_num)
  have u1 : T (m + 1) 0 = T m 0 + 2 * T m 1 := TU (m)
  have v1 : T (m + 1) 1 = T m 0 + T m 1 + T m 2 := TV (m)
  have r1_2 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r1_3 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have r1_4 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 3 4 2 (by norm_num) (by norm_num)
  have r1_5 := T_relZ (m + 1) ((m : ℤ) + 1) (by omega) 4 5 3 (by norm_num) (by norm_num)
  have u2 : T (m + 2) 0 = T (m + 1) 0 + 2 * T (m + 1) 1 := TU (m + 1)
  have v2 : T (m + 2) 1 = T (m + 1) 0 + T (m + 1) 1 + T (m + 1) 2 := TV (m + 1)
  have r2_2 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r2_3 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have r2_4 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 3 4 2 (by norm_num) (by norm_num)
  have r2_5 := T_relZ (m + 2) ((m : ℤ) + 2) (by omega) 4 5 3 (by norm_num) (by norm_num)
  have u3 : T (m + 3) 0 = T (m + 2) 0 + 2 * T (m + 2) 1 := TU (m + 2)
  have v3 : T (m + 3) 1 = T (m + 2) 0 + T (m + 2) 1 + T (m + 2) 2 := TV (m + 2)
  have r3_2 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r3_3 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have r3_4 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 3 4 2 (by norm_num) (by norm_num)
  have r3_5 := T_relZ (m + 3) ((m : ℤ) + 3) (by omega) 4 5 3 (by norm_num) (by norm_num)
  have u4 : T (m + 4) 0 = T (m + 3) 0 + 2 * T (m + 3) 1 := TU (m + 3)
  have v4 : T (m + 4) 1 = T (m + 3) 0 + T (m + 3) 1 + T (m + 3) 2 := TV (m + 3)
  have r4_2 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r4_3 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have r4_4 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 3 4 2 (by norm_num) (by norm_num)
  have r4_5 := T_relZ (m + 4) ((m : ℤ) + 4) (by omega) 4 5 3 (by norm_num) (by norm_num)
  have u5 : T (m + 5) 0 = T (m + 4) 0 + 2 * T (m + 4) 1 := TU (m + 4)
  have v5 : T (m + 5) 1 = T (m + 4) 0 + T (m + 4) 1 + T (m + 4) 2 := TV (m + 4)
  have r5_2 := T_relZ (m + 5) ((m : ℤ) + 5) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r5_3 := T_relZ (m + 5) ((m : ℤ) + 5) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have r5_4 := T_relZ (m + 5) ((m : ℤ) + 5) (by omega) 3 4 2 (by norm_num) (by norm_num)
  have r5_5 := T_relZ (m + 5) ((m : ℤ) + 5) (by omega) 4 5 3 (by norm_num) (by norm_num)
  push_cast
  have hD : (1 * ((m : ℤ) + 3) * ((m : ℤ) + 4) * ((m : ℤ) + 5) * ((m : ℤ) + 6) * ((m : ℤ) + 7) * ((m : ℤ) + 8) * ((m : ℤ) + 9) : ℤ) ≠ 0 := by positivity
  refine (mul_eq_zero.mp ?_).resolve_left hD
  linear_combination (217728 - 38448 * (m : ℤ) - 170544 * (m : ℤ) ^ 2 - 98852 * (m : ℤ) ^ 3 - 26748 * (m : ℤ) ^ 4 - 3812 * (m : ℤ) ^ 5 - 276 * (m : ℤ) ^ 6 - 8 * (m : ℤ) ^ 7) * r0_2
      + (-725760 - 1466496 * (m : ℤ) - 1063668 * (m : ℤ) ^ 2 - 398022 * (m : ℤ) ^ 3 - 84780 * (m : ℤ) ^ 4 - 10344 * (m : ℤ) ^ 5 - 672 * (m : ℤ) ^ 6 - 18 * (m : ℤ) ^ 7) * r0_3
      + (217728 + 409104 * (m : ℤ) + 255096 * (m : ℤ) ^ 2 + 73920 * (m : ℤ) ^ 3 + 10992 * (m : ℤ) ^ 4 + 816 * (m : ℤ) ^ 5 + 24 * (m : ℤ) ^ 6) * r0_4
      + (-217728 - 463536 * (m : ℤ) - 357372 * (m : ℤ) ^ 2 - 137694 * (m : ℤ) ^ 3 - 29472 * (m : ℤ) ^ 4 - 3564 * (m : ℤ) ^ 5 - 228 * (m : ℤ) ^ 6 - 6 * (m : ℤ) ^ 7) * r0_5
      + (580608 + 1973952 * (m : ℤ) + 2444232 * (m : ℤ) ^ 2 + 1442092 * (m : ℤ) ^ 3 + 472696 * (m : ℤ) ^ 4 + 91168 * (m : ℤ) ^ 5 + 10288 * (m : ℤ) ^ 6 + 628 * (m : ℤ) ^ 7 + 16 * (m : ℤ) ^ 8) * u1
      + (-580608 - 2191680 * (m : ℤ) - 2405784 * (m : ℤ) ^ 2 - 1271548 * (m : ℤ) ^ 3 - 373844 * (m : ℤ) ^ 4 - 64420 * (m : ℤ) ^ 5 - 6476 * (m : ℤ) ^ 6 - 352 * (m : ℤ) ^ 7 - 8 * (m : ℤ) ^ 8) * v1
      + (308448 + 981756 * (m : ℤ) + 769836 * (m : ℤ) ^ 2 + 280372 * (m : ℤ) ^ 3 + 55132 * (m : ℤ) ^ 4 + 6024 * (m : ℤ) ^ 5 + 344 * (m : ℤ) ^ 6 + 8 * (m : ℤ) ^ 7) * r1_2
      + (562464 + 252468 * (m : ℤ) - 131694 * (m : ℤ) ^ 2 - 122188 * (m : ℤ) ^ 3 - 36764 * (m : ℤ) ^ 4 - 5468 * (m : ℤ) ^ 5 - 406 * (m : ℤ) ^ 6 - 12 * (m : ℤ) ^ 7) * r1_3
      + (-145152 - 42912 * (m : ℤ) + 42024 * (m : ℤ) ^ 2 + 25160 * (m : ℤ) ^ 3 + 5192 * (m : ℤ) ^ 4 + 472 * (m : ℤ) ^ 5 + 16 * (m : ℤ) ^ 6) * r1_4
      + (181440 + 89928 * (m : ℤ) - 41802 * (m : ℤ) ^ 2 - 41956 * (m : ℤ) ^ 3 - 12780 * (m : ℤ) ^ 4 - 1888 * (m : ℤ) ^ 5 - 138 * (m : ℤ) ^ 6 - 4 * (m : ℤ) ^ 7) * r1_5
      + (-1632960 - 3177144 * (m : ℤ) - 2420172 * (m : ℤ) ^ 2 - 957828 * (m : ℤ) ^ 3 - 215080 * (m : ℤ) ^ 4 - 27536 * (m : ℤ) ^ 5 - 1868 * (m : ℤ) ^ 6 - 52 * (m : ℤ) ^ 7) * u2
      + (1905120 + 3860892 * (m : ℤ) + 3112812 * (m : ℤ) ^ 2 + 1349712 * (m : ℤ) ^ 3 + 352272 * (m : ℤ) ^ 4 + 57548 * (m : ℤ) ^ 5 + 5788 * (m : ℤ) ^ 6 + 328 * (m : ℤ) ^ 7 + 8 * (m : ℤ) ^ 8) * v2
      + (220320 + 536724 * (m : ℤ) + 452880 * (m : ℤ) ^ 2 + 190462 * (m : ℤ) ^ 3 + 44750 * (m : ℤ) ^ 4 + 5954 * (m : ℤ) ^ 5 + 418 * (m : ℤ) ^ 6 + 12 * (m : ℤ) ^ 7) * r2_2
      + (5365440 + 7100136 * (m : ℤ) + 3949434 * (m : ℤ) ^ 2 + 1200723 * (m : ℤ) ^ 3 + 215914 * (m : ℤ) ^ 4 + 22980 * (m : ℤ) ^ 5 + 1340 * (m : ℤ) ^ 6 + 33 * (m : ℤ) ^ 7) * r2_3
      + (-1192320 - 1405584 * (m : ℤ) - 669324 * (m : ℤ) ^ 2 - 164960 * (m : ℤ) ^ 3 - 22216 * (m : ℤ) ^ 4 - 1552 * (m : ℤ) ^ 5 - 44 * (m : ℤ) ^ 6) * r2_4
      + (1788480 + 2406456 * (m : ℤ) + 1355382 * (m : ℤ) ^ 2 + 414771 * (m : ℤ) ^ 3 + 74564 * (m : ℤ) ^ 4 + 7882 * (m : ℤ) ^ 5 + 454 * (m : ℤ) ^ 6 + 11 * (m : ℤ) ^ 7) * r2_5
      + (-13685760 - 22230720 * (m : ℤ) - 15515352 * (m : ℤ) ^ 2 - 6077130 * (m : ℤ) ^ 3 - 1461292 * (m : ℤ) ^ 4 - 220936 * (m : ℤ) ^ 5 - 20516 * (m : ℤ) ^ 6 - 1070 * (m : ℤ) ^ 7 - 24 * (m : ℤ) ^ 8) * u3
      + (11612160 + 17759808 * (m : ℤ) + 11652696 * (m : ℤ) ^ 2 + 4285498 * (m : ℤ) ^ 3 + 966250 * (m : ℤ) ^ 4 + 136742 * (m : ℤ) ^ 5 + 11858 * (m : ℤ) ^ 6 + 576 * (m : ℤ) ^ 7 + 12 * (m : ℤ) ^ 8) * v3
      + (-3108240 - 4131444 * (m : ℤ) - 2291740 * (m : ℤ) ^ 2 - 688190 * (m : ℤ) ^ 3 - 120866 * (m : ℤ) ^ 4 - 12414 * (m : ℤ) ^ 5 - 690 * (m : ℤ) ^ 6 - 16 * (m : ℤ) ^ 7) * r3_2
      + (669600 + 999600 * (m : ℤ) + 626726 * (m : ℤ) ^ 2 + 214013 * (m : ℤ) ^ 3 + 43024 * (m : ℤ) ^ 4 + 5098 * (m : ℤ) ^ 5 + 330 * (m : ℤ) ^ 6 + 9 * (m : ℤ) ^ 7) * r3_3
      + (-129600 - 176400 * (m : ℤ) - 97776 * (m : ℤ) ^ 2 - 28196 * (m : ℤ) ^ 3 - 4452 * (m : ℤ) ^ 4 - 364 * (m : ℤ) ^ 5 - 12 * (m : ℤ) ^ 6) * r3_4
      + (226800 + 341100 * (m : ℤ) + 215208 * (m : ℤ) ^ 2 + 73787 * (m : ℤ) ^ 3 + 14840 * (m : ℤ) ^ 4 + 1750 * (m : ℤ) ^ 5 + 112 * (m : ℤ) ^ 6 + 3 * (m : ℤ) ^ 7) * r3_5
      + (9711360 + 14732112 * (m : ℤ) + 9553828 * (m : ℤ) ^ 2 + 3457872 * (m : ℤ) ^ 3 + 763320 * (m : ℤ) ^ 4 + 105096 * (m : ℤ) ^ 5 + 8796 * (m : ℤ) ^ 6 + 408 * (m : ℤ) ^ 7 + 8 * (m : ℤ) ^ 8) * u4
      + (-14072400 - 21460260 * (m : ℤ) - 14062516 * (m : ℤ) ^ 2 - 5178692 * (m : ℤ) ^ 3 - 1173824 * (m : ℤ) ^ 4 - 167924 * (m : ℤ) ^ 5 - 14828 * (m : ℤ) ^ 6 - 740 * (m : ℤ) ^ 7 - 16 * (m : ℤ) ^ 8) * v4
      + (1630800 + 2067060 * (m : ℤ) + 1082320 * (m : ℤ) ^ 2 + 302878 * (m : ℤ) ^ 3 + 48730 * (m : ℤ) ^ 4 + 4474 * (m : ℤ) ^ 5 + 214 * (m : ℤ) ^ 6 + 4 * (m : ℤ) ^ 7) * r4_2
      + (-2420640 - 3229488 * (m : ℤ) - 1805222 * (m : ℤ) ^ 2 - 549405 * (m : ℤ) ^ 3 - 98570 * (m : ℤ) ^ 4 - 10452 * (m : ℤ) ^ 5 - 608 * (m : ℤ) ^ 6 - 15 * (m : ℤ) ^ 7) * r4_3
      + (413280 + 502056 * (m : ℤ) + 247780 * (m : ℤ) ^ 2 + 63680 * (m : ℤ) ^ 3 + 9000 * (m : ℤ) ^ 4 + 664 * (m : ℤ) ^ 5 + 20 * (m : ℤ) ^ 6) * r4_4
      + (-826560 - 1107432 * (m : ℤ) - 621074 * (m : ℤ) ^ 2 - 189305 * (m : ℤ) ^ 3 - 33920 * (m : ℤ) ^ 4 - 3578 * (m : ℤ) ^ 5 - 206 * (m : ℤ) ^ 6 - 5 * (m : ℤ) ^ 7) * r4_5
      + (-928800 - 1323720 * (m : ℤ) - 795432 * (m : ℤ) ^ 2 - 261598 * (m : ℤ) ^ 3 - 50916 * (m : ℤ) ^ 4 - 5872 * (m : ℤ) ^ 5 - 372 * (m : ℤ) ^ 6 - 10 * (m : ℤ) ^ 7) * u5
      + (4116960 + 6156792 * (m : ℤ) + 3952920 * (m : ℤ) ^ 2 + 1425638 * (m : ℤ) ^ 3 + 316438 * (m : ℤ) ^ 4 + 44342 * (m : ℤ) ^ 5 + 3838 * (m : ℤ) ^ 6 + 188 * (m : ℤ) ^ 7 + 4 * (m : ℤ) ^ 8) * v5
      + (-185760 - 227592 * (m : ℤ) - 113568 * (m : ℤ) ^ 2 - 29606 * (m : ℤ) ^ 3 - 4262 * (m : ℤ) ^ 4 - 322 * (m : ℤ) ^ 5 - 10 * (m : ℤ) ^ 6) * r5_2
      + (529200 + 701820 * (m : ℤ) + 389256 * (m : ℤ) ^ 2 + 117287 * (m : ℤ) ^ 3 + 20780 * (m : ℤ) ^ 4 + 2170 * (m : ℤ) ^ 5 + 124 * (m : ℤ) ^ 6 + 3 * (m : ℤ) ^ 7) * r5_3
      + (-80640 - 98208 * (m : ℤ) - 48616 * (m : ℤ) ^ 2 - 12540 * (m : ℤ) ^ 3 - 1780 * (m : ℤ) ^ 4 - 132 * (m : ℤ) ^ 5 - 4 * (m : ℤ) ^ 6) * r5_4
      + (181440 + 241128 * (m : ℤ) + 133938 * (m : ℤ) ^ 2 + 40369 * (m : ℤ) ^ 3 + 7140 * (m : ℤ) ^ 4 + 742 * (m : ℤ) ^ 5 + 42 * (m : ℤ) ^ 6 + (m : ℤ) ^ 7) * r5_5
