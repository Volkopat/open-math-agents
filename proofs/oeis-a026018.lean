import OMAStatements.S_oeis_a026018
import Mathlib

-- Credit: @hermitokatt (Lean proof with Claude Code)

/-!
Proof of R. J. Mathar's recurrence for A026018 (walks from 2 to 7), as for A026017.

1. Splitting a walk at its last step gives a Pascal-like recursion for the number `c L y` of walks.
2. By induction on the length, the reflection principle in closed form:
   `c L y = B L (m-1) - B L (m+2)` when `L + y = 2m`, so `a (j+6) = C(2j+11, j+3) - C(2j+11, j)`.
3. All eight binomials in the recurrence are rational multiples of `C(2q+11, q)`; the identity
   is a rational-function identity (`field_simp`, `ring`). The cases `n = 6, 7, 8` are numeric.
-/

namespace OMA.A026018Proof

open OMA.S_oeis_a026018

/-- Walks on `N` positions from `2` to `y` with steps `±1`, staying nonnegative. -/
def W (N y : ℕ) : Set (Fin N → ℕ) :=
  {s | (∀ i : Fin N, i.val = 0 → s i = 2) ∧
       (∀ i : Fin N, i.val = N - 1 → s i = y) ∧
       (∀ i j : Fin N, j.val = i.val + 1 → |(s j : ℤ) - (s i : ℤ)| = 1)}

theorem walks_eq (n : ℕ) : walks n = W (2 * n) 7 := rfl

/-- Extend a walk on `L+1` positions by a last value `y`. -/
def ext (L y : ℕ) (t : Fin (L + 1) → ℕ) : Fin (L + 2) → ℕ :=
  fun i => if h : i.val < L + 1 then t ⟨i.val, h⟩ else y

theorem ext_inj (L y : ℕ) : Function.Injective (ext L y) := by
  intro t t' h
  funext i
  have := congrFun h ⟨i.val, by omega⟩
  simpa [ext, i.isLt] using this

theorem abs_one {a b : ℤ} : |a - b| = 1 ↔ a = b + 1 ∨ a + 1 = b := by
  rw [abs_eq zero_le_one]; omega

theorem mem_W_succ (L y : ℕ) (s : Fin (L + 2) → ℕ) :
    s ∈ W (L + 2) y ↔ ∃ z t, t ∈ W (L + 1) z ∧ |(y : ℤ) - z| = 1 ∧ ext L y t = s := by
  constructor
  · rintro ⟨h0, hN, hs⟩
    refine ⟨s ⟨L, by omega⟩, fun i => s ⟨i.val, by omega⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro i hi; exact h0 _ hi
    · intro i hi; exact congrArg s (Fin.ext (by simp at hi ⊢; omega))
    · intro i j hij; exact hs _ _ hij
    · have h1 := hs ⟨L, by omega⟩ ⟨L + 1, by omega⟩ rfl
      rw [hN ⟨L + 1, by omega⟩ (by simp)] at h1
      exact h1
    · funext i
      by_cases h : i.val < L + 1
      · simp [ext, h]
      · simp only [ext, h, dite_false]
        exact (hN i (by omega)).symm
  · rintro ⟨z, t, ⟨h0, hN, hs⟩, hz, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp only [ext, show i.val < L + 1 by omega, dite_true]
      exact h0 _ hi
    · intro i hi
      simp only [ext, show ¬ i.val < L + 1 by omega, dite_false]
    · intro i j hij
      by_cases hj : j.val < L + 1
      · simp only [ext, hj, show i.val < L + 1 by omega, dite_true]
        exact hs ⟨i.val, by omega⟩ ⟨j.val, hj⟩ hij
      · simp only [ext, hj, show i.val < L + 1 by omega, dite_true, dite_false]
        rw [hN ⟨i.val, by omega⟩ (by simp; omega)]
        exact hz

theorem W_zero (L : ℕ) : W (L + 2) 0 = ext L 0 '' W (L + 1) 1 := by
  ext s
  rw [mem_W_succ]
  constructor
  · rintro ⟨z, t, ht, hz, rfl⟩
    rw [abs_one] at hz
    obtain rfl : z = 1 := by omega
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨1, t, ht, by norm_num, rfl⟩

theorem W_pos (L y : ℕ) :
    W (L + 2) (y + 1) = ext L (y + 1) '' W (L + 1) (y + 2) ∪ ext L (y + 1) '' W (L + 1) y := by
  ext s
  rw [mem_W_succ]
  constructor
  · rintro ⟨z, t, ht, hz, rfl⟩
    rw [abs_one] at hz
    rcases hz with hz | hz
    · obtain rfl : z = y := by omega
      exact Or.inr ⟨t, ht, rfl⟩
    · obtain rfl : z = y + 2 := by omega
      exact Or.inl ⟨t, ht, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨y + 2, t, ht, by rw [abs_one]; push_cast; omega, rfl⟩
    · exact ⟨y, t, ht, by rw [abs_one]; push_cast; omega, rfl⟩

theorem W_finite (L : ℕ) : ∀ y, (W (L + 1) y).Finite := by
  induction L with
  | zero =>
    intro y
    apply Set.Subsingleton.finite
    intro s hs s' hs'
    funext i
    rw [hs.1 i (by omega), hs'.1 i (by omega)]
  | succ L ih =>
    intro y
    cases y with
    | zero => rw [W_zero]; exact (ih 1).image _
    | succ y => rw [W_pos]; exact ((ih _).image _).union ((ih _).image _)

/-- `c L y`: the number of walks on `L+1` positions from `2` to `y`. -/
noncomputable def c (L y : ℕ) : ℕ := (W (L + 1) y).ncard

theorem c_zero (L : ℕ) : c (L + 1) 0 = c L 1 := by
  unfold c
  rw [W_zero, Set.ncard_image_of_injective _ (ext_inj _ _)]

theorem c_pos (L y : ℕ) : c (L + 1) (y + 1) = c L (y + 2) + c L y := by
  unfold c
  rw [W_pos, Set.ncard_union_eq _ ((W_finite _ _).image _) ((W_finite _ _).image _),
    Set.ncard_image_of_injective _ (ext_inj _ _), Set.ncard_image_of_injective _ (ext_inj _ _)]
  rw [Set.disjoint_left]
  rintro s ⟨t, ht, rfl⟩ ⟨t', ht', h⟩
  have e := congrFun h ⟨L, by omega⟩
  simp only [ext, show L < L + 1 by omega, dite_true] at e
  rw [ht.2.1 ⟨L, by omega⟩ (by simp), ht'.2.1 ⟨L, by omega⟩ (by simp)] at e
  omega

/-- Binomial coefficient with an integer lower index, zero below `0`. -/
def B (L : ℕ) (k : ℤ) : ℤ := if 0 ≤ k then (L.choose k.toNat : ℤ) else 0

theorem B_nat (L t : ℕ) : B L t = L.choose t := by simp [B]

theorem B_succ (L : ℕ) (k : ℤ) : B (L + 1) k = B L (k - 1) + B L k := by
  rcases lt_trichotomy k 0 with h | rfl | h
  · simp only [B, if_neg (show ¬ (0:ℤ) ≤ k by omega), if_neg (show ¬ (0:ℤ) ≤ k - 1 by omega)]
    ring
  · simp [B]
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, k = t + 1 := ⟨(k - 1).toNat, by omega⟩
    rw [show (t : ℤ) + 1 - 1 = (t : ℤ) by ring, show (t : ℤ) + 1 = ((t + 1 : ℕ) : ℤ) by push_cast; ring,
      B_nat, B_nat, B_nat, Nat.choose_succ_succ']
    push_cast; ring

theorem B_symm (L : ℕ) (k₁ k₂ : ℤ) (h : k₁ + k₂ = L) : B L k₁ = B L k₂ := by
  by_cases h₁ : 0 ≤ k₁
  · by_cases h₂ : 0 ≤ k₂
    · obtain ⟨t₁, rfl⟩ : ∃ t : ℕ, k₁ = t := ⟨k₁.toNat, by omega⟩
      obtain ⟨t₂, rfl⟩ : ∃ t : ℕ, k₂ = t := ⟨k₂.toNat, by omega⟩
      rw [B_nat, B_nat]
      exact_mod_cast Nat.choose_symm_of_eq_add (show L = t₁ + t₂ by omega)
    · simp only [B, h₁, h₂, if_true, if_false]
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · by_cases h₂ : 0 ≤ k₂
    · simp only [B, h₁, h₂, if_true, if_false]
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    · simp [B, h₁, h₂]

theorem B_zero (k : ℤ) : B 0 k = if k = 0 then 1 else 0 := by
  by_cases h1 : 0 ≤ k
  · by_cases h2 : k = 0
    · subst h2; simp [B]
    · simp only [B, h1, h2, if_true, if_false]
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · simp [B, h1, show k ≠ 0 by omega]

/-- The reflection principle: walks of length `L` from `2` to `y`. -/
theorem c_closed (L : ℕ) : ∀ (y : ℕ) (m : ℤ), (L : ℤ) + y = 2 * m →
    (c L y : ℤ) = B L (m - 1) - B L (m + 2) := by
  induction L with
  | zero =>
    intro y m h
    rw [B_zero, B_zero]
    by_cases hy : y = 2
    · subst hy
      have : W 1 2 = {fun _ => 2} := by
        ext s
        simp only [Set.mem_singleton_iff]
        constructor
        · intro hs; funext i; exact hs.1 i (by omega)
        · rintro rfl
          refine ⟨fun _ _ => rfl, fun _ _ => rfl, ?_⟩
          intro i j hij; omega
      simp only [c, this, Set.ncard_singleton]
      split_ifs <;> omega
    · have : W 1 y = ∅ := by
        ext s
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hs
        exact hy ((hs.2.1 0 (by simp)).symm.trans (hs.1 0 rfl))
      simp only [c, this, Set.ncard_empty]
      split_ifs <;> omega
  | succ L ih =>
    intro y m h
    cases y with
    | zero =>
      rw [c_zero, ih 1 m (by push_cast at h ⊢; omega), B_succ, B_succ,
        B_symm L (m - 1 - 1) (m + 2 - 1) (by push_cast at h; omega)]
      ring
    | succ y =>
      rw [c_pos]
      push_cast
      rw [ih (y + 2) m (by push_cast at h ⊢; omega), ih y (m - 1) (by push_cast at h ⊢; omega),
        B_succ, B_succ, show m - 1 + 2 = m + 2 - 1 by ring]
      ring

/-- `a (j + 6) = C(2j+11, j+3) - C(2j+11, j)`. -/
theorem a_closed (j : ℕ) :
    a (j + 6) = ((2 * j + 11).choose (j + 3) : ℤ) - ((2 * j + 11).choose j : ℤ) := by
  have h := c_closed (2 * j + 11) 7 (j + 9) (by push_cast; ring)
  unfold a
  rw [walks_eq, show 2 * (j + 6) = (2 * j + 11) + 1 by ring]
  change ((c (2 * j + 11) 7 : ℕ) : ℤ) = _
  rw [h, B_symm (2 * j + 11) (j + 9 - 1) (j + 3) (by push_cast; ring),
    B_symm (2 * j + 11) (j + 9 + 2) j (by push_cast; ring),
    show (j : ℤ) + 3 = ((j + 3 : ℕ) : ℤ) by push_cast; ring, B_nat, B_nat]

/-- `a (j + 3) = C(2j+5, j+5) - C(2j+5, j+8)`, for the small cases. -/
theorem a_closed2 (j : ℕ) :
    a (j + 3) = ((2 * j + 5).choose (j + 5) : ℤ) - ((2 * j + 5).choose (j + 8) : ℤ) := by
  have h := c_closed (2 * j + 5) 7 (j + 6) (by push_cast; ring)
  unfold a
  rw [walks_eq, show 2 * (j + 3) = (2 * j + 5) + 1 by ring]
  change ((c (2 * j + 5) 7 : ℕ) : ℤ) = _
  rw [h, show (j : ℤ) + 6 - 1 = ((j + 5 : ℕ) : ℤ) by push_cast; ring,
    show (j : ℤ) + 6 + 2 = ((j + 8 : ℕ) : ℤ) by push_cast; ring, B_nat, B_nat]

/-- `C(i+d+2, i+1) = C(i+d, i) (i+d+2)(i+d+1) / ((i+1)(d+1))`. -/
theorem choose_step (i d : ℕ) :
    ((i + d + 2).choose (i + 1) : ℚ) =
      ((i + d).choose i : ℚ) * (((i : ℚ) + d + 2) * ((i : ℚ) + d + 1)) / (((i : ℚ) + 1) * ((d : ℚ) + 1)) := by
  rw [show i + d + 2 = (i + 1) + (d + 1) by ring, Nat.cast_add_choose, Nat.cast_add_choose,
    show (i + 1) + (d + 1) = (i + d) + 1 + 1 by ring]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- `C(2q+11, q+3) = C(2q+11, q) (q+11)(q+10)(q+9) / ((q+1)(q+2)(q+3))`. -/
theorem choose_shift3 (q : ℕ) :
    ((2 * q + 11).choose (q + 3) : ℚ) =
      ((2 * q + 11).choose q : ℚ) * (((q : ℚ) + 11) * ((q : ℚ) + 10) * ((q : ℚ) + 9)) /
        (((q : ℚ) + 1) * ((q : ℚ) + 2) * ((q : ℚ) + 3)) := by
  rw [show 2 * q + 11 = (q + 3) + (q + 8) by ring, Nat.cast_add_choose,
    show (q + 3) + (q + 8) = q + (q + 11) by ring, Nat.cast_add_choose]
  rw [show q + 11 = q + 8 + 1 + 1 + 1 by ring, show q + 3 = q + 1 + 1 + 1 by ring]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

end OMA.A026018Proof

open OMA.S_oeis_a026018 OMA.A026018Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a026018.main := by
  intro n hn
  have e3 : a 3 = 1 := by rw [a_closed2 0]; decide
  have e4 : a 4 = 7 := by rw [a_closed2 1]; decide
  have e5 : a 5 = 36 := by rw [a_closed2 2]; decide
  have e6 : a 6 = 164 := by rw [a_closed2 3]; decide
  have e7 : a 7 = 702 := by rw [a_closed2 4]; decide
  have e8 : a 8 = 2898 := by rw [a_closed2 5]; decide
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | rfl | hk
  · norm_num [e3, e4, e5, e6]
  · norm_num [e4, e5, e6, e7]
  · norm_num [e5, e6, e7, e8]
  · obtain ⟨q, rfl⟩ : ∃ q, k = q + 3 := ⟨k - 3, by omega⟩
    rw [show q + 3 + 6 = q + 9 by ring, show q + 9 - 1 = q + 8 by omega,
      show q + 9 - 2 = q + 7 by omega, show q + 9 - 3 = q + 6 by omega]
    have h9 := a_closed (q + 3)
    have h8 := a_closed (q + 2)
    have h7 := a_closed (q + 1)
    have h6 := a_closed q
    simp only [show q + 3 + 6 = q + 9 by ring, show q + 2 + 6 = q + 8 by ring,
      show q + 1 + 6 = q + 7 by ring, show 2 * (q + 3) + 11 = 2 * q + 17 by ring,
      show 2 * (q + 2) + 11 = 2 * q + 15 by ring, show 2 * (q + 1) + 11 = 2 * q + 13 by ring,
      show q + 2 + 3 = q + 5 by ring, show q + 1 + 3 = q + 4 by ring] at h9 h8 h7 h6
    rw [h9, h8, h7, h6]
    have s0 := choose_shift3 q
    have p1 := choose_step (q + 3) (q + 8)
    have p2 := choose_step (q + 4) (q + 9)
    have p3 := choose_step (q + 5) (q + 10)
    have n1 := choose_step q (q + 11)
    have n2 := choose_step (q + 1) (q + 12)
    have n3 := choose_step (q + 2) (q + 13)
    simp only [show q + 3 + (q + 8) = 2 * q + 11 by ring,
      show q + 4 + (q + 9) = 2 * q + 13 by ring,
      show q + 5 + (q + 10) = 2 * q + 15 by ring,
      show q + (q + 11) = 2 * q + 11 by ring,
      show q + 1 + (q + 12) = 2 * q + 13 by ring,
      show q + 2 + (q + 13) = 2 * q + 15 by ring,
      show q + 3 + 1 = q + 4 by ring, show q + 4 + 1 = q + 5 by ring, show q + 5 + 1 = q + 6 by ring,
      show q + 1 + 1 = q + 2 by ring, show q + 2 + 1 = q + 3 by ring] at p1 p2 p3 n1 n2 n3
    push_cast at p1 p2 p3 n1 n2 n3 ⊢
    qify
    rw [p3, p2, p1, s0, n3, n2, n1]
    field_simp
    ring

