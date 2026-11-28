import OMAStatements.S_oeis_a224186
import Mathlib

/-!
Proof of the conjectures for A224186 (n X 4 arrays over 0..2, rows unimodal, columns
nondecreasing).

An array is a multichain x 0 <= x 1 <= ... (componentwise order) of unimodal rows. Splitting off
the first row (`good_cons224186`), `T m r` (the number of ways to continue the row `r` by `m`
rows) satisfies `T (m + 1) r = Sum over unimodal s >= r of T m s`, and `a (n + 1)` is the sum
of `T n r`. On base-3 codes of rows this is the recursion `G`. If `N k c` is the number of
strict chains c < t_1 < ... < t_k of unimodal rows (a kernel-checked table), then
`G m c = Sum_k N k c * C(m, k)` by induction with Pascal's rule, so
`a (n + 1) = Sum_k D k * C(n, k)` with D = 46, 502, 2476, 6799, 11332, 11780, 7488, 2670, 410.
Expanding the binomials gives the closed form, from which the recurrence and the generating
function follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a224186 Finset

/-- A row of the array. -/
abbrev Row224186 := Fin 4 → Fin 3

instance decUnimodal224186 (r : Row224186) : Decidable (Unimodal r) := by
  unfold Unimodal
  infer_instance

/-- The conditions of the statement on an array with `m` rows. -/
def Good224186 {m : ℕ} (x : Fin m → Row224186) : Prop :=
  (∀ i, Unimodal (x i)) ∧ ∀ j, Monotone (fun i => x i j)

theorem col_cons224186 {m : ℕ} (r : Row224186) (B : Fin (m + 1) → Row224186) (j : Fin 4) :
    (fun i => (Fin.cons r B : Fin (m + 2) → Row224186) i j) =
      Matrix.vecCons (r j) (fun i => B i j) := by
  funext i
  refine Fin.cases rfl (fun i => rfl) i

theorem good_cons224186 {m : ℕ} (r : Row224186) (B : Fin (m + 1) → Row224186) :
    Good224186 (Fin.cons r B : Fin (m + 2) → Row224186) ↔
      Unimodal r ∧ (∀ j, r j ≤ B 0 j) ∧ Good224186 B := by
  have hm : ∀ j, Monotone (fun i => (Fin.cons r B : Fin (m + 2) → Row224186) i j) ↔
      r j ≤ B 0 j ∧ Monotone (fun i => B i j) := fun j => by
    rw [col_cons224186]; exact monotone_vecCons
  unfold Good224186
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, hm, forall_and]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    exact ⟨h0, h2, h1, h3⟩
  · rintro ⟨h0, h2, h1, h3⟩
    exact ⟨⟨h0, h1⟩, h2, h3⟩

theorem good_one224186 (r : Row224186) (B : Fin 0 → Row224186) :
    Good224186 (Fin.cons r B : Fin 1 → Row224186) ↔ Unimodal r := by
  have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
  unfold Good224186
  constructor
  · rintro ⟨h, _⟩
    simpa using h 0
  · intro h
    refine ⟨fun i => ?_, fun j => Subsingleton.monotone _⟩
    rw [Subsingleton.elim i 0]
    simpa using h

/-- The number of ways to continue the row `r` by `m` more rows. -/
noncomputable def T224186 (m : ℕ) (r : Row224186) : ℕ := by
  classical
  exact ∑ B : Fin m → Row224186,
    if Good224186 (Fin.cons r B : Fin (m + 1) → Row224186) then 1 else 0

theorem T_zero224186 (r : Row224186) :
    T224186 0 r = if Unimodal r then 1 else 0 := by
  classical
  unfold T224186
  rw [Fintype.sum_unique]
  exact if_congr (good_one224186 r _) rfl rfl

theorem T_succ224186 (m : ℕ) (r : Row224186) :
    T224186 (m + 1) r =
      ∑ s : Row224186, if Unimodal r ∧ (∀ j, r j ≤ s j) then T224186 m s else 0 := by
  classical
  unfold T224186
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row224186).symm _
    (fun p => if Good224186 (Fin.cons r (Fin.cons p.1 p.2) : Fin (m + 2) → Row224186)
      then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hv : Unimodal r ∧ (∀ j, r j ≤ s j)
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [good_cons224186]
    simp only [Fin.cons_zero]
    exact ⟨fun h => h.2.2, fun h => ⟨hv.1, hv.2, h⟩⟩
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [good_cons224186]
    simp only [Fin.cons_zero]
    exact fun h => hv ⟨h.1, h.2.1⟩

theorem a_eq224186 (n : ℕ) : a (n + 1) = ∑ r : Row224186, T224186 n r := by
  classical
  have h1 : a (n + 1) = ∑ x : Fin (n + 1) → Row224186, if Good224186 x then 1 else 0 := by
    unfold a
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    exact Finset.sum_congr rfl fun x _ => if_congr Iff.rfl rfl rfl
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => Row224186).symm _
    (fun p => if Good224186 (Fin.cons p.1 p.2 : Fin (n + 1) → Row224186) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  rfl

/-- The row with code `c`: its base-3 digits, most significant first. -/
def row224186 (c : Fin 81) : Row224186 :=
  fun j => ⟨c.val / 3 ^ (3 - j.val) % 3, Nat.mod_lt _ (by norm_num)⟩

theorem row_injective224186 : Function.Injective row224186 := by
  decide +kernel

theorem row_bijective224186 : Function.Bijective row224186 := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective224186, by simp⟩

/-- The unimodal codes, as a bit mask. -/
def Ut224186 (c : ℕ) : Bool := Nat.beq (2233909965389573657195519 / 2 ^ c % 2) 1

/-- Digitwise comparison of codes. -/
def Le224186 (c d : ℕ) : Bool :=
  Nat.ble (c / 27 % 3) (d / 27 % 3) && Nat.ble (c / 9 % 3) (d / 9 % 3) &&
    Nat.ble (c / 3 % 3) (d / 3 % 3) && Nat.ble (c % 3) (d % 3)

theorem Ut_iff224186 : ∀ c : Fin 81, Unimodal (row224186 c) ↔ Ut224186 c.val = true := by
  unfold Unimodal
  decide +kernel

theorem Le_iff224186 : ∀ c d : Fin 81,
    (∀ j, row224186 c j ≤ row224186 d j) ↔ Le224186 c.val d.val = true := by
  decide +kernel

/-- The transfer recursion on codes. -/
def G224186 : ℕ → Fin 81 → ℕ
  | 0, c => if Ut224186 c.val then 1 else 0
  | m + 1, c => ∑ d : Fin 81, if (Ut224186 c.val && Le224186 c.val d.val) then G224186 m d else 0

theorem T_eq_G224186 (m : ℕ) : ∀ c : Fin 81, T224186 m (row224186 c) = G224186 m c := by
  induction m with
  | zero =>
    intro c
    rw [T_zero224186, G224186]
    exact if_congr (Ut_iff224186 c) rfl rfl
  | succ m ih =>
    intro c
    rw [T_succ224186, ← row_bijective224186.sum_comp]
    simp only [G224186]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [ih d]
    refine if_congr ?_ rfl rfl
    rw [Ut_iff224186, Le_iff224186, Bool.and_eq_true]

theorem a_eq_G224186 (n : ℕ) : a (n + 1) = ∑ c : Fin 81, G224186 n c := by
  rw [a_eq224186, ← row_bijective224186.sum_comp]
  exact Finset.sum_congr rfl fun c _ => T_eq_G224186 n c

/-- `Ntab[c][k]`: the number of strict chains of unimodal rows of length `k` above the row `c`. -/
def Ntab224186 : List (List ℕ) :=
  [[1, 45, 457, 2019, 4780, 6552, 5228, 2260, 410],
   [1, 23, 140, 395, 605, 521, 238, 45, 0],
   [1, 9, 31, 54, 51, 25, 5, 0, 0],
   [1, 34, 263, 887, 1568, 1523, 772, 160, 0],
   [1, 21, 110, 254, 297, 173, 40, 0, 0],
   [1, 8, 23, 31, 20, 5, 0, 0, 0],
   [1, 17, 85, 193, 224, 130, 30, 0, 0],
   [1, 11, 37, 55, 38, 10, 0, 0, 0],
   [1, 5, 9, 7, 2, 0, 0, 0, 0],
   [1, 34, 263, 887, 1568, 1523, 772, 160, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 28, 173, 450, 578, 364, 90, 0, 0],
   [1, 17, 69, 116, 88, 25, 0, 0, 0],
   [1, 6, 12, 10, 3, 0, 0, 0, 0],
   [1, 14, 55, 92, 70, 20, 0, 0, 0],
   [1, 9, 23, 23, 8, 0, 0, 0, 0],
   [1, 4, 5, 2, 0, 0, 0, 0, 0],
   [1, 17, 85, 193, 224, 130, 30, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 14, 55, 92, 70, 20, 0, 0, 0],
   [1, 8, 19, 18, 6, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 8, 19, 18, 6, 0, 0, 0, 0],
   [1, 5, 7, 3, 0, 0, 0, 0, 0],
   [1, 2, 1, 0, 0, 0, 0, 0, 0],
   [1, 23, 140, 395, 605, 521, 238, 45, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 21, 110, 254, 297, 173, 40, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 17, 69, 116, 88, 25, 0, 0, 0],
   [1, 10, 25, 24, 8, 0, 0, 0, 0],
   [1, 3, 3, 1, 0, 0, 0, 0, 0],
   [1, 8, 19, 18, 6, 0, 0, 0, 0],
   [1, 5, 7, 3, 0, 0, 0, 0, 0],
   [1, 2, 1, 0, 0, 0, 0, 0, 0],
   [1, 11, 37, 55, 38, 10, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 9, 23, 23, 8, 0, 0, 0, 0],
   [1, 5, 7, 3, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 5, 7, 3, 0, 0, 0, 0, 0],
   [1, 3, 2, 0, 0, 0, 0, 0, 0],
   [1, 1, 0, 0, 0, 0, 0, 0, 0],
   [1, 9, 31, 54, 51, 25, 5, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 8, 23, 31, 20, 5, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 6, 12, 10, 3, 0, 0, 0, 0],
   [1, 3, 3, 1, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 5, 9, 7, 2, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 4, 5, 2, 0, 0, 0, 0, 0],
   [1, 2, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 2, 1, 0, 0, 0, 0, 0, 0],
   [1, 1, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Lookup in the chain table. -/
def N224186 (k : ℕ) (c : Fin 81) : ℕ := (Ntab224186.getD c.val []).getD k 0

theorem N_step224186 : ∀ c : Fin 81, ∀ k : Fin 9,
    (∑ d : Fin 81, if (Ut224186 c.val && Le224186 c.val d.val) then N224186 k.val d else 0) =
      N224186 k.val c + N224186 (k.val + 1) c := by
  decide +kernel

theorem N_zero224186 : ∀ c : Fin 81, N224186 0 c = if Ut224186 c.val then 1 else 0 := by
  decide +kernel

theorem N_nine224186 : ∀ c : Fin 81, N224186 9 c = 0 := by
  decide +kernel

theorem G_closed224186 (m : ℕ) :
    ∀ c : Fin 81, G224186 m c = ∑ k ∈ range 9, N224186 k c * m.choose k := by
  induction m with
  | zero =>
    intro c
    simp only [G224186, Finset.sum_range_succ, Finset.sum_range_zero, N_zero224186 c]
    simp
  | succ m ih =>
    intro c
    have h1 : G224186 (m + 1) c = ∑ k ∈ range 9,
        (∑ d : Fin 81, if (Ut224186 c.val && Le224186 c.val d.val) then N224186 k d else 0) *
          m.choose k := by
      simp only [G224186]
      rw [Finset.sum_congr rfl fun d _ => (show (if (Ut224186 c.val && Le224186 c.val d.val) then
          G224186 m d else 0) = ∑ k ∈ range 9, (if (Ut224186 c.val && Le224186 c.val d.val) then
          N224186 k d else 0) * m.choose k by
        split_ifs
        · exact ih d
        · simp), Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => (Finset.sum_mul _ _ _).symm
    have h2 : G224186 (m + 1) c =
        ∑ k ∈ range 9, (N224186 k c + N224186 (k + 1) c) * m.choose k := by
      rw [h1]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [N_step224186 c ⟨k, Finset.mem_range.mp hk⟩]
    rw [h2]
    have p1 : (m + 1).choose 1 = m.choose 0 + m.choose 1 := Nat.choose_succ_succ' m 0
    have p2 : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ' m 1
    have p3 : (m + 1).choose 3 = m.choose 2 + m.choose 3 := Nat.choose_succ_succ' m 2
    have p4 : (m + 1).choose 4 = m.choose 3 + m.choose 4 := Nat.choose_succ_succ' m 3
    have p5 : (m + 1).choose 5 = m.choose 4 + m.choose 5 := Nat.choose_succ_succ' m 4
    have p6 : (m + 1).choose 6 = m.choose 5 + m.choose 6 := Nat.choose_succ_succ' m 5
    have p7 : (m + 1).choose 7 = m.choose 6 + m.choose 7 := Nat.choose_succ_succ' m 6
    have p8 : (m + 1).choose 8 = m.choose 7 + m.choose 8 := Nat.choose_succ_succ' m 7
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, p1, p2, p3, p4, p5, p6, p7, p8,
      Nat.choose_zero_right, N_nine224186 c]
    ring

theorem D_facts224186 :
    (∑ c : Fin 81, N224186 0 c) = 46 ∧
    (∑ c : Fin 81, N224186 1 c) = 502 ∧
    (∑ c : Fin 81, N224186 2 c) = 2476 ∧
    (∑ c : Fin 81, N224186 3 c) = 6799 ∧
    (∑ c : Fin 81, N224186 4 c) = 11332 ∧
    (∑ c : Fin 81, N224186 5 c) = 11780 ∧
    (∑ c : Fin 81, N224186 6 c) = 7488 ∧
    (∑ c : Fin 81, N224186 7 c) = 2670 ∧
    (∑ c : Fin 81, N224186 8 c) = 410 := by
  decide +kernel

theorem a_closed224186 (n : ℕ) :
    a (n + 1) = 46 * n.choose 0 + 502 * n.choose 1 + 2476 * n.choose 2 + 6799 * n.choose 3 + 11332 * n.choose 4 + 11780 * n.choose 5 + 7488 * n.choose 6 + 2670 * n.choose 7 + 410 * n.choose 8 := by
  rw [a_eq_G224186]
  simp only [G_closed224186 n]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul]
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8⟩ := D_facts224186
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, d0, d1, d2, d3, d4, d5, d6, d7, d8]
  ring

theorem ch1_224186 (n : ℕ) : (n.choose 1 : ℚ) = n := by simp

theorem ch2_224186 (n : ℕ) : (n.choose 2 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 2 = n.choose 1 + n.choose 2 from Nat.choose_succ_succ' n 1,
      Nat.cast_add, ih, ch1_224186]
    push_cast
    ring

theorem ch3_224186 (n : ℕ) : (n.choose 3 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 3 = n.choose 2 + n.choose 3 from Nat.choose_succ_succ' n 2,
      Nat.cast_add, ih, ch2_224186]
    push_cast
    ring

theorem ch4_224186 (n : ℕ) : (n.choose 4 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) / 24 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 4 = n.choose 3 + n.choose 4 from Nat.choose_succ_succ' n 3,
      Nat.cast_add, ih, ch3_224186]
    push_cast
    ring

theorem ch5_224186 (n : ℕ) : (n.choose 5 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) * ((n : ℚ) - 4) / 120 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 5 = n.choose 4 + n.choose 5 from Nat.choose_succ_succ' n 4,
      Nat.cast_add, ih, ch4_224186]
    push_cast
    ring

theorem ch6_224186 (n : ℕ) : (n.choose 6 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) * ((n : ℚ) - 4) * ((n : ℚ) - 5) / 720 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 6 = n.choose 5 + n.choose 6 from Nat.choose_succ_succ' n 5,
      Nat.cast_add, ih, ch5_224186]
    push_cast
    ring

theorem ch7_224186 (n : ℕ) : (n.choose 7 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) * ((n : ℚ) - 4) * ((n : ℚ) - 5) * ((n : ℚ) - 6) / 5040 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 7 = n.choose 6 + n.choose 7 from Nat.choose_succ_succ' n 6,
      Nat.cast_add, ih, ch6_224186]
    push_cast
    ring

theorem ch8_224186 (n : ℕ) : (n.choose 8 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) * ((n : ℚ) - 4) * ((n : ℚ) - 5) * ((n : ℚ) - 6) * ((n : ℚ) - 7) / 40320 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 8 = n.choose 7 + n.choose 8 from Nat.choose_succ_succ' n 7,
      Nat.cast_add, ih, ch7_224186]
    push_cast
    ring

theorem closedQ224186 (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (1 : ℚ) + (2173/420 : ℚ) * (n : ℚ) + (56759/5040 : ℚ) * (n : ℚ) ^ 2 + (215/16 : ℚ) * (n : ℚ) ^ 3 + (615/64 : ℚ) * (n : ℚ) ^ 4 + (169/40 : ℚ) * (n : ℚ) ^ 5 + (179/160 : ℚ) * (n : ℚ) ^ 6 + (55/336 : ℚ) * (n : ℚ) ^ 7 + (41/4032 : ℚ) * (n : ℚ) ^ 8 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_closed224186]
  push_cast
  rw [ch1_224186, ch2_224186, ch3_224186, ch4_224186, ch5_224186, ch6_224186, ch7_224186,
    ch8_224186]
  simp only [Nat.choose_zero_right, Nat.cast_one]
  ring

theorem recurrence224186 (n : ℕ) (hn : 10 ≤ n) :
    (a n : ℤ) = 9 * (a (n - 1) : ℤ) - 36 * (a (n - 2) : ℤ) + 84 * (a (n - 3) : ℤ) - 126 * (a (n - 4) : ℤ) + 126 * (a (n - 5) : ℤ) - 84 * (a (n - 6) : ℤ) + 36 * (a (n - 7) : ℤ) - 9 * (a (n - 8) : ℤ) + 1 * (a (n - 9) : ℤ) := by
  have h : ((a n : ℤ) : ℚ) = ((9 * (a (n - 1) : ℤ) - 36 * (a (n - 2) : ℤ) + 84 * (a (n - 3) : ℤ) - 126 * (a (n - 4) : ℤ) + 126 * (a (n - 5) : ℤ) - 84 * (a (n - 6) : ℤ) + 36 * (a (n - 7) : ℤ) - 9 * (a (n - 8) : ℤ) + 1 * (a (n - 9) : ℤ) : ℤ) : ℚ) := by
    push_cast
    rw [closedQ224186 n (by omega), closedQ224186 (n - 1) (by omega), closedQ224186 (n - 2) (by omega), closedQ224186 (n - 3) (by omega), closedQ224186 (n - 4) (by omega), closedQ224186 (n - 5) (by omega), closedQ224186 (n - 6) (by omega), closedQ224186 (n - 7) (by omega), closedQ224186 (n - 8) (by omega), closedQ224186 (n - 9) (by omega)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega, show 8 ≤ n by omega, show 9 ≤ n by omega]
    ring
  exact_mod_cast h

open PowerSeries in
theorem gen_fun224186 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - PowerSeries.X) ^ 9 =
      C 1 * (PowerSeries.mk F * PowerSeries.X ^ 0) - C 9 * (PowerSeries.mk F * PowerSeries.X ^ 1) + C 36 * (PowerSeries.mk F * PowerSeries.X ^ 2) - C 84 * (PowerSeries.mk F * PowerSeries.X ^ 3) + C 126 * (PowerSeries.mk F * PowerSeries.X ^ 4) - C 126 * (PowerSeries.mk F * PowerSeries.X ^ 5) + C 84 * (PowerSeries.mk F * PowerSeries.X ^ 6) - C 36 * (PowerSeries.mk F * PowerSeries.X ^ 7) + C 9 * (PowerSeries.mk F * PowerSeries.X ^ 8) - C 1 * (PowerSeries.mk F * PowerSeries.X ^ 9) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (46 * PowerSeries.X + 134 * PowerSeries.X ^ 2 + 250 * PowerSeries.X ^ 3 - 91 * PowerSeries.X ^ 4 + 127 * PowerSeries.X ^ 5 - 84 * PowerSeries.X ^ 6 + 36 * PowerSeries.X ^ 7 - 9 * PowerSeries.X ^ 8 + 1 * PowerSeries.X ^ 9 : ℚ⟦X⟧) =
      C 46 * PowerSeries.X ^ 1 + C 134 * PowerSeries.X ^ 2 + C 250 * PowerSeries.X ^ 3 - C 91 * PowerSeries.X ^ 4 + C 127 * PowerSeries.X ^ 5 - C 84 * PowerSeries.X ^ 6 + C 36 * PowerSeries.X ^ 7 - C 9 * PowerSeries.X ^ 8 + C 1 * PowerSeries.X ^ 9 := by
    simp only [map_one, map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 10
  · interval_cases k <;> norm_num [hF, closedQ224186]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 10 := ⟨k - 10, by omega⟩
    simp only [show 0 ≤ j + 10 by omega,
      show j + 10 - 0 = j + 10 by omega,
      show 1 ≤ j + 10 by omega,
      show j + 10 - 1 = j + 9 by omega,
      show 2 ≤ j + 10 by omega,
      show j + 10 - 2 = j + 8 by omega,
      show 3 ≤ j + 10 by omega,
      show j + 10 - 3 = j + 7 by omega,
      show 4 ≤ j + 10 by omega,
      show j + 10 - 4 = j + 6 by omega,
      show 5 ≤ j + 10 by omega,
      show j + 10 - 5 = j + 5 by omega,
      show 6 ≤ j + 10 by omega,
      show j + 10 - 6 = j + 4 by omega,
      show 7 ≤ j + 10 by omega,
      show j + 10 - 7 = j + 3 by omega,
      show 8 ≤ j + 10 by omega,
      show j + 10 - 8 = j + 2 by omega,
      show 9 ≤ j + 10 by omega,
      show j + 10 - 9 = j + 1 by omega,
      show ¬ (j + 10 = 1) by omega,
      show ¬ (j + 10 = 2) by omega,
      show ¬ (j + 10 = 3) by omega,
      show ¬ (j + 10 = 4) by omega,
      show ¬ (j + 10 = 5) by omega,
      show ¬ (j + 10 = 6) by omega,
      show ¬ (j + 10 = 7) by omega,
      show ¬ (j + 10 = 8) by omega,
      show ¬ (j + 10 = 9) by omega,
      show ¬ (j + 1 = 0) by omega,
      show ¬ (j + 2 = 0) by omega,
      show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 5 = 0) by omega,
      show ¬ (j + 6 = 0) by omega,
      show ¬ (j + 7 = 0) by omega,
      show ¬ (j + 8 = 0) by omega,
      show ¬ (j + 9 = 0) by omega,
      show ¬ (j + 10 = 0) by omega,
      if_true, if_false, hF]
    rw [closedQ224186 (j + 10) (by omega), closedQ224186 (j + 9) (by omega), closedQ224186 (j + 8) (by omega), closedQ224186 (j + 7) (by omega), closedQ224186 (j + 6) (by omega), closedQ224186 (j + 5) (by omega), closedQ224186 (j + 4) (by omega), closedQ224186 (j + 3) (by omega), closedQ224186 (j + 2) (by omega), closedQ224186 (j + 1) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a224186.main :=
  ⟨OMA.Helpers.recurrence224186, OMA.Helpers.gen_fun224186, OMA.Helpers.closedQ224186⟩
