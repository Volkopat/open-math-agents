import OMAStatements.S_oeis_a385736
import Mathlib.Tactic

/-!
Mod-3 construction and finite exhaustion proof for OEIS A385736:
for n not in {0, 1, 3, 4, 7, 10}, explicit triangular triples witness
perimeter (triangular n), while for n in {0, 1, 3, 4, 7, 10}, any valid
triple satisfies i, j, k < 7 and is ruled out by finite decision.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a385736.main := by
  let T := OMA.S_oeis_a385736.triangular
  have hT : ∀ m : ℕ, 2 * T m = m * (m + 1) := by
    intro m
    dsimp [T, OMA.S_oeis_a385736.triangular]
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.mul_add, ih]
      ring
  have hfits_of_mul2 : ∀ p i j k : ℕ,
      2 * T i + 2 * T j + 2 * T k = 2 * p →
      2 * T k < 2 * T i + 2 * T j →
      2 * T j < 2 * T i + 2 * T k →
      2 * T i < 2 * T j + 2 * T k →
      OMA.S_oeis_a385736.fits p i j k := by
    intro p i j k hsum h1 h2 h3
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp [T] at hsum h1 h2 h3 <;> omega
  have hperim_2 : OMA.S_oeis_a385736.perimeter (T 2) := by
    refine ⟨1, 1, 1, hfits_of_mul2 (T 2) 1 1 1 ?_ ?_ ?_ ?_⟩ <;>
      simp only [hT] <;> decide
  have hperim_3m : ∀ m : ℕ, 2 ≤ m → OMA.S_oeis_a385736.perimeter (T (3 * m)) := by
    intro m hm
    refine ⟨2 * m, 2 * m, m - 1, hfits_of_mul2 (T (3 * m)) (2 * m) (2 * m) (m - 1) ?_ ?_ ?_ ?_⟩
    · simp only [hT]
      zify [show 1 ≤ m by omega]
      ring
    · simp only [hT]
      zify [show 1 ≤ m by omega]
      nlinarith
    · simp only [hT]
      zify [show 1 ≤ m by omega]
      nlinarith
    · simp only [hT]
      zify [show 1 ≤ m by omega]
      nlinarith
  have hperim_3m1 : ∀ m : ℕ, 4 ≤ m → OMA.S_oeis_a385736.perimeter (T (3 * m + 1)) := by
    intro m hm
    refine ⟨2 * m, 2 * m + 1, m, hfits_of_mul2 (T (3 * m + 1)) (2 * m) (2 * m + 1) m ?_ ?_ ?_ ?_⟩
    · simp only [hT]; ring
    · simp only [hT]; nlinarith
    · simp only [hT]; nlinarith
    · simp only [hT]; nlinarith
  have hperim_3m2 : ∀ m : ℕ, 1 ≤ m → OMA.S_oeis_a385736.perimeter (T (3 * m + 2)) := by
    intro m hm
    refine ⟨2 * m + 1, 2 * m + 1, m + 1,
      hfits_of_mul2 (T (3 * m + 2)) (2 * m + 1) (2 * m + 1) (m + 1) ?_ ?_ ?_ ?_⟩
    · simp only [hT]; ring
    · simp only [hT]; nlinarith
    · simp only [hT]; nlinarith
    · simp only [hT]; nlinarith
  have hperim_all : ∀ n : ℕ,
      n ≠ 0 → n ≠ 1 → n ≠ 3 → n ≠ 4 → n ≠ 7 → n ≠ 10 →
      OMA.S_oeis_a385736.perimeter (T n) := by
    intro n h0 h1 h3 h4 h7 h10
    rcases (by omega : n = 2 ∨ (2 ≤ n / 3 ∧ n = 3 * (n / 3)) ∨
        (4 ≤ n / 3 ∧ n = 3 * (n / 3) + 1) ∨ (1 ≤ n / 3 ∧ n = 3 * (n / 3) + 2)) with
      rfl | ⟨hm, hEq⟩ | ⟨hm, hEq⟩ | ⟨hm, hEq⟩
    · exact hperim_2
    · rw [hEq]; exact hperim_3m (n / 3) hm
    · rw [hEq]; exact hperim_3m1 (n / 3) hm
    · rw [hEq]; exact hperim_3m2 (n / 3) hm
  have hlt_7_of_le55 : ∀ p i : ℕ, p ≤ 55 → 2 * T i < p → i < 7 := by
    intro p i hp hlt
    have hi := hT i
    by_contra hge
    have : 7 ≤ i := by omega
    nlinarith
  have hno_small : ∀ n ∈ ({0, 1, 3, 4, 7, 10} : Finset ℕ),
      ¬ OMA.S_oeis_a385736.perimeter (T n) := by
    intro n hn ⟨i, j, k, hfit⟩
    have hn_le : T n ≤ 55 := by
      fin_cases hn <;> dsimp [T, OMA.S_oeis_a385736.triangular] <;> decide
    have hsum : T i + T j + T k = T n := hfit.1
    have h1 : T k < T i + T j := hfit.2.1
    have h2 : T j < T i + T k := hfit.2.2.1
    have h3 : T i < T j + T k := hfit.2.2.2
    dsimp [T] at hsum h1 h2 h3
    have hi : i < 7 := hlt_7_of_le55 (T n) i hn_le (by dsimp [T]; omega)
    have hj : j < 7 := hlt_7_of_le55 (T n) j hn_le (by dsimp [T]; omega)
    have hk : k < 7 := hlt_7_of_le55 (T n) k hn_le (by dsimp [T]; omega)
    let triB : ℕ → ℕ := fun m => m * (m + 1) / 2
    have htri : ∀ m, T m = triB m := fun m => by have := hT m; dsimp [triB]; omega
    let fitsB : ℕ → ℕ → ℕ → ℕ → Bool := fun p a b c =>
      decide (triB a + triB b + triB c = p) && decide (triB c < triB a + triB b) &&
      decide (triB b < triB a + triB c) && decide (triB a < triB b + triB c)
    have htrue : fitsB (triB n) i j k = true := by
      dsimp [fitsB]
      rw [← htri i, ← htri j, ← htri k, ← htri n]
      dsimp [T]
      simp [hsum, h1, h2, h3]
    have hfalse : (([0, 1, 3, 4, 7, 10] : List ℕ).all fun n' =>
        (List.range 7).all fun i' =>
        (List.range 7).all fun j' =>
        (List.range 7).all fun k' =>
        !fitsB (triB n') i' j' k') = true := by
      decide
    simp only [List.all_eq_true] at hfalse
    have hn_list : n ∈ ([0, 1, 3, 4, 7, 10] : List ℕ) := by
      fin_cases hn <;> decide
    have h4' := hfalse n hn_list i (List.mem_range.mpr hi)
      j (List.mem_range.mpr hj) k (List.mem_range.mpr hk)
    rw [htrue] at h4'
    cases h4'
  have hexc_small : ∀ n ∈ ({0, 1, 3, 4, 7, 10} : Finset ℕ),
      OMA.S_oeis_a385736.exceptional (T n) := by
    intro n hn
    fin_cases hn <;> dsimp [T, OMA.S_oeis_a385736.triangular, OMA.S_oeis_a385736.exceptional] <;>
      decide
  have hexc_bound : ∀ n : ℕ, OMA.S_oeis_a385736.exceptional (T n) → n ≤ 10 := by
    intro n hex
    have hTn := hT n
    have hle : T n ≤ 55 := by
      rcases hex with h | h | h | h | h | h <;> rw [h] <;> omega
    by_contra hgt
    have : 11 ≤ n := by omega
    nlinarith
  intro n
  by_cases hn_mem : n ∈ ({0, 1, 3, 4, 7, 10} : Finset ℕ)
  · constructor
    · intro _; exact hexc_small n hn_mem
    · intro _; exact hno_small n hn_mem
  · have hnot : n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 7 ∧ n ≠ 10 := by
      simpa [Finset.mem_insert, Finset.mem_singleton, not_or] using hn_mem
    have hperim := hperim_all n hnot.1 hnot.2.1 hnot.2.2.1 hnot.2.2.2.1 hnot.2.2.2.2.1 hnot.2.2.2.2.2
    constructor
    · intro hnp; exact False.elim (hnp hperim)
    · intro hex
      exfalso
      have hn10 := hexc_bound n hex
      have hTn := hT n
      have hmul : n * (n + 1) = 0 ∨ n * (n + 1) = 2 ∨ n * (n + 1) = 12 ∨
          n * (n + 1) = 20 ∨ n * (n + 1) = 56 ∨ n * (n + 1) = 110 := by
        dsimp [OMA.S_oeis_a385736.exceptional] at hex
        rcases hex with h | h | h | h | h | h <;> dsimp [T] at hTn <;> omega
      have h5 : n = 2 ∨ n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 9 := by omega
      rcases h5 with rfl | rfl | rfl | rfl | rfl <;> omega
