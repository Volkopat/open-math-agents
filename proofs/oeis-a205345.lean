import OMAStatements.S_oeis_a205345

/-!
Proof of Barker's conjectures for A205345 (arrays x(0..7) of nonnegative integers with
x(0) = x(7) = 0 whose adjacent entries are unequal and differ by at most n).

Every entry of a valid array is at most 3n (`valid_le`), so the valid arrays are the walks
0 = x(0), x(1), ..., x(7) = 0 of seven steps inside the box 0..3n, where a step goes from u to a
different v with |u - v| <= n (`Stp`). Let `w n k h` be the number of walks of k + 1 steps from
0 to h inside the box. Then `w n (k + 1) = T n (w n k)`, where
`T n g h = Sum_{y <= 3n, y step to h} g y` (`T`), and listing an array by its entries x(6), ..., x(1)
gives `a n = w n 6 0` (`a_eq_w`).

On the box the walk counts have four pieces: the value at 0, and a polynomial in (n, t) on each
of the blocks 1 + t, n + 1 + t and 2n + 1 + t for t < n (`Pw`). The window lemma (`window`)
writes `T n g h` as a difference of two prefix sums of `g`; computing these prefix sums block by
block (`pre1`, `pre2`, `pre3`) shows that `T n` maps a four-piece function to a four-piece
function whose pieces are explicit in terms of the antiderivatives of the old pieces (`T_pw`).
Starting from the one-step count `w n 0 h = [1 <= h <= n]`, this gives the explicit pieces `Bk`,
`Ck`, `Dk` of the k-step count (`pw1` .. `pw6`); each antiderivative `QBk`, `QCk`, `QDk` is
checked by telescoping (`tB1` .. `tB6`). The last step gives, for every n,
  a(n) = 841/180 n^6 - 1/3 n^5 - 19/36 n^4 + 1/3 n^3 - 103/90 n^2 - 3 n
(`a_formula`). The recurrence and the generating function follow by comparing coefficients:
the seventh difference of a polynomial of degree 6 vanishes.
-/

namespace OMA.Helpers

open OMA.S_oeis_a205345 Finset

/-- One step of an array: from `u` to `v`, unequal and differing by at most `n`. -/
def Stp (n u v : ℕ) : Prop := u ≠ v ∧ u ≤ v + n ∧ v ≤ u + n

instance decStp (n u v : ℕ) : Decidable (Stp n u v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The transfer operator on the box `0..3n`: the sum of `g y` over the `y ≤ 3n` that step to `h`. -/
def T (n : ℕ) (g : ℕ → ℚ) (h : ℕ) : ℚ :=
  ∑ y ∈ range (3 * n + 1), if Stp n y h then g y else 0

/-- The window lemma: the entries `y ≤ 3n` that step to `h` form an interval with `h` removed. -/
theorem window (n : ℕ) (g : ℕ → ℚ) (h : ℕ) (hh : h ≤ 3 * n) :
    T n g h = ∑ y ∈ range (min (3 * n) (h + n) + 1), g y - ∑ y ∈ range (h - n), g y - g h := by
  unfold T
  rw [← sum_filter]
  have hf : (range (3 * n + 1)).filter (fun y => Stp n y h) =
      (Ico (h - n) (min (3 * n) (h + n) + 1)).erase h := by
    ext y
    rw [mem_filter, mem_range, mem_erase, mem_Ico]
    unfold Stp
    omega
  rw [hf, sum_erase_eq_sub (by simp only [mem_Ico]; omega), sum_Ico_eq_sub _ (by omega)]

/-- A function on `0..3n` given by four pieces: the value at 0, and polynomial pieces on
`1..n`, `n+1..2n` and `2n+1..3n` (each indexed by `t < n`). -/
def Pw (n : ℕ) (g : ℕ → ℚ) (A : ℚ) (B C D : ℕ → ℚ) : Prop :=
  g 0 = A ∧ (∀ t < n, g (1 + t) = B t) ∧ (∀ t < n, g (n + 1 + t) = C t) ∧
    (∀ t < n, g (2 * n + 1 + t) = D t)

theorem pre1 (n : ℕ) (g : ℕ → ℚ) (A : ℚ) (B QB : ℕ → ℚ) (hA : g 0 = A)
    (hB : ∀ t < n, g (1 + t) = B t) (hQB : ∀ s, ∑ t ∈ range s, B t = QB s) :
    ∀ s ≤ n, ∑ y ∈ range (1 + s), g y = A + QB s := by
  intro s hs
  rw [← hQB s]
  induction s with
  | zero => simp [hA]
  | succ s ih =>
    rw [show 1 + (s + 1) = (1 + s) + 1 by ring, sum_range_succ, ih (by omega), sum_range_succ,
      hB s (by omega)]
    ring

theorem pre2 (n : ℕ) (g : ℕ → ℚ) (A : ℚ) (B C QB QC : ℕ → ℚ) (hA : g 0 = A)
    (hB : ∀ t < n, g (1 + t) = B t) (hC : ∀ t < n, g (n + 1 + t) = C t)
    (hQB : ∀ s, ∑ t ∈ range s, B t = QB s) (hQC : ∀ s, ∑ t ∈ range s, C t = QC s) :
    ∀ s ≤ n, ∑ y ∈ range (n + 1 + s), g y = A + QB n + QC s := by
  intro s hs
  rw [← hQC s]
  induction s with
  | zero =>
    rw [show n + 1 + 0 = 1 + n by ring, pre1 n g A B QB hA hB hQB n le_rfl]
    simp
  | succ s ih =>
    rw [show n + 1 + (s + 1) = (n + 1 + s) + 1 by ring, sum_range_succ, ih (by omega),
      sum_range_succ, hC s (by omega)]
    ring

theorem pre3 (n : ℕ) (g : ℕ → ℚ) (A : ℚ) (B C D QB QC QD : ℕ → ℚ) (hA : g 0 = A)
    (hB : ∀ t < n, g (1 + t) = B t) (hC : ∀ t < n, g (n + 1 + t) = C t)
    (hD : ∀ t < n, g (2 * n + 1 + t) = D t)
    (hQB : ∀ s, ∑ t ∈ range s, B t = QB s) (hQC : ∀ s, ∑ t ∈ range s, C t = QC s)
    (hQD : ∀ s, ∑ t ∈ range s, D t = QD s) :
    ∀ s ≤ n, ∑ y ∈ range (2 * n + 1 + s), g y = A + QB n + QC n + QD s := by
  intro s hs
  rw [← hQD s]
  induction s with
  | zero =>
    rw [show 2 * n + 1 + 0 = n + 1 + n by ring, pre2 n g A B C QB QC hA hB hC hQB hQC n le_rfl]
    simp
  | succ s ih =>
    rw [show 2 * n + 1 + (s + 1) = (2 * n + 1 + s) + 1 by ring, sum_range_succ, ih (by omega),
      sum_range_succ, hD s (by omega)]
    ring

/-- The value of `T n g` at 0. -/
theorem T_zero (n : ℕ) (g : ℕ → ℚ) (A : ℚ) (B QB : ℕ → ℚ) (hA : g 0 = A)
    (hB : ∀ t < n, g (1 + t) = B t) (hQB : ∀ s, ∑ t ∈ range s, B t = QB s) :
    T n g 0 = QB n := by
  rw [window n g 0 (Nat.zero_le _), show min (3 * n) (0 + n) + 1 = 1 + n by omega,
    pre1 n g A B QB hA hB hQB n le_rfl, show 0 - n = 0 by omega, sum_range_zero, hA]
  ring

/-- The transfer operator maps a four-piece function to a four-piece function. -/
theorem T_pw (n : ℕ) (g : ℕ → ℚ) (A : ℚ) (B C D QB QC QD : ℕ → ℚ) (hg : Pw n g A B C D)
    (hQB : ∀ s, ∑ t ∈ range s, B t = QB s) (hQC : ∀ s, ∑ t ∈ range s, C t = QC s)
    (hQD : ∀ s, ∑ t ∈ range s, D t = QD s) :
    Pw n (T n g) (QB n) (fun t => A + QB n + QC (t + 1) - B t)
      (fun t => QB n + QC n + QD (t + 1) - QB t - C t)
      (fun t => QC n + QD n - QC t - D t) := by
  obtain ⟨hA, hB, hC, hD⟩ := hg
  refine ⟨T_zero n g A B QB hA hB hQB, ?_, ?_, ?_⟩
  · intro t ht
    rw [window n g (1 + t) (by omega), show min (3 * n) (1 + t + n) + 1 = n + 1 + (t + 1) by omega,
      pre2 n g A B C QB QC hA hB hC hQB hQC (t + 1) (by omega), show 1 + t - n = 0 by omega,
      sum_range_zero, hB t ht]
    ring
  · intro t ht
    rw [window n g (n + 1 + t) (by omega),
      show min (3 * n) (n + 1 + t + n) + 1 = 2 * n + 1 + (t + 1) by omega,
      pre3 n g A B C D QB QC QD hA hB hC hD hQB hQC hQD (t + 1) (by omega),
      show n + 1 + t - n = 1 + t by omega, pre1 n g A B QB hA hB hQB t (by omega), hC t ht]
    ring
  · intro t ht
    rw [window n g (2 * n + 1 + t) (by omega),
      show min (3 * n) (2 * n + 1 + t + n) + 1 = 2 * n + 1 + n by omega,
      pre3 n g A B C D QB QC QD hA hB hC hD hQB hQC hQD n le_rfl,
      show 2 * n + 1 + t - n = n + 1 + t by omega,
      pre2 n g A B C QB QC hA hB hC hQB hQC t (by omega), hD t ht]
    ring

theorem Pw_congr {n : ℕ} {g : ℕ → ℚ} {A A' : ℚ} {B C D B' C' D' : ℕ → ℚ}
    (hg : Pw n g A B C D) (hA : A = A') (hB : ∀ t, B t = B' t) (hC : ∀ t, C t = C' t)
    (hD : ∀ t, D t = D' t) : Pw n g A' B' C' D' := by
  obtain ⟨h0, h1, h2, h3⟩ := hg
  refine ⟨h0.trans hA, fun t ht => (h1 t ht).trans (hB t), fun t ht => (h2 t ht).trans (hC t),
    fun t ht => (h3 t ht).trans (hD t)⟩

/-- `w n k h`: the number of walks `0 = y 0, y 1, ..., y (k + 1) = h` of `k + 1` steps with all
entries in `0..3n`. -/
def w (n : ℕ) : ℕ → ℕ → ℚ
  | 0, h => if Stp n 0 h then 1 else 0
  | k + 1, h => T n (w n k) h

/-- Every entry of a valid array is at most `3n`. -/
theorem valid_le (n : ℕ) (x : Fin 8 → ℕ) (hx : IsValid n x) (i : Fin 8) : x i ≤ 3 * n := by
  obtain ⟨h0, h7, h⟩ := hx
  have c0 : x 0 ≠ x 1 ∧ x 0 ≤ x 1 + n ∧ x 1 ≤ x 0 + n := h 0
  have c1 : x 1 ≠ x 2 ∧ x 1 ≤ x 2 + n ∧ x 2 ≤ x 1 + n := h 1
  have c2 : x 2 ≠ x 3 ∧ x 2 ≤ x 3 + n ∧ x 3 ≤ x 2 + n := h 2
  have c3 : x 3 ≠ x 4 ∧ x 3 ≤ x 4 + n ∧ x 4 ≤ x 3 + n := h 3
  have c4 : x 4 ≠ x 5 ∧ x 4 ≤ x 5 + n ∧ x 5 ≤ x 4 + n := h 4
  have c5 : x 5 ≠ x 6 ∧ x 5 ≤ x 6 + n ∧ x 6 ≤ x 5 + n := h 5
  have c6 : x 6 ≠ x 7 ∧ x 6 ≤ x 7 + n ∧ x 7 ≤ x 6 + n := h 6
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega

/-- The count of valid arrays is the walk count `w n 6 0` (seven steps from 0 back to 0). -/
theorem a_eq_w (n : ℕ) : (a n : ℚ) = w n 6 0 := by
  classical
  let S := (Fintype.piFinset fun _ : Fin 8 => range (3 * n + 1)).filter (IsValid n)
  have h1 : a n = S.card := by
    unfold a
    have e : {x : Fin 8 → ℕ // IsValid n x} ≃ {x // x ∈ S} := Equiv.subtypeEquivRight (fun x => by
      simp only [S, mem_filter, Fintype.mem_piFinset, mem_range]
      constructor
      · intro hx
        exact ⟨fun i => by have := valid_le n x hx i; omega, hx⟩
      · intro hx
        exact hx.2)
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  let P6 := (range (3 * n + 1) ×ˢ range (3 * n + 1) ×ˢ range (3 * n + 1) ×ˢ range (3 * n + 1) ×ˢ
      range (3 * n + 1) ×ˢ range (3 * n + 1)).filter
    (fun p : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => Stp n p.1 0 ∧ Stp n p.2.1 p.1 ∧ Stp n p.2.2.1 p.2.1 ∧
      Stp n p.2.2.2.1 p.2.2.1 ∧ Stp n p.2.2.2.2.1 p.2.2.2.1 ∧ Stp n p.2.2.2.2.2 p.2.2.2.2.1 ∧
      Stp n 0 p.2.2.2.2.2)
  have h2 : S.card = P6.card := by
    apply card_nbij' (fun x => (x 6, x 5, x 4, x 3, x 2, x 1))
      (fun p => ![0, p.2.2.2.2.2, p.2.2.2.2.1, p.2.2.2.1, p.2.2.1, p.2.1, p.1, 0])
    · intro x hx
      rw [mem_coe, mem_filter] at hx
      obtain ⟨hb, hv⟩ := hx
      have hv' := hv
      obtain ⟨h0, h7, h⟩ := hv'
      have c0 : x 0 ≠ x 1 ∧ x 0 ≤ x 1 + n ∧ x 1 ≤ x 0 + n := h 0
      have c1 : x 1 ≠ x 2 ∧ x 1 ≤ x 2 + n ∧ x 2 ≤ x 1 + n := h 1
      have c2 : x 2 ≠ x 3 ∧ x 2 ≤ x 3 + n ∧ x 3 ≤ x 2 + n := h 2
      have c3 : x 3 ≠ x 4 ∧ x 3 ≤ x 4 + n ∧ x 4 ≤ x 3 + n := h 3
      have c4 : x 4 ≠ x 5 ∧ x 4 ≤ x 5 + n ∧ x 5 ≤ x 4 + n := h 4
      have c5 : x 5 ≠ x 6 ∧ x 5 ≤ x 6 + n ∧ x 6 ≤ x 5 + n := h 5
      have c6 : x 6 ≠ x 7 ∧ x 6 ≤ x 7 + n ∧ x 7 ≤ x 6 + n := h 6
      rw [h0] at c0
      rw [h7] at c6
      rw [mem_coe, mem_filter]
      simp only [mem_product, mem_range]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have := valid_le n x hv 6; omega
      · have := valid_le n x hv 5; omega
      · have := valid_le n x hv 4; omega
      · have := valid_le n x hv 3; omega
      · have := valid_le n x hv 2; omega
      · have := valid_le n x hv 1; omega
      · exact c6
      · exact c5
      · exact c4
      · exact c3
      · exact c2
      · exact c1
      · exact c0
    · intro p hp
      rw [mem_coe, mem_filter] at hp
      obtain ⟨hb, d6, d5, d4, d3, d2, d1, d0⟩ := hp
      simp only [mem_product, mem_range] at hb
      rw [mem_coe, mem_filter]
      refine ⟨?_, rfl, rfl, ?_⟩
      · rw [Fintype.mem_piFinset]
        intro i
        rw [mem_range]
        fin_cases i
        · show 0 < 3 * n + 1
          omega
        · exact hb.2.2.2.2.2
        · exact hb.2.2.2.2.1
        · exact hb.2.2.2.1
        · exact hb.2.2.1
        · exact hb.2.1
        · exact hb.1
        · show 0 < 3 * n + 1
          omega
      · intro i
        fin_cases i
        · exact d0
        · exact d1
        · exact d2
        · exact d3
        · exact d4
        · exact d5
        · exact d6
    · intro x hx
      rw [mem_coe, mem_filter] at hx
      obtain ⟨_, h0, h7, _⟩ := hx
      funext i
      fin_cases i
      · exact h0.symm
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact h7.symm
    · intro p _
      rfl
  rw [h1, h2, natCast_card_filter]
  simp only [sum_product, ite_and, sum_ite_irrel, sum_const_zero]
  rfl

/-! Explicit pieces. `Bk N T`, `Ck N T`, `Dk N T` are the pieces of the walk count of `k` steps
(at `n = N`, position `1 + T`, `n + 1 + T`, `2n + 1 + T`), and `QBk N S` is the sum of `Bk N T`
over `T < S` (similarly `QCk`, `QDk`). -/

def B1 (_N _T : ℚ) : ℚ :=
  1

def QB1 (_N S : ℚ) : ℚ :=
  S

def B2 (N _T : ℚ) : ℚ :=
  N - 1

def C2 (N T : ℚ) : ℚ :=
  N - T

def QB2 (N S : ℚ) : ℚ :=
  N * S - S

def QC2 (N S : ℚ) : ℚ :=
  N * S - S ^ 2 / 2 + S / 2

def B3 (N T : ℚ) : ℚ :=
  N ^ 2 + N * T - T ^ 2 / 2 - T / 2 + 1

def C3 (N T : ℚ) : ℚ :=
  3 * N ^ 2 / 2 - N * T - 3 * N / 2 + 2 * T

def D3 (N T : ℚ) : ℚ :=
  N ^ 2 / 2 - N * T + T ^ 2 / 2 + N / 2 - T / 2

def QB3 (N S : ℚ) : ℚ :=
  N ^ 2 * S + N * S ^ 2 / 2 - S ^ 3 / 6 - N * S / 2 + 7 * S / 6

def QC3 (N S : ℚ) : ℚ :=
  3 * N ^ 2 * S / 2 - N * S ^ 2 / 2 - N * S + S ^ 2 - S

def QD3 (N S : ℚ) : ℚ :=
  N ^ 2 * S / 2 - N * S ^ 2 / 2 + S ^ 3 / 6 + N * S - S ^ 2 / 2 + S / 3

def B4 (N T : ℚ) : ℚ :=
  4 * N ^ 3 / 3 + 3 * N ^ 2 * T / 2 - N * T ^ 2 / 2 + N ^ 2 - 3 * N * T + 3 * T ^ 2 / 2 - 4 * N / 3
    + 3 * T / 2 - 1

def C4 (N T : ℚ) : ℚ :=
  7 * N ^ 3 / 3 - N ^ 2 * T / 2 - N * T ^ 2 + T ^ 3 / 3 - 3 * N ^ 2 / 2 + 3 * N * T / 2 + 13 * N / 6
    - 10 * T / 3

def D4 (N T : ℚ) : ℚ :=
  7 * N ^ 3 / 6 - 3 * N ^ 2 * T / 2 + N * T ^ 2 / 2 + 2 * N * T - 3 * T ^ 2 / 2 - 7 * N / 6
    + 3 * T / 2

def QB4 (N S : ℚ) : ℚ :=
  4 * N ^ 3 * S / 3 + 3 * N ^ 2 * S ^ 2 / 4 - N * S ^ 3 / 6 + N ^ 2 * S / 4 - 5 * N * S ^ 2 / 4
    + S ^ 3 / 2 + N * S / 12 - 3 * S / 2

def QC4 (N S : ℚ) : ℚ :=
  7 * N ^ 3 * S / 3 - N ^ 2 * S ^ 2 / 4 - N * S ^ 3 / 3 + S ^ 4 / 12 - 5 * N ^ 2 * S / 4
    + 5 * N * S ^ 2 / 4 - S ^ 3 / 6 + 5 * N * S / 4 - 19 * S ^ 2 / 12 + 5 * S / 3

def QD4 (N S : ℚ) : ℚ :=
  7 * N ^ 3 * S / 6 - 3 * N ^ 2 * S ^ 2 / 4 + N * S ^ 3 / 6 + 3 * N ^ 2 * S / 4 + 3 * N * S ^ 2 / 4
    - S ^ 3 / 2 - 25 * N * S / 12 + 3 * S ^ 2 / 2 - S

def B5 (N T : ℚ) : ℚ :=
  23 * N ^ 4 / 12 + 7 * N ^ 3 * T / 3 - N ^ 2 * T ^ 2 / 4 - N * T ^ 3 / 3 + T ^ 4 / 12
    + 11 * N ^ 3 / 6 - 13 * N ^ 2 * T / 4 + 3 * N * T ^ 2 / 4 + T ^ 3 / 6 - 35 * N ^ 2 / 12
    + 23 * N * T / 4 - 37 * T ^ 2 / 12 + 19 * N / 6 - 19 * T / 6 + 1

def C5 (N T : ℚ) : ℚ :=
  15 * N ^ 4 / 4 - N ^ 3 * T / 6 - 3 * N ^ 2 * T ^ 2 / 2 + N * T ^ 3 / 3 - 11 * N ^ 3 / 6
    - N ^ 2 * T / 2 + 7 * N * T ^ 2 / 2 - 4 * T ^ 3 / 3 + 5 * N ^ 2 / 4 - 5 * N * T / 3 - 19 * N / 6
    + 16 * T / 3

def D5 (N T : ℚ) : ℚ :=
  29 * N ^ 4 / 12 - 7 * N ^ 3 * T / 3 + N ^ 2 * T ^ 2 / 4 + N * T ^ 3 / 3 - T ^ 4 / 12 - N ^ 3 / 3
    + 11 * N ^ 2 * T / 4 - 7 * N * T ^ 2 / 4 + T ^ 3 / 6 - 11 * N ^ 2 / 12 - 13 * N * T / 4
    + 37 * T ^ 2 / 12 + 11 * N / 6 - 19 * T / 6

def QB5 (N S : ℚ) : ℚ :=
  23 * N ^ 4 * S / 12 + 7 * N ^ 3 * S ^ 2 / 6 - N ^ 2 * S ^ 3 / 12 - N * S ^ 4 / 12 + S ^ 5 / 60
    + 2 * N ^ 3 * S / 3 - 3 * N ^ 2 * S ^ 2 / 2 + 5 * N * S ^ 3 / 12 - 4 * N ^ 2 * S / 3
    + 29 * N * S ^ 2 / 12 - 13 * S ^ 3 / 12 + 5 * N * S / 12 + 31 * S / 15

def QC5 (N S : ℚ) : ℚ :=
  15 * N ^ 4 * S / 4 - N ^ 3 * S ^ 2 / 12 - N ^ 2 * S ^ 3 / 2 + N * S ^ 4 / 12 - 7 * N ^ 3 * S / 4
    + N ^ 2 * S ^ 2 / 2 + N * S ^ 3 - S ^ 4 / 3 + 5 * N ^ 2 * S / 4 - 5 * N * S ^ 2 / 2
    + 2 * S ^ 3 / 3 - 7 * N * S / 4 + 7 * S ^ 2 / 3 - 8 * S / 3

def QD5 (N S : ℚ) : ℚ :=
  29 * N ^ 4 * S / 12 - 7 * N ^ 3 * S ^ 2 / 6 + N ^ 2 * S ^ 3 / 12 + N * S ^ 4 / 12 - S ^ 5 / 60
    + 5 * N ^ 3 * S / 6 + 5 * N ^ 2 * S ^ 2 / 4 - 3 * N * S ^ 3 / 4 + S ^ 4 / 12 - 9 * N ^ 2 * S / 4
    - 2 * N * S ^ 2 / 3 + 11 * S ^ 3 / 12 + 19 * N * S / 6 - 37 * S ^ 2 / 12 + 21 * S / 10

def B6 (N T : ℚ) : ℚ :=
  44 * N ^ 5 / 15 + 15 * N ^ 4 * T / 4 - N ^ 3 * T ^ 2 / 12 - N ^ 2 * T ^ 3 / 2 + N * T ^ 4 / 12
    + 10 * N ^ 4 / 3 - 17 * N ^ 3 * T / 4 - 3 * N ^ 2 * T ^ 2 / 4 + 5 * N * T ^ 3 / 3
    - 5 * T ^ 4 / 12 - 25 * N ^ 3 / 6 + 4 * N ^ 2 * T + N * T ^ 2 / 4 - 5 * T ^ 3 / 6
    + 14 * N ^ 2 / 3 - 55 * N * T / 6 + 65 * T ^ 2 / 12 - 173 * N / 30 + 35 * T / 6 - 1

def C6 (N T : ℚ) : ℚ :=
  371 * N ^ 5 / 60 + N ^ 4 * T / 2 - 7 * N ^ 3 * T ^ 2 / 3 + N ^ 2 * T ^ 3 / 6 + N * T ^ 4 / 6
    - T ^ 5 / 30 - 7 * N ^ 4 / 3 - 2 * N ^ 3 * T + 9 * N ^ 2 * T ^ 2 / 2 - 7 * N * T ^ 3 / 6
    + 11 * N ^ 3 / 12 + 7 * N ^ 2 * T / 3 - 25 * N * T ^ 2 / 3 + 7 * T ^ 3 / 2 - 7 * N ^ 2 / 6
    + 7 * N * T / 6 + 22 * N / 5 - 127 * T / 15

def D6 (N T : ℚ) : ℚ :=
  93 * N ^ 5 / 20 - 15 * N ^ 4 * T / 4 + N ^ 3 * T ^ 2 / 12 + N ^ 2 * T ^ 3 / 2 - N * T ^ 4 / 12
    - 19 * N ^ 4 / 12 + 49 * N ^ 3 * T / 12 - 3 * N ^ 2 * T ^ 2 / 4 - 4 * N * T ^ 3 / 3
    + 5 * T ^ 4 / 12 - 9 * N ^ 3 / 4 - 4 * N ^ 2 * T + 17 * N * T ^ 2 / 4 - 5 * T ^ 3 / 6
    + 19 * N ^ 2 / 12 + 5 * N * T - 65 * T ^ 2 / 12 - 12 * N / 5 + 35 * T / 6

def QB6 (N S : ℚ) : ℚ :=
  44 * N ^ 5 * S / 15 + 15 * N ^ 4 * S ^ 2 / 8 - N ^ 3 * S ^ 3 / 36 - N ^ 2 * S ^ 4 / 8
    + N * S ^ 5 / 60 + 35 * N ^ 4 * S / 24 - 25 * N ^ 3 * S ^ 2 / 12 + 3 * N * S ^ 4 / 8
    - S ^ 5 / 12 - 37 * N ^ 3 * S / 18 + 9 * N ^ 2 * S ^ 2 / 4 - 13 * N * S ^ 3 / 18
    + 61 * N ^ 2 * S / 24 - 103 * N * S ^ 2 / 24 + 25 * S ^ 3 / 12 - 103 * N * S / 90 - 3 * S

theorem tB1 (N : ℚ) (s : ℕ) : ∑ t ∈ range s, B1 N t = QB1 N s := by
  induction s with
  | zero => simp [QB1]
  | succ s ih =>
    rw [sum_range_succ, ih]
    simp only [B1, QB1]
    push_cast
    ring

theorem tB2 (N : ℚ) (s : ℕ) : ∑ t ∈ range s, B2 N t = QB2 N s := by
  induction s with
  | zero => simp [QB2]
  | succ s ih =>
    rw [sum_range_succ, ih]
    simp only [B2, QB2]
    push_cast
    ring

theorem tC2 (N : ℚ) (s : ℕ) : ∑ t ∈ range s, C2 N t = QC2 N s := by
  induction s with
  | zero => simp [QC2]
  | succ s ih =>
    rw [sum_range_succ, ih]
    simp only [C2, QC2]
    push_cast
    ring

theorem tB3 (N : ℚ) (s : ℕ) : ∑ t ∈ range s, B3 N t = QB3 N s := by
  induction s with
  | zero => simp [QB3]
  | succ s ih =>
    rw [sum_range_succ, ih]
    simp only [B3, QB3]
    push_cast
    ring

theorem tC3 (N : ℚ) (s : ℕ) : ∑ t ∈ range s, C3 N t = QC3 N s := by
  induction s with
  | zero => simp [QC3]
  | succ s ih =>
    rw [sum_range_succ, ih]
    simp only [C3, QC3]
    push_cast
    ring

theorem tD3 (N : ℚ) (s : ℕ) : ∑ t ∈ range s, D3 N t = QD3 N s := by
  induction s with
  | zero => simp [QD3]
  | succ s ih =>
    rw [sum_range_succ, ih]
    simp only [D3, QD3]
    push_cast
    ring

theorem tB4 (N : ℚ) (s : ℕ) : ∑ t ∈ range s, B4 N t = QB4 N s := by
  induction s with
  | zero => simp [QB4]
  | succ s ih =>
    rw [sum_range_succ, ih]
    simp only [B4, QB4]
    push_cast
    ring

theorem tC4 (N : ℚ) (s : ℕ) : ∑ t ∈ range s, C4 N t = QC4 N s := by
  induction s with
  | zero => simp [QC4]
  | succ s ih =>
    rw [sum_range_succ, ih]
    simp only [C4, QC4]
    push_cast
    ring

theorem tD4 (N : ℚ) (s : ℕ) : ∑ t ∈ range s, D4 N t = QD4 N s := by
  induction s with
  | zero => simp [QD4]
  | succ s ih =>
    rw [sum_range_succ, ih]
    simp only [D4, QD4]
    push_cast
    ring

theorem tB5 (N : ℚ) (s : ℕ) : ∑ t ∈ range s, B5 N t = QB5 N s := by
  induction s with
  | zero => simp [QB5]
  | succ s ih =>
    rw [sum_range_succ, ih]
    simp only [B5, QB5]
    push_cast
    ring

theorem tC5 (N : ℚ) (s : ℕ) : ∑ t ∈ range s, C5 N t = QC5 N s := by
  induction s with
  | zero => simp [QC5]
  | succ s ih =>
    rw [sum_range_succ, ih]
    simp only [C5, QC5]
    push_cast
    ring

theorem tD5 (N : ℚ) (s : ℕ) : ∑ t ∈ range s, D5 N t = QD5 N s := by
  induction s with
  | zero => simp [QD5]
  | succ s ih =>
    rw [sum_range_succ, ih]
    simp only [D5, QD5]
    push_cast
    ring

theorem tB6 (N : ℚ) (s : ℕ) : ∑ t ∈ range s, B6 N t = QB6 N s := by
  induction s with
  | zero => simp [QB6]
  | succ s ih =>
    rw [sum_range_succ, ih]
    simp only [B6, QB6]
    push_cast
    ring

theorem pw1 (n : ℕ) : Pw n (w n 0) 0 (fun t => B1 n t) (fun _ => 0) (fun _ => 0) := by
  refine ⟨?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · show (if Stp n 0 0 then (1 : ℚ) else 0) = 0
    rw [if_neg (fun h => by obtain ⟨h1, -, -⟩ := h; exact h1 rfl)]
  · show (if Stp n 0 (1 + t) then (1 : ℚ) else 0) = B1 n t
    rw [if_pos ⟨by omega, by omega, by omega⟩]
    rfl
  · show (if Stp n 0 (n + 1 + t) then (1 : ℚ) else 0) = 0
    rw [if_neg (fun h => by obtain ⟨-, -, h3⟩ := h; omega)]
  · show (if Stp n 0 (2 * n + 1 + t) then (1 : ℚ) else 0) = 0
    rw [if_neg (fun h => by obtain ⟨-, -, h3⟩ := h; omega)]

theorem pw2 (n : ℕ) :
    Pw n (w n 1) (QB1 n n) (fun t => B2 n t) (fun t => C2 n t) (fun _ => 0) :=
  Pw_congr (T_pw n (w n 0) 0 (fun t => B1 n t) (fun _ => 0) (fun _ => 0)
      (fun s => QB1 n s) (fun _ => 0) (fun _ => 0) (pw1 n)
      (tB1 n) (fun s => by simp) (fun s => by simp))
    rfl
    (fun t => by simp only [QB1, B1, B2]; ring)
    (fun t => by simp only [QB1, C2]; ring)
    (fun t => by simp)

theorem pw3 (n : ℕ) :
    Pw n (w n 2) (QB2 n n) (fun t => B3 n t) (fun t => C3 n t) (fun t => D3 n t) :=
  Pw_congr (T_pw n (w n 1) (QB1 n n) (fun t => B2 n t) (fun t => C2 n t) (fun _ => 0)
      (fun s => QB2 n s) (fun s => QC2 n s) (fun _ => 0) (pw2 n)
      (tB2 n) (tC2 n) (fun s => by simp))
    rfl
    (fun t => by simp only [QB1, QB2, QC2, B2, B3]; push_cast; ring)
    (fun t => by simp only [QB2, QC2, C2, C3]; ring)
    (fun t => by simp only [QC2, D3]; ring)

theorem pw4 (n : ℕ) :
    Pw n (w n 3) (QB3 n n) (fun t => B4 n t) (fun t => C4 n t) (fun t => D4 n t) :=
  Pw_congr (T_pw n (w n 2) (QB2 n n) (fun t => B3 n t) (fun t => C3 n t) (fun t => D3 n t)
      (fun s => QB3 n s) (fun s => QC3 n s) (fun s => QD3 n s) (pw3 n)
      (tB3 n) (tC3 n) (tD3 n))
    rfl
    (fun t => by simp only [QB2, QB3, QC3, B3, B4]; push_cast; ring)
    (fun t => by simp only [QB3, QC3, QD3, C3, C4]; push_cast; ring)
    (fun t => by simp only [QC3, QD3, D3, D4]; ring)

theorem pw5 (n : ℕ) :
    Pw n (w n 4) (QB4 n n) (fun t => B5 n t) (fun t => C5 n t) (fun t => D5 n t) :=
  Pw_congr (T_pw n (w n 3) (QB3 n n) (fun t => B4 n t) (fun t => C4 n t) (fun t => D4 n t)
      (fun s => QB4 n s) (fun s => QC4 n s) (fun s => QD4 n s) (pw4 n)
      (tB4 n) (tC4 n) (tD4 n))
    rfl
    (fun t => by simp only [QB3, QB4, QC4, B4, B5]; push_cast; ring)
    (fun t => by simp only [QB4, QC4, QD4, C4, C5]; push_cast; ring)
    (fun t => by simp only [QC4, QD4, D4, D5]; ring)

theorem pw6 (n : ℕ) :
    Pw n (w n 5) (QB5 n n) (fun t => B6 n t) (fun t => C6 n t) (fun t => D6 n t) :=
  Pw_congr (T_pw n (w n 4) (QB4 n n) (fun t => B5 n t) (fun t => C5 n t) (fun t => D5 n t)
      (fun s => QB5 n s) (fun s => QC5 n s) (fun s => QD5 n s) (pw5 n)
      (tB5 n) (tC5 n) (tD5 n))
    rfl
    (fun t => by simp only [QB4, QB5, QC5, B5, B6]; push_cast; ring)
    (fun t => by simp only [QB5, QC5, QD5, C5, C6]; push_cast; ring)
    (fun t => by simp only [QC5, QD5, D5, D6]; ring)

/-- The closed form, for every `n` (including `n = 0`, where both sides are 0). -/
theorem a_formula (n : ℕ) : (a n : ℚ) =
    841 / 180 * (n : ℚ) ^ 6 - 1 / 3 * (n : ℚ) ^ 5 - 19 / 36 * (n : ℚ) ^ 4 + 1 / 3 * (n : ℚ) ^ 3 -
      103 / 90 * (n : ℚ) ^ 2 - 3 * n := by
  obtain ⟨h0, h1, -, -⟩ := pw6 n
  rw [a_eq_w, show w n 6 0 = T n (w n 5) 0 from rfl,
    T_zero n (w n 5) (QB5 n n) (fun t => B6 n t) (fun s => QB6 n s) h0 h1 (tB6 n)]
  simp only [QB6]
  ring

theorem recurrence (n : ℕ) (hn : 7 < n) :
    (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) +
      21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  have hQ : (a n : ℚ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) +
      21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    rw [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega,
      show k + 8 - 3 = k + 5 by omega, show k + 8 - 4 = k + 4 by omega,
      show k + 8 - 5 = k + 3 by omega, show k + 8 - 6 = k + 2 by omega,
      show k + 8 - 7 = k + 1 by omega]
    rw [a_formula (k + 8), a_formula (k + 7), a_formula (k + 6), a_formula (k + 5),
      a_formula (k + 4), a_formula (k + 3), a_formula (k + 2), a_formula (k + 1)]
    push_cast
    ring
  exact_mod_cast hQ

open PowerSeries in
/-- The coefficient of `x^k` in `A * (c x^j)`. -/
theorem coeff_mul_CX (A : ℚ⟦X⟧) (c : ℚ) (j k : ℕ) :
    coeff k (A * (C c * X ^ j)) = if j ≤ k then c * coeff (k - j) A else 0 := by
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow', mul_ite, mul_zero]

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      2 * X ^ 2 * (136 + 684 * X + 730 * X ^ 2 + 129 * X ^ 3 + 3 * X ^ 4) := by
  have ha0 : ∀ m : ℕ, (if m = 0 then (0 : ℚ) else (a m : ℚ)) = a m := by
    intro m
    split_ifs with hm
    · subst hm
      rw [a_formula]
      simp
    · rfl
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have hpow : A * ((1 : ℚ⟦X⟧) - X) ^ 7 =
      A * (C (1 : ℚ) * X ^ 0) - A * (C (7 : ℚ) * X ^ 1) + A * (C (21 : ℚ) * X ^ 2) -
        A * (C (35 : ℚ) * X ^ 3) + A * (C (35 : ℚ) * X ^ 4) - A * (C (21 : ℚ) * X ^ 5) +
        A * (C (7 : ℚ) * X ^ 6) - A * (C (1 : ℚ) * X ^ 7) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (2 : ℚ⟦X⟧) * X ^ 2 * (136 + 684 * X + 730 * X ^ 2 + 129 * X ^ 3 + 3 * X ^ 4) =
      C (272 : ℚ) * X ^ 2 + C (1368 : ℚ) * X ^ 3 + C (1460 : ℚ) * X ^ 4 + C (258 : ℚ) * X ^ 5 +
        C (6 : ℚ) * X ^ 6 := by
    simp only [map_ofNat]
    ring
  rw [hpow, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow, coeff_mul_CX, hA, coeff_mk, ha0, zero_le,
    if_true, Nat.sub_zero, one_mul]
  have h0 : (a 0 : ℚ) = 0 := by rw [a_formula]; norm_num
  have h1 : (a 1 : ℚ) = 0 := by rw [a_formula]; norm_num
  have h2 : (a 2 : ℚ) = 272 := by rw [a_formula]; norm_num
  have h3 : (a 3 : ℚ) = 3272 := by rw [a_formula]; norm_num
  have h4 : (a 4 : ℚ) = 18652 := by rw [a_formula]; norm_num
  have h5 : (a 5 : ℚ) = 71630 := by rw [a_formula]; norm_num
  have h6 : (a 6 : ℚ) = 214724 := by rw [a_formula]; norm_num
  rcases k with _ | _ | _ | _ | _ | _ | _ | j
  · norm_num [h0]
  · norm_num [h0, h1]
  · norm_num [h0, h1, h2]
  · norm_num [h0, h1, h2, h3]
  · norm_num [h0, h1, h2, h3, h4]
  · norm_num [h0, h1, h2, h3, h4, h5]
  · norm_num [h0, h1, h2, h3, h4, h5, h6]
  · simp only [show 1 ≤ j + 7 by omega, show 2 ≤ j + 7 by omega, show 3 ≤ j + 7 by omega,
      show 4 ≤ j + 7 by omega, show 5 ≤ j + 7 by omega, show 6 ≤ j + 7 by omega,
      show 7 ≤ j + 7 by omega, show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega,
      show j + 7 - 3 = j + 4 by omega, show j + 7 - 4 = j + 3 by omega,
      show j + 7 - 5 = j + 2 by omega, show j + 7 - 6 = j + 1 by omega,
      show j + 7 - 7 = j by omega, show ¬ (j + 7 = 2) by omega, show ¬ (j + 7 = 3) by omega,
      show ¬ (j + 7 = 4) by omega, show ¬ (j + 7 = 5) by omega, show ¬ (j + 7 = 6) by omega,
      if_true, if_false]
    rw [a_formula (j + 7), a_formula (j + 6), a_formula (j + 5), a_formula (j + 4),
      a_formula (j + 3), a_formula (j + 2), a_formula (j + 1), a_formula j]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a205345.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
