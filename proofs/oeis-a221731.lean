import OMAStatements.S_oeis_a221731

/-!
Proof of Barker's g.f. and closed form for A221731 (n X 2 occupancy arrays after moves to
horizontal or antidiagonal neighbours, without move-in move-out left turns).

Positions. The cell `(i, j)` gets the position `cpos = 2 i + j`. The allowed moves are exactly
the moves to the same, the next or the previous position (`allowed_iff`), and two consecutive
moves `c → d → e` to neighbours form a left turn exactly for a rightward chain through a cell of
column 0 or a leftward chain through a cell of column 1 (`leftTurn_iff`).

Flows. For a map `m`, `netFlow m k` is the number of elements crossing the cut between the
positions `k - 1` and `k` to the right minus the number crossing it to the left. For a local
map the occupancy of `x` is `1 + netFlow m (cpos x) - netFlow m (cpos x + 1)` (`occ_eq`).
The flow of a valid map is a word `F` with values in {-1, 0, 1}, zero outside the cuts
`1 .. 2 n - 1`, such that no cut with flow -1 is followed by a cut with flow 1, no even position
has flow 1 on both sides and no odd position has flow -1 on both sides (`FlowOK`,
`flowOK_of_valid`). Conversely every such word is the flow of a valid map, the canonical move
`canon F` in which no two elements exchange cells (`canon_valid`, `netFlow_canon`), and the
occupancy array determines the flow word (`occF_inj`). So `a n` is the number of words of rows
`Fin n → Fin 3 × Fin 3` (the codes of the flows on the right of the two cells of each row) whose
flow word satisfies `FlowOK` (`a_eq_card`).

Counting. These are the words in which a row with horizontal flow -1 has antidiagonal flow 0, a
row followed by a row with horizontal flow 1 has antidiagonal flow 0, and the last row has
antidiagonal flow 0 (`vwp_iff`). Splitting off the first row gives
`tot (k + 1) = 3 tot k + 4 totU k` and `totU (k + 1) = 2 tot k + 2 totU k` with `tot 0 = 3`,
`totU 0 = 2`, where `tot k = a (k + 1)` and `totU k` counts the words whose first row has
horizontal flow different from 1. Hence `a 1 = 3`, `a 2 = 17` and
`a (n + 2) = 5 a (n + 1) + 2 a n` for `n ≥ 1`, which gives the g.f. and, by induction with
`(5 ± √33)^2 = 10 (5 ± √33) + 8`, the closed form.
-/

namespace OMA.Helpers

open OMA.S_oeis_a221731 Finset

/-- `1` if `p` holds, `0` otherwise (as an integer). -/
def indZ (p : Prop) [Decidable p] : ℤ := if p then 1 else 0

/-- The position `2 i + j` of the cell `(i, j)` on the path `(0,0), (0,1), (1,0), (1,1), ...`. -/
def cpos {n : ℕ} (c : Cell n) : ℕ := 2 * c.1.val + c.2.val

theorem cpos_lt {n : ℕ} (c : Cell n) : cpos c < 2 * n := by
  unfold cpos
  have := c.1.isLt
  have := c.2.isLt
  omega

theorem cpos_inj {n : ℕ} {c d : Cell n} (h : cpos c = cpos d) : c = d := by
  unfold cpos at h
  have := c.2.isLt
  have := d.2.isLt
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem cpos_mod {n : ℕ} (c : Cell n) : cpos c % 2 = c.2.val := by
  unfold cpos
  have := c.2.isLt
  omega

/-- The cell at position `p < 2 n`. -/
def cellOf {n : ℕ} (p : ℕ) (h : p < 2 * n) : Cell n :=
  (⟨p / 2, by omega⟩, ⟨p % 2, by omega⟩)

theorem cpos_cellOf {n : ℕ} (p : ℕ) (h : p < 2 * n) : cpos (cellOf p h) = p := by
  unfold cpos cellOf
  simp only
  omega

theorem sum_indZ_unique {α : Type*} [Fintype α] (A : α → Prop) [DecidablePred A]
    (h : ∀ x y, A x → A y → x = y) :
    (∑ x, indZ (A x)) = if ∃ x, A x then 1 else 0 := by
  split_ifs with hex
  · obtain ⟨x0, hx0⟩ := hex
    rw [Fintype.sum_eq_single x0]
    · simp [indZ, hx0]
    · intro y hy
      simp only [indZ]
      rw [if_neg]
      intro hAy
      exact hy (h y x0 hAy hx0)
  · apply Finset.sum_eq_zero
    intro x _
    simp only [indZ]
    rw [if_neg]
    intro hx
    exact hex ⟨x, hx⟩

theorem sum_indZ_cpos {n : ℕ} (p : ℕ) :
    (∑ c : Cell n, indZ (cpos c = p)) = if p < 2 * n then 1 else 0 := by
  rw [sum_indZ_unique (fun c : Cell n => cpos c = p) (fun x y hx hy => cpos_inj (hx.trans hy.symm))]
  by_cases hp : p < 2 * n
  · rw [if_pos ⟨cellOf p hp, cpos_cellOf p hp⟩, if_pos hp]
  · rw [if_neg, if_neg hp]
    rintro ⟨c, hc⟩
    have := cpos_lt c
    omega

/-- The allowed moves are exactly the moves to the same, the next or the previous position. -/
theorem allowed_iff {n : ℕ} (c d : Cell n) :
    (d = c ∨ IsHorizontalNbr c d ∨ IsAntidiagonalNbr c d) ↔
      (cpos d = cpos c ∨ cpos d = cpos c + 1 ∨ cpos d + 1 = cpos c) := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := c
  obtain ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ := d
  simp only [IsHorizontalNbr, IsAntidiagonalNbr, dr, dc, cpos, Prod.mk.injEq, Fin.mk.injEq]
  omega

/-- The four kinds of moves to a neighbour. -/
theorem nbr_cases {n : ℕ} (c d : Cell n) (h : cpos d = cpos c + 1 ∨ cpos d + 1 = cpos c) :
    (dr c d = 0 ∧ dc c d = 1 ∧ c.2.val = 0 ∧ d.2.val = 1 ∧ cpos d = cpos c + 1) ∨
    (dr c d = 1 ∧ dc c d = -1 ∧ c.2.val = 1 ∧ d.2.val = 0 ∧ cpos d = cpos c + 1) ∨
    (dr c d = 0 ∧ dc c d = -1 ∧ c.2.val = 1 ∧ d.2.val = 0 ∧ cpos d + 1 = cpos c) ∨
    (dr c d = -1 ∧ dc c d = 1 ∧ c.2.val = 0 ∧ d.2.val = 1 ∧ cpos d + 1 = cpos c) := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := c
  obtain ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ := d
  simp only [dr, dc, cpos] at h ⊢
  omega

/-- Left turns of two moves to neighbours, in terms of positions: a rightward chain through a
cell of column 0, or a leftward chain through a cell of column 1. -/
theorem leftTurn_iff {n : ℕ} (c d e : Cell n) (h1 : cpos d = cpos c + 1 ∨ cpos d + 1 = cpos c)
    (h2 : cpos e = cpos d + 1 ∨ cpos e + 1 = cpos d) :
    LeftTurn c d e ↔ (cpos d = cpos c + 1 ∧ cpos e = cpos d + 1 ∧ d.2.val = 0) ∨
      (cpos d + 1 = cpos c ∧ cpos e + 1 = cpos d ∧ d.2.val = 1) := by
  rcases nbr_cases c d h1 with ⟨a1, b1, s1, t1, p1⟩ | ⟨a1, b1, s1, t1, p1⟩ |
      ⟨a1, b1, s1, t1, p1⟩ | ⟨a1, b1, s1, t1, p1⟩ <;>
    rcases nbr_cases d e h2 with ⟨a2, b2, s2, t2, p2⟩ | ⟨a2, b2, s2, t2, p2⟩ |
      ⟨a2, b2, s2, t2, p2⟩ | ⟨a2, b2, s2, t2, p2⟩ <;>
    simp only [LeftTurn, a1, b1, a2, b2] <;> norm_num <;> omega

/-- Each element moves to the same, the next or the previous position. -/
def Loc {n : ℕ} (m : Cell n → Cell n) : Prop :=
  ∀ c, cpos (m c) = cpos c ∨ cpos (m c) = cpos c + 1 ∨ cpos (m c) + 1 = cpos c

theorem loc_of_valid {n : ℕ} {m : Cell n → Cell n} (h : Valid m) : Loc m :=
  fun c => (allowed_iff c (m c)).1 (h.1 c)

/-- The number of elements crossing the cut `k` (between positions `k - 1` and `k`) to the
right. -/
def rightCross {n : ℕ} (m : Cell n → Cell n) (k : ℕ) : ℤ :=
  ∑ c, indZ (cpos c + 1 = k ∧ cpos (m c) = k)

/-- The number of elements crossing the cut `k` to the left. -/
def leftCross {n : ℕ} (m : Cell n → Cell n) (k : ℕ) : ℤ :=
  ∑ c, indZ (cpos c = k ∧ cpos (m c) + 1 = k)

/-- The net flow of elements across the cut `k`, to the right. -/
def netFlow {n : ℕ} (m : Cell n → Cell n) (k : ℕ) : ℤ := rightCross m k - leftCross m k

theorem point_identity {n : ℕ} (m : Cell n → Cell n) (c : Cell n)
    (hc : cpos (m c) = cpos c ∨ cpos (m c) = cpos c + 1 ∨ cpos (m c) + 1 = cpos c) (p : ℕ) :
    indZ (cpos (m c) = p) = indZ (cpos c = p) -
      indZ (cpos c + 1 = p + 1 ∧ cpos (m c) = p + 1) +
      indZ (cpos c = p + 1 ∧ cpos (m c) + 1 = p + 1) +
      indZ (cpos c + 1 = p ∧ cpos (m c) = p) - indZ (cpos c = p ∧ cpos (m c) + 1 = p) := by
  simp only [indZ]
  split_ifs <;> omega

theorem occ_eq {n : ℕ} {m : Cell n → Cell n} (hm : Loc m) (x : Cell n) :
    (occ m x : ℤ) = 1 + netFlow m (cpos x) - netFlow m (cpos x + 1) := by
  have h1 : (occ m x : ℤ) = ∑ c, indZ (cpos (m c) = cpos x) := by
    unfold occ
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro c _
    unfold indZ
    by_cases h : m c = x
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (cpos_inj h'))]
  rw [h1, Finset.sum_congr rfl (fun c _ => point_identity m c (hm c) (cpos x))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_indZ_cpos, if_pos (cpos_lt x)]
  unfold netFlow rightCross leftCross
  ring

theorem rightCross_eq {n : ℕ} (m : Cell n → Cell n) (k : ℕ) :
    rightCross m k = if ∃ c, cpos c + 1 = k ∧ cpos (m c) = k then 1 else 0 :=
  sum_indZ_unique _ (fun x y hx hy => cpos_inj (by omega))

theorem leftCross_eq {n : ℕ} (m : Cell n → Cell n) (k : ℕ) :
    leftCross m k = if ∃ c, cpos c = k ∧ cpos (m c) + 1 = k then 1 else 0 :=
  sum_indZ_unique _ (fun x y hx hy => cpos_inj (by omega))

theorem netFlow_range {n : ℕ} (m : Cell n → Cell n) (k : ℕ) :
    netFlow m k = -1 ∨ netFlow m k = 0 ∨ netFlow m k = 1 := by
  unfold netFlow
  rw [rightCross_eq, leftCross_eq]
  split_ifs <;> norm_num

theorem netFlow_pos {n : ℕ} {m : Cell n → Cell n} {k : ℕ} (h : netFlow m k = 1) :
    ∃ c, cpos c + 1 = k ∧ cpos (m c) = k := by
  unfold netFlow at h
  rw [rightCross_eq, leftCross_eq] at h
  split_ifs at h <;> first | assumption | norm_num at h

theorem netFlow_neg {n : ℕ} {m : Cell n → Cell n} {k : ℕ} (h : netFlow m k = -1) :
    ∃ c, cpos c = k ∧ cpos (m c) + 1 = k := by
  unfold netFlow at h
  rw [rightCross_eq, leftCross_eq] at h
  split_ifs at h <;> first | assumption | norm_num at h

theorem netFlow_zero {n : ℕ} (m : Cell n → Cell n) : netFlow m 0 = 0 := by
  unfold netFlow
  rw [rightCross_eq, leftCross_eq, if_neg, if_neg]
  · norm_num
  · rintro ⟨c, -, hc⟩
    omega
  · rintro ⟨c, hc, -⟩
    omega

theorem netFlow_big {n : ℕ} (m : Cell n → Cell n) (k : ℕ) (hk : 2 * n ≤ k) :
    netFlow m k = 0 := by
  unfold netFlow
  rw [rightCross_eq, leftCross_eq, if_neg, if_neg]
  · norm_num
  · rintro ⟨c, hc, -⟩
    have := cpos_lt c
    omega
  · rintro ⟨c, -, hc⟩
    have := cpos_lt (m c)
    omega

/-- The conditions on a flow word. -/
def FlowOK (n : ℕ) (F : ℕ → ℤ) : Prop :=
  F 0 = 0 ∧ (∀ k, 2 * n ≤ k → F k = 0) ∧ (∀ k, F k = -1 ∨ F k = 0 ∨ F k = 1) ∧
    (∀ k, ¬ (F k = -1 ∧ F (k + 1) = 1)) ∧
    (∀ k, k % 2 = 0 → ¬ (F k = 1 ∧ F (k + 1) = 1)) ∧
    (∀ k, k % 2 = 1 → ¬ (F k = -1 ∧ F (k + 1) = -1))

theorem flowOK_of_valid {n : ℕ} {m : Cell n → Cell n} (hv : Valid m) :
    FlowOK n (netFlow m) := by
  refine ⟨netFlow_zero m, netFlow_big m, netFlow_range m, ?_, ?_, ?_⟩
  · rintro k ⟨h1, h2⟩
    obtain ⟨c, hc1, hc2⟩ := netFlow_neg h1
    obtain ⟨d, hd1, hd2⟩ := netFlow_pos h2
    have hcd : c = d := cpos_inj (by omega)
    subst hcd
    omega
  · rintro k hk ⟨h1, h2⟩
    obtain ⟨c, hc1, hc2⟩ := netFlow_pos h1
    obtain ⟨d, hd1, hd2⟩ := netFlow_pos h2
    have hdm : m c = d := cpos_inj (by omega)
    have hne1 : m c ≠ c := fun h => by rw [h] at hc2; omega
    have hne2 : m (m c) ≠ m c := fun h => by rw [hdm] at h; rw [h] at hd2; omega
    apply hv.2 c hne1 hne2
    have hp := cpos_mod (m c)
    rw [leftTurn_iff c (m c) (m (m c)) (Or.inl (by omega)) (Or.inl (by rw [hdm]; omega))]
    left
    exact ⟨by omega, by rw [hdm]; omega, by omega⟩
  · rintro k hk ⟨h1, h2⟩
    obtain ⟨c, hc1, hc2⟩ := netFlow_neg h1
    obtain ⟨d, hd1, hd2⟩ := netFlow_neg h2
    have hdm : m d = c := cpos_inj (by omega)
    have hne1 : m d ≠ d := fun h => by rw [h] at hd2; omega
    have hne2 : m (m d) ≠ m d := fun h => by rw [hdm] at h; rw [h] at hc2; omega
    apply hv.2 d hne1 hne2
    have hp := cpos_mod (m d)
    rw [leftTurn_iff d (m d) (m (m d)) (Or.inr (by omega)) (Or.inr (by rw [hdm]; omega))]
    right
    exact ⟨by omega, by rw [hdm]; omega, by omega⟩

/-- The target position of the element at position `p` in the canonical move of the flow word
`F`: one step right if the flow on its right is `1`, one step left if the flow on its left is
`-1`, otherwise it stays. -/
def ctgt (F : ℕ → ℤ) (p : ℕ) : ℕ :=
  if F (p + 1) = 1 then p + 1 else if F p = -1 then p - 1 else p

/-- The canonical move of the flow word `F`. -/
def canon {n : ℕ} (F : ℕ → ℤ) (c : Cell n) : Cell n :=
  if h : ctgt F (cpos c) < 2 * n then cellOf (ctgt F (cpos c)) h else c

theorem ctgt_cases (F : ℕ → ℤ) (p : ℕ) (h0 : F 0 = 0) :
    (ctgt F p = p + 1 ∧ F (p + 1) = 1) ∨ (ctgt F p + 1 = p ∧ F (p + 1) ≠ 1 ∧ F p = -1) ∨
      (ctgt F p = p ∧ F (p + 1) ≠ 1 ∧ F p ≠ -1) := by
  unfold ctgt
  by_cases h1 : F (p + 1) = 1
  · left
    exact ⟨if_pos h1, h1⟩
  · by_cases h2 : F p = -1
    · right; left
      have hp : p ≠ 0 := by
        rintro rfl
        rw [h0] at h2
        norm_num at h2
      rw [if_neg h1, if_pos h2]
      exact ⟨by omega, h1, h2⟩
    · right; right
      rw [if_neg h1, if_neg h2]
      exact ⟨rfl, h1, h2⟩

theorem ctgt_lt {n : ℕ} {F : ℕ → ℤ} (hF : FlowOK n F) (c : Cell n) :
    ctgt F (cpos c) < 2 * n := by
  have h1 := cpos_lt c
  have h2 := hF.2.1 (2 * n) le_rfl
  rcases ctgt_cases F (cpos c) hF.1 with ⟨h, h'⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
  · rw [h]
    by_contra hc
    have he : cpos c + 1 = 2 * n := by omega
    rw [he] at h'
    omega
  · omega
  · omega

theorem cpos_canon {n : ℕ} {F : ℕ → ℤ} (hF : FlowOK n F) (c : Cell n) :
    cpos (canon F c) = ctgt F (cpos c) := by
  unfold canon
  rw [dif_pos (ctgt_lt hF c), cpos_cellOf]

theorem canon_valid {n : ℕ} {F : ℕ → ℤ} (hF : FlowOK n F) : Valid (canon (n := n) F) := by
  have hloc : ∀ c : Cell n, cpos (canon F c) = cpos c ∨ cpos (canon F c) = cpos c + 1 ∨
      cpos (canon F c) + 1 = cpos c := by
    intro c
    rw [cpos_canon hF]
    rcases ctgt_cases F (cpos c) hF.1 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  refine ⟨fun c => (allowed_iff c (canon F c)).2 (hloc c), ?_⟩
  intro c hne1 hne2 hlt
  have hp1 : cpos (canon F c) = cpos c + 1 ∨ cpos (canon F c) + 1 = cpos c := by
    rcases hloc c with h | h | h
    · exact absurd (cpos_inj h) hne1
    · exact Or.inl h
    · exact Or.inr h
  have hp2 : cpos (canon F (canon F c)) = cpos (canon F c) + 1 ∨
      cpos (canon F (canon F c)) + 1 = cpos (canon F c) := by
    rcases hloc (canon F c) with h | h | h
    · exact absurd (cpos_inj h) hne2
    · exact Or.inl h
    · exact Or.inr h
  rw [leftTurn_iff c _ _ hp1 hp2] at hlt
  have hmod := cpos_mod (canon F c)
  have q1 := cpos_canon hF c
  have q2 := cpos_canon hF (canon F c)
  rcases hlt with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
  · have f1 : F (cpos (canon F c)) = 1 := by
      rcases ctgt_cases F (cpos c) hF.1 with ⟨h, h'⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
      · rw [e1]
        exact h'
      · omega
      · omega
    have f2 : F (cpos (canon F c) + 1) = 1 := by
      rcases ctgt_cases F (cpos (canon F c)) hF.1 with ⟨h, h'⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
      · exact h'
      · omega
      · omega
    exact hF.2.2.2.2.1 _ (by omega) ⟨f1, f2⟩
  · have f1 : F (cpos (canon F c) + 1) = -1 := by
      rcases ctgt_cases F (cpos c) hF.1 with ⟨h, -⟩ | ⟨h, -, h'⟩ | ⟨h, -, -⟩
      · omega
      · rw [e1]
        exact h'
      · omega
    have f2 : F (cpos (canon F c)) = -1 := by
      rcases ctgt_cases F (cpos (canon F c)) hF.1 with ⟨h, -⟩ | ⟨h, -, h'⟩ | ⟨h, -, -⟩
      · omega
      · exact h'
      · omega
    exact hF.2.2.2.2.2 _ (by omega) ⟨f2, f1⟩

theorem netFlow_canon {n : ℕ} {F : ℕ → ℤ} (hF : FlowOK n F) :
    netFlow (canon (n := n) F) = F := by
  funext k
  unfold netFlow
  rw [rightCross_eq, leftCross_eq]
  have h0 := hF.1
  have hbig := hF.2.1
  have hr := hF.2.2.1
  have h2 := hF.2.2.2.1
  have e1 : (∃ c : Cell n, cpos c + 1 = k ∧ cpos (canon F c) = k) ↔
      (1 ≤ k ∧ k ≤ 2 * n ∧ F k = 1) := by
    constructor
    · rintro ⟨c, hc1, hc2⟩
      have := cpos_lt c
      rw [cpos_canon hF] at hc2
      rcases ctgt_cases F (cpos c) h0 with ⟨h, h'⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
      · exact ⟨by omega, by omega, by rw [← hc1]; exact h'⟩
      · omega
      · omega
    · rintro ⟨hk1, hk2, hk3⟩
      refine ⟨cellOf (k - 1) (by omega), by rw [cpos_cellOf]; omega, ?_⟩
      rw [cpos_canon hF, cpos_cellOf]
      unfold ctgt
      rw [if_pos (by rw [show k - 1 + 1 = k by omega]; exact hk3)]
      omega
  have e2 : (∃ c : Cell n, cpos c = k ∧ cpos (canon F c) + 1 = k) ↔
      (k < 2 * n ∧ F k = -1) := by
    constructor
    · rintro ⟨c, hc1, hc2⟩
      have := cpos_lt c
      rw [cpos_canon hF] at hc2
      rcases ctgt_cases F (cpos c) h0 with ⟨h, -⟩ | ⟨h, -, h'⟩ | ⟨h, -, -⟩
      · omega
      · exact ⟨by omega, by rw [← hc1]; exact h'⟩
      · omega
    · rintro ⟨hk1, hk2⟩
      refine ⟨cellOf k hk1, cpos_cellOf k hk1, ?_⟩
      rw [cpos_canon hF, cpos_cellOf]
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [h0] at hk2
        norm_num at hk2
      have h3 : F (k + 1) ≠ 1 := fun h => h2 k ⟨hk2, h⟩
      unfold ctgt
      rw [if_neg h3, if_pos hk2]
      omega
  rw [if_congr e1 rfl rfl, if_congr e2 rfl rfl]
  have hk0 : k = 0 → F k = 0 := fun h => h ▸ h0
  have hkb : 2 * n ≤ k → F k = 0 := hbig k
  have hrk := hr k
  split_ifs <;> omega

/-- The occupancy array of a flow word. -/
def occF {n : ℕ} (F : ℕ → ℤ) (x : Cell n) : ℕ := (1 + F (cpos x) - F (cpos x + 1)).toNat

theorem occF_nonneg {n : ℕ} {F : ℕ → ℤ} (hF : FlowOK n F) (p : ℕ) :
    0 ≤ 1 + F p - F (p + 1) := by
  have := hF.2.2.1 p
  have := hF.2.2.1 (p + 1)
  have := hF.2.2.2.1 p
  omega

theorem occF_inj {n : ℕ} {F G : ℕ → ℤ} (hF : FlowOK n F) (hG : FlowOK n G)
    (h : occF (n := n) F = occF G) : F = G := by
  have key : ∀ p, p < 2 * n → F (p + 1) - F p = G (p + 1) - G p := by
    intro p hp
    have h1 := congrFun h (cellOf p hp)
    unfold occF at h1
    rw [cpos_cellOf] at h1
    have e1 := Int.toNat_of_nonneg (occF_nonneg hF p)
    have e2 := Int.toNat_of_nonneg (occF_nonneg hG p)
    rw [h1] at e1
    linarith
  have h2 : ∀ p, p ≤ 2 * n → F p = G p := by
    intro p
    induction p with
    | zero => intro _; rw [hF.1, hG.1]
    | succ p ih =>
      intro hp
      have := key p (by omega)
      have := ih (by omega)
      linarith
  funext p
  by_cases hp : p ≤ 2 * n
  · exact h2 p hp
  · rw [hF.2.1 p (by omega), hG.2.1 p (by omega)]

/-- A row of a flow word: the codes of the flows on the right of the cells `(i, 0)` and `(i, 1)`
(code `v` stands for the flow `v - 1`). -/
abbrev Letter := Fin 3 × Fin 3

/-- The flow with code `v`. -/
def dec (v : Fin 3) : ℤ := (v.val : ℤ) - 1

/-- The code of the flow `z`. -/
def enc (z : ℤ) : Fin 3 := if z = -1 then 0 else if z = 0 then 1 else 2

theorem enc_dec (v : Fin 3) : enc (dec v) = v := by
  fin_cases v <;> rfl

theorem dec_enc (z : ℤ) (h : z = -1 ∨ z = 0 ∨ z = 1) : dec (enc z) = z := by
  rcases h with rfl | rfl | rfl <;> rfl

/-- The code at column `j` of a row. -/
def codeAt (l : Letter) (j : ℕ) : Fin 3 := if j = 0 then l.1 else l.2

/-- The flow word of a word of rows: the flow on the right of the cell `c` is the code at `c`. -/
def Fw {n : ℕ} (w : Fin n → Letter) (k : ℕ) : ℤ :=
  ∑ c : Cell n, if cpos c + 1 = k then dec (codeAt (w c.1) c.2.val) else 0

theorem Fw_cell {n : ℕ} (w : Fin n → Letter) (c : Cell n) :
    Fw w (cpos c + 1) = dec (codeAt (w c.1) c.2.val) := by
  unfold Fw
  rw [Fintype.sum_eq_single c (fun d hd => if_neg (fun h => hd (cpos_inj (by omega))))]
  exact if_pos rfl

theorem Fw_out {n : ℕ} (w : Fin n → Letter) (k : ℕ) (h : ∀ c : Cell n, cpos c + 1 ≠ k) :
    Fw w k = 0 :=
  Finset.sum_eq_zero (fun c _ => if_neg (h c))

theorem Fw_zero {n : ℕ} (w : Fin n → Letter) : Fw w 0 = 0 :=
  Fw_out w 0 (fun c => by omega)

theorem Fw_big {n : ℕ} (w : Fin n → Letter) (k : ℕ) (hk : 2 * n < k) : Fw w k = 0 :=
  Fw_out w k (fun c => by have := cpos_lt c; omega)

theorem Fw_h {n : ℕ} (w : Fin n → Letter) (i : ℕ) (hi : i < n) :
    Fw w (2 * i + 1) = dec (w ⟨i, hi⟩).1 := by
  have h := Fw_cell w (⟨i, hi⟩, 0)
  simpa [cpos, codeAt] using h

theorem Fw_g {n : ℕ} (w : Fin n → Letter) (i : ℕ) (hi : i < n) :
    Fw w (2 * i + 2) = dec (w ⟨i, hi⟩).2 := by
  have h := Fw_cell w (⟨i, hi⟩, 1)
  simpa [cpos, codeAt] using h

theorem k_cases (n k : ℕ) :
    k = 0 ∨ (∃ i, i < n ∧ k = 2 * i + 1) ∨ (∃ i, i < n ∧ k = 2 * i + 2) ∨
      2 * n < k := by
  by_cases h0 : k = 0
  · exact Or.inl h0
  · by_cases hb : 2 * n < k
    · exact Or.inr (Or.inr (Or.inr hb))
    · by_cases hp : k % 2 = 1
      · exact Or.inr (Or.inl ⟨(k - 1) / 2, by omega, by omega⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨(k - 2) / 2, by omega, by omega⟩))

theorem dec_range (v : Fin 3) : dec v = -1 ∨ dec v = 0 ∨ dec v = 1 := by
  unfold dec
  have := v.isLt
  omega

theorem Fw_range {n : ℕ} (w : Fin n → Letter) (k : ℕ) :
    Fw w k = -1 ∨ Fw w k = 0 ∨ Fw w k = 1 := by
  rcases k_cases n k with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | hk
  · rw [Fw_zero]
    norm_num
  · rw [Fw_h w i hi]
    exact dec_range _
  · rw [Fw_g w i hi]
    exact dec_range _
  · rw [Fw_big w k hk]
    norm_num

/-- The word of rows of a flow word. -/
def wordOf {n : ℕ} (F : ℕ → ℤ) : Fin n → Letter :=
  fun i => (enc (F (2 * i.val + 1)), enc (F (2 * i.val + 2)))

theorem Fw_wordOf {n : ℕ} {F : ℕ → ℤ} (h0 : F 0 = 0) (hbig : ∀ k, 2 * n ≤ k → F k = 0)
    (hr : ∀ k, F k = -1 ∨ F k = 0 ∨ F k = 1) : Fw (wordOf (n := n) F) = F := by
  funext k
  rcases k_cases n k with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | hk
  · rw [Fw_zero, h0]
  · rw [Fw_h _ i hi]
    exact dec_enc _ (hr _)
  · rw [Fw_g _ i hi]
    exact dec_enc _ (hr _)
  · rw [Fw_big _ k hk, hbig k (by omega)]

theorem wordOf_Fw {n : ℕ} (w : Fin n → Letter) : wordOf (Fw w) = w := by
  funext i
  unfold wordOf
  rw [Fw_h w i.val i.isLt, Fw_g w i.val i.isLt, enc_dec, enc_dec]

/-- The valid words of rows: those whose flow word satisfies the conditions. -/
def VWp {n : ℕ} (w : Fin n → Letter) : Prop := FlowOK n (Fw w)

theorem occ_image_eq (n : ℕ) [DecidablePred (fun m : Cell n → Cell n => Valid m)]
    [DecidablePred (fun w : Fin n → Letter => VWp w)] [DecidableEq (Cell n → ℕ)] :
    (univ.filter (fun m : Cell n → Cell n => Valid m)).image occ =
      (univ.filter (fun w : Fin n → Letter => VWp w)).image (fun w => occF (Fw w)) := by
  ext o
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨m, hv, rfl⟩
    have hF := flowOK_of_valid hv
    have hw : Fw (wordOf (n := n) (netFlow m)) = netFlow m := Fw_wordOf hF.1 hF.2.1 hF.2.2.1
    refine ⟨wordOf (netFlow m), ?_, ?_⟩
    · unfold VWp
      rw [hw]
      exact hF
    · rw [hw]
      funext x
      unfold occF
      rw [← occ_eq (loc_of_valid hv) x, Int.toNat_natCast]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨canon (Fw w), canon_valid hw, ?_⟩
    funext x
    have h1 := occ_eq (loc_of_valid (canon_valid hw)) x
    rw [netFlow_canon hw] at h1
    unfold occF
    rw [← h1, Int.toNat_natCast]

theorem a_eq_card (n : ℕ) [DecidablePred (fun w : Fin n → Letter => VWp w)] :
    a n = (univ.filter (fun w : Fin n → Letter => VWp w)).card := by
  classical
  unfold a
  rw [occ_image_eq n]
  apply Finset.card_image_of_injOn
  intro w hw w' hw' h
  simp only [coe_filter, Finset.mem_univ, true_and] at hw hw'
  have := occF_inj hw hw' h
  rw [← wordOf_Fw w, ← wordOf_Fw w', this]

/-- A row with horizontal flow `-1` sends nothing along the antidiagonal below it. -/
def rowOK (l : Letter) : Prop := l.1.val = 0 → l.2.val = 1

/-- Nothing comes along the antidiagonal into a row with horizontal flow `1`. -/
def rowCompat (l l' : Letter) : Prop := l'.1.val = 2 → l.2.val = 1

/-- Nothing leaves the last row along an antidiagonal. -/
def endOK (l : Letter) : Prop := l.2.val = 1

/-- The row conditions of a valid word. -/
def RowsOK {k : ℕ} (w : Fin k → Letter) : Prop :=
  (∀ (i : ℕ) (hi : i < k), rowOK (w ⟨i, hi⟩)) ∧
    (∀ (i : ℕ) (hi : i + 1 < k), rowCompat (w ⟨i, by omega⟩) (w ⟨i + 1, hi⟩)) ∧
    (∀ (i : ℕ) (hi : i < k), i + 1 = k → endOK (w ⟨i, hi⟩))

theorem vwp_iff {n : ℕ} (w : Fin n → Letter) : VWp w ↔ RowsOK w := by
  constructor
  · intro hw
    obtain ⟨-, hbig, -, h2, h3, h4⟩ := hw
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi hin => ?_⟩
    · intro h
      have a2 := h2 (2 * i + 1)
      have a4 := h4 (2 * i + 1) (by omega)
      rw [Fw_h w i hi, show 2 * i + 1 + 1 = 2 * i + 2 by ring, Fw_g w i hi] at a2 a4
      have := (w ⟨i, hi⟩).2.isLt
      unfold dec at a2 a4
      omega
    · intro h
      have a2 := h2 (2 * i + 2)
      have a3 := h3 (2 * i + 2) (by omega)
      rw [Fw_g w i (by omega), show 2 * i + 2 + 1 = 2 * (i + 1) + 1 by ring,
        Fw_h w (i + 1) hi] at a2 a3
      have := (w ⟨i, by omega⟩).2.isLt
      unfold dec at a2 a3
      omega
    · have := hbig (2 * n) le_rfl
      rw [show 2 * n = 2 * i + 2 by omega, Fw_g w i hi] at this
      unfold endOK
      unfold dec at this
      omega
  · rintro ⟨hrow, hcomp, hend⟩
    have hbig : ∀ k, 2 * n ≤ k → Fw w k = 0 := by
      intro k hk
      rcases Nat.eq_or_lt_of_le hk with h | h
      · rw [← h]
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          exact Fw_zero w
        · rw [show 2 * n = 2 * (n - 1) + 2 by omega, Fw_g w (n - 1) (by omega)]
          have := hend (n - 1) (by omega) (by omega)
          unfold endOK at this
          unfold dec
          omega
      · exact Fw_big w k h
    refine ⟨Fw_zero w, hbig, Fw_range w, ?_, ?_, ?_⟩
    · rintro k ⟨h1, h2⟩
      rcases k_cases n k with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | hk
      · rw [Fw_zero] at h1
        norm_num at h1
      · rw [Fw_h w i hi] at h1
        rw [show 2 * i + 1 + 1 = 2 * i + 2 by ring, Fw_g w i hi] at h2
        have := hrow i hi
        unfold rowOK at this
        unfold dec at h1 h2
        omega
      · rw [Fw_g w i hi] at h1
        by_cases hi' : i + 1 < n
        · rw [show 2 * i + 2 + 1 = 2 * (i + 1) + 1 by ring, Fw_h w (i + 1) hi'] at h2
          have := hcomp i hi'
          unfold rowCompat at this
          unfold dec at h1 h2
          omega
        · rw [Fw_big w _ (by omega)] at h2
          norm_num at h2
      · rw [Fw_big w k hk] at h1
        norm_num at h1
    · rintro k hk ⟨h1, h2⟩
      rcases k_cases n k with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | hk'
      · rw [Fw_zero] at h1
        norm_num at h1
      · omega
      · rw [Fw_g w i hi] at h1
        by_cases hi' : i + 1 < n
        · rw [show 2 * i + 2 + 1 = 2 * (i + 1) + 1 by ring, Fw_h w (i + 1) hi'] at h2
          have := hcomp i hi'
          unfold rowCompat at this
          unfold dec at h1 h2
          omega
        · rw [Fw_big w _ (by omega)] at h2
          norm_num at h2
      · rw [Fw_big w k hk'] at h1
        norm_num at h1
    · rintro k hk ⟨h1, h2⟩
      rcases k_cases n k with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | hk'
      · omega
      · rw [Fw_h w i hi] at h1
        rw [show 2 * i + 1 + 1 = 2 * i + 2 by ring, Fw_g w i hi] at h2
        have := hrow i hi
        unfold rowOK at this
        unfold dec at h1 h2
        omega
      · omega
      · rw [Fw_big w k hk'] at h1
        norm_num at h1

theorem cons_mk_zero {k : ℕ} (r : Letter) (A : Fin k → Letter) (h : 0 < k + 1) :
    (Fin.cons r A : Fin (k + 1) → Letter) ⟨0, h⟩ = r := by
  have e : (⟨0, h⟩ : Fin (k + 1)) = 0 := Fin.ext (by simp)
  rw [e, Fin.cons_zero]

theorem cons_mk_succ {k : ℕ} (r : Letter) (A : Fin k → Letter) (i : ℕ) (h : i + 1 < k + 1) :
    (Fin.cons r A : Fin (k + 1) → Letter) ⟨i + 1, h⟩ = A ⟨i, by omega⟩ := by
  have e : (⟨i + 1, h⟩ : Fin (k + 1)) = Fin.succ ⟨i, Nat.lt_of_succ_lt_succ h⟩ :=
    Fin.ext (by simp)
  rw [e, Fin.cons_succ]

theorem rowsOK_one (r : Letter) (A : Fin 0 → Letter) :
    RowsOK (Fin.cons r A : Fin 1 → Letter) ↔ rowOK r ∧ endOK r := by
  constructor
  · rintro ⟨h1, -, h3⟩
    have e1 := h1 0 (by omega)
    have e3 := h3 0 (by omega) rfl
    rw [cons_mk_zero] at e1 e3
    exact ⟨e1, e3⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => absurd hi (by omega), fun i hi _ => ?_⟩
    · obtain rfl : i = 0 := by omega
      rw [cons_mk_zero]
      exact h1
    · obtain rfl : i = 0 := by omega
      rw [cons_mk_zero]
      exact h2

theorem rowsOK_cons {k : ℕ} (r : Letter) (A : Fin (k + 1) → Letter) :
    RowsOK (Fin.cons r A : Fin (k + 2) → Letter) ↔
      rowOK r ∧ rowCompat r (A ⟨0, by omega⟩) ∧ RowsOK A := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have e1 := h1 0 (by omega)
    have e2 := h2 0 (by omega)
    rw [cons_mk_zero] at e1 e2
    rw [cons_mk_succ] at e2
    refine ⟨e1, e2, fun i hi => ?_, fun i hi => ?_, fun i hi hik => ?_⟩
    · have := h1 (i + 1) (by omega)
      rwa [cons_mk_succ] at this
    · have := h2 (i + 1) (by omega)
      rwa [cons_mk_succ, cons_mk_succ] at this
    · have := h3 (i + 1) (by omega) (by omega)
      rwa [cons_mk_succ] at this
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi hik => ?_⟩
    · cases i with
      | zero =>
        rw [cons_mk_zero]
        exact h1
      | succ i =>
        rw [cons_mk_succ]
        exact h3 i (by omega)
    · cases i with
      | zero =>
        rw [cons_mk_zero, cons_mk_succ]
        exact h2
      | succ i =>
        rw [cons_mk_succ, cons_mk_succ]
        exact h4 i (by omega)
    · cases i with
      | zero => omega
      | succ i =>
        rw [cons_mk_succ]
        exact h5 i (by omega) (by omega)

/-- `1` if `p` holds, `0` otherwise (classically). -/
noncomputable def cind (p : Prop) : ℤ := by
  classical
  exact if p then 1 else 0

theorem cind_and (p q : Prop) : cind (p ∧ q) = cind p * cind q := by
  unfold cind
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem cind_congr {p q : Prop} (h : p ↔ q) : cind p = cind q := by
  rw [propext h]

/-- The number of ways to continue the row `r` by `k` more rows into a good word. -/
noncomputable def cont (k : ℕ) (r : Letter) : ℤ :=
  ∑ A : Fin k → Letter, cind (RowsOK (Fin.cons r A : Fin (k + 1) → Letter))

theorem cont_zero (r : Letter) : cont 0 r = cind (rowOK r ∧ endOK r) := by
  unfold cont
  rw [Fintype.sum_unique]
  exact cind_congr (rowsOK_one r _)

theorem cont_succ (k : ℕ) (r : Letter) :
    cont (k + 1) r = ∑ s, cind (rowOK r ∧ rowCompat r s) * cont k s := by
  unfold cont
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ => Letter))
    (fun p => cind (RowsOK (Fin.cons r (Fin.cons p.1 p.2 : Fin (k + 1) → Letter) :
      Fin (k + 2) → Letter))) _ (fun p => rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [cind_congr (rowsOK_cons r _), cons_mk_zero, ← and_assoc, cind_and]

theorem card_rowsOK (k : ℕ) [DecidablePred (fun w : Fin (k + 1) → Letter => RowsOK w)] :
    (((univ.filter (fun w : Fin (k + 1) → Letter => RowsOK w)).card : ℕ) : ℤ) =
      ∑ r, cont k r := by
  rw [Finset.card_filter]
  push_cast
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ => Letter))
    (fun p => if RowsOK (Fin.cons p.1 p.2 : Fin (k + 1) → Letter) then (1 : ℤ) else 0) _
    (fun p => rfl), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  unfold cont
  refine Finset.sum_congr rfl (fun A _ => ?_)
  unfold cind
  by_cases h : RowsOK (Fin.cons r A : Fin (k + 1) → Letter)
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- The number of good words with `k + 1` rows. -/
noncomputable def tot (k : ℕ) : ℤ := ∑ r, cont k r

/-- The number of good words with `k + 1` rows whose first row has horizontal flow `≠ 1`. -/
noncomputable def totU (k : ℕ) : ℤ := ∑ r : Letter, cind (r.1.val ≠ 2) * cont k r

theorem inner1 (s : Letter) :
    ∑ r : Letter, cind (rowOK r ∧ rowCompat r s) = 3 + 4 * cind (s.1.val ≠ 2) := by
  obtain ⟨s1, s2⟩ := s
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three]
  fin_cases s1 <;> fin_cases s2 <;> simp [cind, rowOK, rowCompat]

theorem inner2 (s : Letter) :
    ∑ r : Letter, cind (r.1.val ≠ 2) * cind (rowOK r ∧ rowCompat r s) =
      2 + 2 * cind (s.1.val ≠ 2) := by
  obtain ⟨s1, s2⟩ := s
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three]
  fin_cases s1 <;> fin_cases s2 <;> simp [cind, rowOK, rowCompat]

theorem tot_zero : tot 0 = 3 := by
  unfold tot
  simp only [cont_zero, Fintype.sum_prod_type, Fin.sum_univ_three]
  simp [cind, rowOK, endOK]

theorem totU_zero : totU 0 = 2 := by
  unfold totU
  simp only [cont_zero, Fintype.sum_prod_type, Fin.sum_univ_three]
  simp [cind, rowOK, endOK]

theorem tot_succ (k : ℕ) : tot (k + 1) = 3 * tot k + 4 * totU k := by
  unfold tot totU
  simp only [cont_succ]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, inner1]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]

theorem totU_succ (k : ℕ) : totU (k + 1) = 2 * tot k + 2 * totU k := by
  unfold tot totU
  simp only [cont_succ, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul, inner2]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]

theorem tot_rec (k : ℕ) : tot (k + 2) = 5 * tot (k + 1) + 2 * tot k := by
  have h1 := tot_succ (k + 1)
  have h2 := tot_succ k
  have h3 := totU_succ k
  linarith

theorem a_succ (k : ℕ) : (a (k + 1) : ℤ) = tot k := by
  classical
  rw [a_eq_card (k + 1), Finset.filter_congr (fun w _ => vwp_iff w), card_rowsOK]
  rfl

theorem a_one : a 1 = 3 := by
  have h := a_succ 0
  rw [tot_zero] at h
  exact_mod_cast h

theorem a_two : a 2 = 17 := by
  have h := a_succ 1
  rw [tot_succ, tot_zero, totU_zero] at h
  norm_num at h
  exact_mod_cast h

theorem a_rec (k : ℕ) : (a (k + 3) : ℤ) = 5 * a (k + 2) + 2 * a (k + 1) := by
  rw [a_succ (k + 2), a_succ (k + 1), a_succ k]
  exact tot_rec k

open PowerSeries in
theorem gf_generic (f : ℕ → ℚ) (h1 : f 1 = 3) (h2 : f 2 = 17)
    (hrec : ∀ k, f (k + 3) = 5 * f (k + 2) + 2 * f (k + 1)) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else f n) * (1 - 5 * X - 2 * X ^ 2) =
        X * (3 + 2 * X) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else f n with hF
  have key : PowerSeries.mk F * (1 - 5 * X - 2 * X ^ 2) =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 5 * (PowerSeries.mk F * X ^ 1) -
        C 2 * (PowerSeries.mk F * X ^ 2) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X * (3 + 2 * X) : ℚ⟦X⟧) = C 3 * X ^ 1 + C 2 * X ^ 2 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 3
  · interval_cases k <;> norm_num [hF, h1, h2]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    simp only [show 0 ≤ j + 3 by omega, show 1 ≤ j + 3 by omega, show 2 ≤ j + 3 by omega,
      show j + 3 - 0 = j + 3 by omega, show j + 3 - 1 = j + 2 by omega,
      show j + 3 - 2 = j + 1 by omega, show ¬ (j + 3 = 1) by omega, show ¬ (j + 3 = 2) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega,
      if_true, if_false, hF]
    rw [hrec j]
    ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 5 * X - 2 * X ^ 2) =
        X * (3 + 2 * X) := by
  refine gf_generic (fun n => (a n : ℚ)) (by rw [a_one]; norm_num) (by rw [a_two]; norm_num) ?_
  intro k
  have h := a_rec k
  have h' : ((a (k + 3) : ℤ) : ℚ) = ((5 * a (k + 2) + 2 * a (k + 1) : ℤ) : ℚ) := by rw [h]
  push_cast at h'
  exact h'

/-- The numerator of the closed form. -/
noncomputable def numer (n : ℕ) : ℝ :=
  (5 - Real.sqrt 33) ^ n * (-1 + Real.sqrt 33) + (1 + Real.sqrt 33) * (5 + Real.sqrt 33) ^ n

theorem numer_rec (n : ℕ) : numer (n + 2) = 10 * numer (n + 1) + 8 * numer n := by
  have hs : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  unfold numer
  linear_combination ((5 - Real.sqrt 33) ^ n * (-1 + Real.sqrt 33) +
    (1 + Real.sqrt 33) * (5 + Real.sqrt 33) ^ n) * hs

theorem a_real_rec (k : ℕ) : (a (k + 3) : ℝ) = 5 * a (k + 2) + 2 * a (k + 1) := by
  have h := a_rec k
  have h' : ((a (k + 3) : ℤ) : ℝ) = ((5 * a (k + 2) + 2 * a (k + 1) : ℤ) : ℝ) := by rw [h]
  push_cast at h'
  exact h'

theorem a_mul (k : ℕ) :
    (a (k + 1) : ℝ) * (2 ^ (k + 2) * Real.sqrt 33) = numer (k + 1) ∧
      (a (k + 2) : ℝ) * (2 ^ (k + 3) * Real.sqrt 33) = numer (k + 2) := by
  have hs : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  induction k with
  | zero =>
    constructor
    · rw [a_one]
      unfold numer
      push_cast
      ring
    · rw [a_two]
      unfold numer
      push_cast
      linear_combination (-2 * Real.sqrt 33) * hs
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [show k + 1 + 2 = k + 3 by ring, a_real_rec k, show k + 3 = k + 1 + 2 by ring,
      numer_rec (k + 1)]
    rw [show k + 1 + 1 = k + 2 by ring]
    have e1 := ih.1
    have e2 := ih.2
    rw [show (2 : ℝ) ^ (k + 1 + 3) = 4 * 2 ^ (k + 2) by ring]
    rw [show (2 : ℝ) ^ (k + 3) = 2 * 2 ^ (k + 2) by ring] at e2
    linear_combination 10 * e2 + 8 * e1

theorem closed_form (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℝ) = (2 : ℝ) ^ (-1 - (n : ℤ)) * ((5 - Real.sqrt 33) ^ n * (-1 + Real.sqrt 33) +
        (1 + Real.sqrt 33) * (5 + Real.sqrt 33) ^ n) / Real.sqrt 33 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := (a_mul k).1
  have hs : 0 < Real.sqrt 33 := Real.sqrt_pos.2 (by norm_num)
  have hz : (2 : ℝ) ^ (-1 - ((k + 1 : ℕ) : ℤ)) = ((2 : ℝ) ^ (k + 2))⁻¹ := by
    rw [show (-1 - ((k + 1 : ℕ) : ℤ)) = -((k + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast]
  rw [hz]
  unfold numer at h
  field_simp
  linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a221731.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.closed_form⟩
