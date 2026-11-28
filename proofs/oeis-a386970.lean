import OMAStatements.S_oeis_a386970

/-!
Proof of the OEIS A386970 conjecture:
For every `n ≥ 2`, Langton's ant on the `(3*n + 1) × 3` torus has minimal period `96*n + 16`.

Proof architecture:
1. **Time-reversal symmetry**: Define the involution `revRot180` combining 180-degree torus rotation
   `(x, y) ↦ (-x, 2 - y)` with Langton's ant time reversal (stepping backward before reversing
   heading). We prove `revRot180 (revRot180 s) = s` and `antStep (revRot180 (antStep s)) = revRot180 s`.
   By induction, `antStep^[k] (revRot180 (antStep^[k] s)) = revRot180 s`, so if both `initState W`
   and `antStep^[H] (initState W)` are fixed points of `revRot180` (with `H = 48*n + 8`), then:
   - `antStep^[2*H] (initState W) = initState W`, and
   - if `grid ≠ all_false` for every `1 ≤ t ≤ H`, then `antStep^[t] (initState W) ≠ initState W`
     for every `1 ≤ t < 2*H` (since `revRot180` preserves `all_false`).
2. **Local non-wrapping window simulator (`localRunNZ`)**: Any finite run of `T` steps inside a
   contiguous window of `L ≤ W` columns that never steps off the window edge and keeps a nonzero
   column at every intermediate step lifts directly to the parametric torus `ZMod W × ZMod 3`,
   leaving all columns outside the window untouched.
3. **Five-phase half-period traversal (`0 → 48*n + 8`)**:
   - `START` (`48` steps, window `L = 7` at `W - 1`): reaches `fwdState n 0`.
   - `FWD` (`30` steps per `+3` columns, repeated `n - 2` times, window `L = 5`):
     reaches `fwdState n (n - 2)` at `t = 30*n - 12`.
   - `BOUNCE` (`40` steps, window `L = 6` at `W - 4`): reaches `bwdState n (n - 2)` at `t = 30*n + 28`.
   - `BWD` (`18` steps per `-3` columns, repeated `n - 2` times, window `L = 5`):
     reaches `bwdState n 0` at `t = 48*n - 8`.
   - `FINISH` (`16` steps, window `L = 5` at `0`): reaches `halfState n` at `t = 48*n + 8`,
     which is an exact fixed point of `revRot180`.
-/

namespace A386970Proof

open OMA.S_oeis_a386970

/-! ### Part 1: Time-reversal symmetry (`revRot180`) -/

private def revRot180 {W : ℕ} (s : AntState W) : AntState W :=
  { x := -(s.x - dx W s.dir)
    y := 2 - (s.y - dy s.dir)
    dir := s.dir
    grid := fun a b => s.grid (-a) (2 - b) }

private lemma dx_neg {W : ℕ} (d : Fin 4) : dx W d + dx W (d + 2) = 0 := by
  fin_cases d <;> simp [dx]

private lemma dy_neg (d : Fin 4) : dy d + dy (d + 2) = 0 := by
  fin_cases d <;> decide

private lemma revRot180_invol {W : ℕ} (s : AntState W) :
    revRot180 (revRot180 s) = s := by
  cases s with
  | mk x y dir grid =>
    simp only [revRot180, AntState.mk.injEq]
    refine ⟨by ring, by ring, trivial, ?_⟩
    funext a b
    rw [neg_neg, show (2 : ZMod 3) - (2 - b) = b by ring]

private lemma antStep_revRot180_antStep {W : ℕ} (s : AntState W) :
    antStep (revRot180 (antStep s)) = revRot180 s := by
  cases s with
  | mk x y dir grid =>
    simp only [antStep, revRot180, AntState.mk.injEq]
    have hx : -(x + dx W (if grid x y then dir + 3 else dir + 1) -
        dx W (if grid x y then dir + 3 else dir + 1)) = -x := by ring
    have hy : (2 : ZMod 3) - (y + dy (if grid x y then dir + 3 else dir + 1) -
        dy (if grid x y then dir + 3 else dir + 1)) = 2 - y := by ring
    have hcell : (if -(-x) = x ∧ (2 : ZMod 3) - (2 - y) = y then !grid x y else grid (-(-x)) (2 - (2 - y))) =
        !grid x y := by
      rw [if_pos ⟨neg_neg x, by ring⟩]
    rw [hx, hy, hcell]
    have hdir : (if (!grid x y) = true then (if grid x y = true then dir + 3 else dir + 1) + 3
        else (if grid x y = true then dir + 3 else dir + 1) + 1) = dir := by
      cases grid x y <;> fin_cases dir <;> decide
    rw [hdir]
    refine ⟨by ring, by ring, rfl, ?_⟩
    funext a b
    by_cases h : a = -x ∧ b = 2 - y
    · obtain ⟨rfl, rfl⟩ := h
      rw [if_pos ⟨rfl, rfl⟩, Bool.not_not, neg_neg,
        show (2 : ZMod 3) - (2 - y) = y by ring]
    · rw [if_neg h]
      have h' : ¬ (-a = x ∧ (2 : ZMod 3) - b = y) := by
        rintro ⟨h1, h2⟩
        apply h
        refine ⟨?_, ?_⟩
        · have := congrArg Neg.neg h1; simpa using this
        · have := congrArg (fun z : ZMod 3 => 2 - z) h2; simpa [sub_sub_cancel] using this
      rw [if_neg h']

private lemma antStep_iter_revRot180 {W : ℕ} :
    ∀ (k : ℕ) (s : AntState W),
      antStep^[k] (revRot180 (antStep^[k] s)) = revRot180 s := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    rw [Function.iterate_succ_apply (f := antStep) k,
      Function.iterate_succ_apply' (f := antStep) k,
      antStep_revRot180_antStep, ih]

private lemma antStep_add_eq_revRot180 {W : ℕ} {H : ℕ} {s₀ : AntState W}
    (hH : revRot180 (antStep^[H] s₀) = antStep^[H] s₀) :
    ∀ t : ℕ, t ≤ H → antStep^[H + t] s₀ = revRot180 (antStep^[H - t] s₀) := by
  intro t ht
  have h2 : antStep^[t] (antStep^[H] s₀) = revRot180 (antStep^[H - t] s₀) := by
    have hsplit : H = t + (H - t) := by omega
    calc
      antStep^[t] (antStep^[H] s₀)
          = antStep^[t] (revRot180 (antStep^[H] s₀)) := by rw [hH]
      _ = antStep^[t] (revRot180 (antStep^[t] (antStep^[H - t] s₀))) := by
          conv_lhs => rw [hsplit]
          rw [Function.iterate_add_apply]
      _ = revRot180 (antStep^[H - t] s₀) := antStep_iter_revRot180 t (antStep^[H - t] s₀)
  rw [add_comm H t, Function.iterate_add_apply]
  exact h2

private lemma revRot180_initState (W : ℕ) : revRot180 (initState W) = initState W := by
  simp only [revRot180, initState, AntState.mk.injEq]
  refine ⟨?_, ?_, trivial, trivial⟩
  · have : dx W 1 = 0 := rfl
    rw [this]; ring
  · have : dy 1 = 1 := by decide
    rw [this]; decide

private lemma period_of_half_fixed {W H : ℕ} (hHpos : 0 < H)
    (hfix : revRot180 (antStep^[H] (initState W)) = antStep^[H] (initState W))
    (hgrid : ∀ t : ℕ, 1 ≤ t → t ≤ H → (antStep^[t] (initState W)).grid ≠ fun _ _ => false) :
    IsPeriod W (2 * H) := by
  refine ⟨by omega, ?_, ?_⟩
  · have h := antStep_add_eq_revRot180 hfix H le_rfl
    rw [show H + H = 2 * H by omega, Nat.sub_self, Function.iterate_zero_apply,
      revRot180_initState] at h
    exact h
  · intro t ht1 ht2 heq
    by_cases hle : t ≤ H
    · have hg : (antStep^[t] (initState W)).grid = fun _ _ => false := by
        rw [heq]; rfl
      exact hgrid t (by omega) hle hg
    · set r := t - H
      have hr : r ≤ H := by omega
      have htr : t = H + r := by omega
      have hsym := antStep_add_eq_revRot180 hfix r hr
      rw [← htr, heq] at hsym
      have hrev := congrArg revRot180 hsym
      rw [revRot180_initState, revRot180_invol] at hrev
      have hg : (antStep^[H - r] (initState W)).grid = fun _ _ => false := by
        rw [← hrev]; rfl
      exact hgrid (H - r) (by omega) (by omega) hg

/-! ### Part 2: Local non-wrapping window simulator -/

private def bitOf (m y : ℕ) : Bool := (m / 2 ^ y) % 2 == 1

private def flipBit (m y : ℕ) : ℕ :=
  if bitOf m y then m - 2 ^ y else m + 2 ^ y

private lemma flipBit_lt_eight : ∀ m < 8, ∀ y < 3, flipBit m y < 8 := by
  decide

private lemma bitOf_flipBit_self : ∀ m < 8, ∀ y < 3, bitOf (flipBit m y) y = !bitOf m y := by
  decide

private lemma bitOf_flipBit_ne :
    ∀ m < 8, ∀ y < 3, ∀ y' < 3, y' ≠ y → bitOf (flipBit m y) y' = bitOf m y' := by
  decide

private lemma exists_bitOf_true_of_ne_zero :
    ∀ m < 8, m ≠ 0 → ∃ y < 3, bitOf m y = true := by
  decide

private structure LocalState where
  j : ℕ
  y : ℕ
  d : ℕ
  cols : List ℕ
  deriving DecidableEq

private def nextYNat (y d2 : ℕ) : ℕ :=
  match d2 with
  | 1 => (y + 1) % 3
  | 3 => (y + 2) % 3
  | _ => y

private def moveLocal (L j y d2 : ℕ) (cols2 : List ℕ) : Option LocalState :=
  match d2 with
  | 0 => if j + 1 < L then some ⟨j + 1, nextYNat y d2, d2, cols2⟩ else none
  | 2 => if 0 < j then some ⟨j - 1, nextYNat y d2, d2, cols2⟩ else none
  | _ => some ⟨j, nextYNat y d2, d2, cols2⟩

private def localStep (L : ℕ) (s : LocalState) : Option LocalState :=
  let m := s.cols.getD s.j 0
  let c := bitOf m s.y
  let d2 := if c then (s.d + 3) % 4 else (s.d + 1) % 4
  let cols2 := s.cols.set s.j (flipBit m s.y)
  moveLocal L s.j s.y d2 cols2

private def localRunNZ (L : ℕ) : ℕ → LocalState → Option LocalState
  | 0, s => some s
  | t + 1, s =>
    match localStep L s with
    | none => none
    | some s' =>
      if s'.cols.any (· != 0) then localRunNZ L t s' else none

private def ValidLocal (L : ℕ) (s : LocalState) : Prop :=
  s.j < L ∧ s.y < 3 ∧ s.d < 4 ∧ s.cols.length = L ∧ ∀ i < L, s.cols.getD i 0 < 8

private def WindowMatches {W : ℕ} (base : ZMod W) (L : ℕ) (ls : LocalState) (st : AntState W) : Prop :=
  st.x = base + (ls.j : ZMod W) ∧
  st.y = (ls.y : ZMod 3) ∧
  st.dir.val = ls.d ∧
  ∀ i : ℕ, i < L → ∀ y : ℕ, y < 3 → st.grid (base + (i : ZMod W)) (y : ZMod 3) = bitOf (ls.cols.getD i 0) y

private lemma natCast_zmod_inj {W L : ℕ} (hLW : L ≤ W) {i j : ℕ} (hi : i < L) (hj : j < L)
    (heq : (i : ZMod W) = (j : ZMod W)) : i = j := by
  have : NeZero W := ⟨by omega⟩
  have h := congrArg ZMod.val heq
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  exact h

private lemma natCast_zmod3_inj {a b : ℕ} (ha : a < 3) (hb : b < 3)
    (heq : (a : ZMod 3) = (b : ZMod 3)) : a = b := by
  have h := congrArg ZMod.val heq
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact h

private lemma nextYNat_lt (y d2 : ℕ) (hy : y < 3) : nextYNat y d2 < 3 := by
  unfold nextYNat
  rcases (show d2 = 1 ∨ d2 = 3 ∨ (d2 ≠ 1 ∧ d2 ≠ 3) by omega) with rfl | rfl | ⟨h1, h3⟩
  · change (y + 1) % 3 < 3; omega
  · change (y + 2) % 3 < 3; omega
  · cases d2 with
    | zero => exact hy
    | succ d' =>
      cases d' with
      | zero => omega
      | succ d'' =>
        cases d'' with
        | zero => exact hy
        | succ d''' =>
          cases d''' with
          | zero => omega
          | succ _ => exact hy

private lemma dy_eq_nextYNat (y : ℕ) (hy : y < 3) (d : Fin 4) :
    (y : ZMod 3) + dy d = (nextYNat y d.val : ZMod 3) := by
  fin_cases d <;> (interval_cases y <;> decide)

private lemma localStep_sound {W L : ℕ} (hLW : L ≤ W) (base : ZMod W)
    {ls ls' : LocalState} {st : AntState W}
    (hval : ValidLocal L ls) (hmatch : WindowMatches base L ls st)
    (hstep : localStep L ls = some ls') :
    ValidLocal L ls' ∧ WindowMatches base L ls' (antStep st) ∧
    (∀ a : ZMod W, (∀ i : ℕ, i < L → a ≠ base + (i : ZMod W)) → ∀ b : ZMod 3,
      (antStep st).grid a b = st.grid a b) := by
  obtain ⟨hjL, hy3, hd4, hlen, hcols8⟩ := hval
  obtain ⟨hx, hy, hdir, hgrid⟩ := hmatch
  have hc_eq : st.grid st.x st.y = bitOf (ls.cols.getD ls.j 0) ls.y := by
    rw [hx, hy]
    exact hgrid ls.j hjL ls.y hy3
  set d' : Fin 4 := if st.grid st.x st.y then st.dir + 3 else st.dir + 1
  set d2 : ℕ := if bitOf (ls.cols.getD ls.j 0) ls.y then (ls.d + 3) % 4 else (ls.d + 1) % 4
  have hd2_lt : d2 < 4 := by
    simp only [d2]; split_ifs <;> omega
  have hd'_val : d'.val = d2 := by
    simp only [d', hc_eq, d2]
    cases bitOf (ls.cols.getD ls.j 0) ls.y with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have : (st.dir + 1).val = (st.dir.val + 1) % 4 := rfl
      rw [this, hdir]
    | true =>
      simp only [↓reduceIte]
      have : (st.dir + 3).val = (st.dir.val + 3) % 4 := rfl
      rw [this, hdir]
  set cols2 : List ℕ := ls.cols.set ls.j (flipBit (ls.cols.getD ls.j 0) ls.y)
  have hcols2_len : cols2.length = L := by simp [cols2, hlen]
  have hcols2_getD : ∀ i < L, cols2.getD i 0 =
      if i = ls.j then flipBit (ls.cols.getD ls.j 0) ls.y else ls.cols.getD i 0 := by
    intro i hi
    simp only [cols2, List.getD_eq_getElem?_getD]
    by_cases hij : i = ls.j
    · subst hij
      rw [if_pos rfl, List.getElem?_set_self (by omega), Option.getD_some]
    · rw [if_neg hij, List.getElem?_set_ne (Ne.symm hij)]
  have hcols2_8 : ∀ i < L, cols2.getD i 0 < 8 := by
    intro i hi
    rw [hcols2_getD i hi]
    split_ifs
    · exact flipBit_lt_eight _ (hcols8 ls.j hjL) ls.y hy3
    · exact hcols8 i hi
  have hmove : moveLocal L ls.j ls.y d2 cols2 = some ls' := hstep
  have hj_and_x : ls'.j < L ∧ ls'.y = nextYNat ls.y d2 ∧ ls'.d = d2 ∧ ls'.cols = cols2 ∧
      (antStep st).x = base + (ls'.j : ZMod W) := by
    have hstx : (antStep st).x = base + (ls.j : ZMod W) + dx W d' := by
      simp only [antStep, hx, d']
    have hcases : d2 = 0 ∨ d2 = 1 ∨ d2 = 2 ∨ d2 = 3 := by omega
    rcases hcases with hd0 | hd1 | hd2 | hd3
    · rw [hd0] at hmove
      simp only [moveLocal] at hmove
      split_ifs at hmove with hlt
      injection hmove with hls'
      subst hls'
      refine ⟨hlt, by rw [hd0], hd0.symm, rfl, ?_⟩
      rw [hstx]
      have hdx : dx W d' = 1 := by unfold dx; rw [hd'_val, hd0]; rfl
      rw [hdx]; push_cast; ring
    · rw [hd1] at hmove
      simp only [moveLocal] at hmove
      injection hmove with hls'
      subst hls'
      refine ⟨hjL, by rw [hd1], hd1.symm, rfl, ?_⟩
      rw [hstx]
      have hdx : dx W d' = 0 := by unfold dx; rw [hd'_val, hd1]; rfl
      rw [hdx, add_zero]
    · rw [hd2] at hmove
      simp only [moveLocal] at hmove
      split_ifs at hmove with hpos
      injection hmove with hls'
      subst hls'
      refine ⟨by dsimp only; omega, by rw [hd2], hd2.symm, rfl, ?_⟩
      rw [hstx]
      have hdx : dx W d' = -1 := by unfold dx; rw [hd'_val, hd2]; rfl
      rw [hdx, Nat.cast_sub (by omega : 1 ≤ ls.j), Nat.cast_one]; ring
    · rw [hd3] at hmove
      simp only [moveLocal] at hmove
      injection hmove with hls'
      subst hls'
      refine ⟨hjL, by rw [hd3], hd3.symm, rfl, ?_⟩
      rw [hstx]
      have hdx : dx W d' = 0 := by unfold dx; rw [hd'_val, hd3]; rfl
      rw [hdx, add_zero]
  obtain ⟨hj'_lt, hy'_eq, hd'_eq, hcols'_eq, hx'_eq⟩ := hj_and_x
  have hy'_zmod : (antStep st).y = (ls'.y : ZMod 3) := by
    change st.y + dy d' = (ls'.y : ZMod 3)
    rw [hy, dy_eq_nextYNat ls.y hy3 d', hd'_val, hy'_eq]
  refine ⟨⟨hj'_lt, by rw [hy'_eq]; exact nextYNat_lt ls.y d2 hy3, by rw [hd'_eq]; exact hd2_lt,
      by rw [hcols'_eq]; exact hcols2_len, by rw [hcols'_eq]; exact hcols2_8⟩,
    ⟨hx'_eq, hy'_zmod, by rw [hd'_eq]; exact hd'_val, ?_⟩, ?_⟩
  · intro i hi y' hy'
    simp only [antStep, hx, hy, hcols'_eq, hcols2_getD i hi]
    by_cases hij : i = ls.j
    · subst hij
      rw [if_pos rfl]
      by_cases hyy : y' = ls.y
      · subst hyy
        rw [if_pos ⟨rfl, rfl⟩, bitOf_flipBit_self _ (hcols8 ls.j hjL) ls.y hy3,
          hgrid ls.j hjL ls.y hy3]
      · have hne : ¬ ((y' : ZMod 3) = (ls.y : ZMod 3)) :=
          fun heq => hyy (natCast_zmod3_inj hy' hy3 heq)
        rw [if_neg (fun h => hne h.2), bitOf_flipBit_ne _ (hcols8 ls.j hjL) ls.y hy3 y' hy' hyy,
          hgrid ls.j hjL y' hy']
    · rw [if_neg hij]
      have hne : ¬ (base + (i : ZMod W) = base + (ls.j : ZMod W)) := by
        intro heq
        exact hij (natCast_zmod_inj hLW hi hjL (add_left_cancel heq))
      rw [if_neg (fun h => hne h.1), hgrid i hi y' hy']
  · intro a ha b
    simp only [antStep, hx]
    rw [if_neg (fun h => ha ls.j hjL h.1)]

private lemma localRunNZ_sound {W L : ℕ} (hLW : L ≤ W) (base : ZMod W) :
    ∀ (T : ℕ) (ls ls' : LocalState) (st : AntState W),
      ValidLocal L ls → WindowMatches base L ls st → localRunNZ L T ls = some ls' →
      WindowMatches base L ls' (antStep^[T] st) ∧
      (∀ a : ZMod W, (∀ i : ℕ, i < L → a ≠ base + (i : ZMod W)) → ∀ b : ZMod 3,
        (antStep^[T] st).grid a b = st.grid a b) ∧
      (∀ t : ℕ, 1 ≤ t → t ≤ T → (antStep^[t] st).grid ≠ fun _ _ => false) := by
  intro T
  induction T with
  | zero =>
    intro ls ls' st _ hmatch hrun
    simp only [localRunNZ, Option.some.injEq] at hrun
    subst hrun
    exact ⟨hmatch, fun _ _ _ => rfl, fun t ht1 ht2 => by omega⟩
  | succ T ih =>
    intro ls ls' st hval hmatch hrun
    unfold localRunNZ at hrun
    cases hst : localStep L ls with
    | none => rw [hst] at hrun; simp at hrun
    | some ls1 =>
      rw [hst] at hrun
      dsimp only at hrun
      split_ifs at hrun with hany
      obtain ⟨hval1, hmatch1, hout1⟩ := localStep_sound hLW base hval hmatch hst
      obtain ⟨hmatchT, houtT, hnzT⟩ := ih ls1 ls' (antStep st) hval1 hmatch1 hrun
      have hnz1 : (antStep st).grid ≠ fun _ _ => false := by
        rw [List.any_eq_true] at hany
        obtain ⟨m, hm_mem, hm_ne⟩ := hany
        obtain ⟨i, hi_lt, hm_eq⟩ := List.mem_iff_getElem.mp hm_mem
        have hiL : i < L := by rw [← hval1.2.2.2.1]; exact hi_lt
        have hgetD : ls1.cols.getD i 0 = m := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_lt, Option.getD_some, hm_eq]
        have hm0 : m ≠ 0 := by simpa using hm_ne
        have hm8 : m < 8 := by rw [← hgetD]; exact hval1.2.2.2.2 i hiL
        obtain ⟨y, hy3, hbit⟩ := exists_bitOf_true_of_ne_zero m hm8 hm0
        intro hall
        have h1 := hmatch1.2.2.2 i hiL y hy3
        rw [hgetD, hbit, hall] at h1
        exact Bool.false_ne_true h1
      refine ⟨?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply]; exact hmatchT
      · intro a ha b
        rw [Function.iterate_succ_apply, houtT a ha b, hout1 a ha b]
      · intro t ht1 ht2
        cases t with
        | zero => omega
        | succ t' =>
          rw [Function.iterate_succ_apply]
          cases t' with
          | zero => exact hnz1
          | succ t'' => exact hnzT (t'' + 1) (by omega) (by omega)

/-! ### Part 3: The five finite local macro-steps (`by decide`) -/

private def startInit : LocalState := ⟨1, 0, 1, [0, 0, 0, 0, 0, 0, 0]⟩
private def startEnd  : LocalState := ⟨5, 2, 3, [5, 2, 0, 0, 0, 2, 5]⟩

private def fwdInit   : LocalState := ⟨0, 2, 3, [2, 5, 0, 0, 0]⟩
private def fwdEnd    : LocalState := ⟨3, 2, 3, [0, 0, 0, 2, 5]⟩

private def bncInit   : LocalState := ⟨1, 2, 3, [0, 2, 5, 5, 2, 0]⟩
private def bncEnd    : LocalState := ⟨1, 0, 3, [6, 1, 6, 0, 7, 6]⟩

private def bwdInit   : LocalState := ⟨4, 0, 3, [0, 0, 0, 6, 1]⟩
private def bwdEnd    : LocalState := ⟨1, 0, 3, [6, 1, 0, 0, 0]⟩

private def finInit   : LocalState := ⟨4, 0, 3, [7, 6, 0, 6, 1]⟩
private def finEnd    : LocalState := ⟨0, 2, 3, [5, 0, 3, 0, 0]⟩

private lemma run_start : localRunNZ 7 48 startInit = some startEnd := by decide
private lemma run_fwd   : localRunNZ 5 30 fwdInit   = some fwdEnd   := by decide
private lemma run_bnc   : localRunNZ 6 40 bncInit   = some bncEnd   := by decide
private lemma run_bwd   : localRunNZ 5 18 bwdInit   = some bwdEnd   := by decide
private lemma run_fin   : localRunNZ 5 16 finInit   = some finEnd   := by decide

private lemma valid_start : ValidLocal 7 startInit := by
  refine ⟨by decide, by decide, by decide, rfl, ?_⟩
  intro i hi; interval_cases i <;> decide

private lemma valid_fwd : ValidLocal 5 fwdInit := by
  refine ⟨by decide, by decide, by decide, rfl, ?_⟩
  intro i hi; interval_cases i <;> decide

private lemma valid_bnc : ValidLocal 6 bncInit := by
  refine ⟨by decide, by decide, by decide, rfl, ?_⟩
  intro i hi; interval_cases i <;> decide

private lemma valid_bwd : ValidLocal 5 bwdInit := by
  refine ⟨by decide, by decide, by decide, rfl, ?_⟩
  intro i hi; interval_cases i <;> decide

private lemma valid_fin : ValidLocal 5 finInit := by
  refine ⟨by decide, by decide, by decide, rfl, ?_⟩
  intro i hi; interval_cases i <;> decide

/-! ### Part 4: Parametric global states on the `(3*n + 1) × 3` torus -/

private def colMaskGrid {W : ℕ} (f : ZMod W → ℕ) : ZMod W → ZMod 3 → Bool :=
  fun a b => bitOf (f a) b.val

private def fwdGrid (n k : ℕ) : ZMod (3 * n + 1) → ZMod 3 → Bool :=
  colMaskGrid fun a =>
    if a = 0 then 2
    else if a = ((3 * k + 4 : ℕ) : ZMod (3 * n + 1)) then 2
    else if a = ((3 * k + 5 : ℕ) : ZMod (3 * n + 1)) then 5
    else if a = (-1 : ZMod (3 * n + 1)) then 5
    else 0

private def fwdState (n k : ℕ) : AntState (3 * n + 1) :=
  { x := ((3 * k + 4 : ℕ) : ZMod (3 * n + 1))
    y := 2
    dir := 3
    grid := fwdGrid n k }

private def bwdGrid (n k : ℕ) : ZMod (3 * n + 1) → ZMod 3 → Bool :=
  colMaskGrid fun a =>
    if a = 0 then 7
    else if a = 1 then 6
    else if a = ((3 * k + 3 : ℕ) : ZMod (3 * n + 1)) then 6
    else if a = ((3 * k + 4 : ℕ) : ZMod (3 * n + 1)) then 1
    else if a = (-2 : ZMod (3 * n + 1)) then 6
    else 0

private def bwdState (n k : ℕ) : AntState (3 * n + 1) :=
  { x := ((3 * k + 4 : ℕ) : ZMod (3 * n + 1))
    y := 0
    dir := 3
    grid := bwdGrid n k }

private def halfGrid (n : ℕ) : ZMod (3 * n + 1) → ZMod 3 → Bool :=
  colMaskGrid fun a =>
    if a = 0 then 5
    else if a = 2 then 3
    else if a = (-2 : ZMod (3 * n + 1)) then 6
    else 0

private def halfState (n : ℕ) : AntState (3 * n + 1) :=
  { x := 0
    y := 2
    dir := 3
    grid := halfGrid n }

private lemma zmod_ne_of_lt {W a b : ℕ} (ha : a < W) (hb : b < W) (hne : a ≠ b) :
    (a : ZMod W) ≠ (b : ZMod W) := by
  have : NeZero W := ⟨by omega⟩
  intro heq
  have h := congrArg ZMod.val heq
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact hne h

private lemma zmod_ne_zero_of_lt {W a : ℕ} (ha0 : 0 < a) (ha : a < W) :
    (a : ZMod W) ≠ 0 := by
  simpa using zmod_ne_of_lt (W := W) (a := a) (b := 0) ha (by omega) (by omega)

private lemma neg_one_eq_natCast (W : ℕ) (hW : 1 ≤ W) :
    (-1 : ZMod W) = ((W - 1 : ℕ) : ZMod W) := by
  have : NeZero W := ⟨by omega⟩
  rw [Nat.cast_sub hW, ZMod.natCast_self, zero_sub, Nat.cast_one]

private lemma neg_two_eq_natCast (W : ℕ) (hW : 2 ≤ W) :
    (-2 : ZMod W) = ((W - 2 : ℕ) : ZMod W) := by
  have : NeZero W := ⟨by omega⟩
  rw [Nat.cast_sub hW, ZMod.natCast_self, zero_sub, Nat.cast_ofNat]

private lemma neg_four_eq_natCast (W : ℕ) (hW : 4 ≤ W) :
    (-4 : ZMod W) = ((W - 4 : ℕ) : ZMod W) := by
  have : NeZero W := ⟨by omega⟩
  rw [Nat.cast_sub hW, ZMod.natCast_self, zero_sub, Nat.cast_ofNat]

private lemma bitOf_zero (y : ℕ) : bitOf 0 y = false := by
  unfold bitOf; simp

private lemma zmod3_cases (b : ZMod 3) : b = (b.val : ZMod 3) ∧ b.val < 3 :=
  ⟨(ZMod.natCast_zmod_val b).symm, b.val_lt⟩

private lemma start_phase {n : ℕ} (hn : 2 ≤ n) :
    antStep^[48] (initState (3 * n + 1)) = fwdState n 0 ∧
    (∀ t : ℕ, 1 ≤ t → t ≤ 48 →
      (antStep^[t] (initState (3 * n + 1))).grid ≠ fun _ _ => false) := by
  set W := 3 * n + 1
  have hW7 : 7 ≤ W := by omega
  have hmatch0 : WindowMatches (-1 : ZMod W) 7 startInit (initState W) := by
    refine ⟨by simp [initState, startInit], by simp [initState, startInit], rfl, ?_⟩
    intro i hi y hy
    simp only [initState, startInit]
    interval_cases i <;> simp [bitOf_zero]
  obtain ⟨hmatch1, hout1, hnz1⟩ := localRunNZ_sound hW7 (-1 : ZMod W) 48 startInit startEnd
    (initState W) valid_start hmatch0 run_start
  refine ⟨?_, hnz1⟩
  have hx1 : (antStep^[48] (initState W)).x = (4 : ZMod W) := by
    rw [hmatch1.1]; simp [startEnd]; ring
  have hy1 : (antStep^[48] (initState W)).y = 2 := by
    rw [hmatch1.2.1]; rfl
  have hd1 : (antStep^[48] (initState W)).dir = 3 := by
    apply Fin.ext; exact hmatch1.2.2.1
  cases hs : antStep^[48] (initState W) with
  | mk sx sy sd sg =>
    simp only [hs] at hx1 hy1 hd1 hmatch1 hout1
    dsimp only [WindowMatches] at hmatch1
    simp only [fwdState, AntState.mk.injEq]
    refine ⟨by simpa using hx1, hy1, hd1, ?_⟩
    funext a b
    obtain ⟨hb_eq, hb_lt⟩ := zmod3_cases b
    by_cases ha : ∃ i : ℕ, i < 7 ∧ a = (-1 : ZMod W) + (i : ZMod W)
    · obtain ⟨i, hi, rfl⟩ := ha
      rw [hb_eq, hmatch1.2.2.2 i hi b.val hb_lt]
      simp only [fwdGrid, colMaskGrid, ZMod.val_natCast, Nat.mod_eq_of_lt hb_lt]
      rw [neg_one_eq_natCast W (by omega)]
      interval_cases i
      · -- W - 1
        have h1 : ((W - 1 : ℕ) : ZMod W) + (0 : ℕ) = ((W - 1 : ℕ) : ZMod W) := by simp
        rw [h1]
        have hne0 := zmod_ne_zero_of_lt (W := W) (a := W - 1) (by omega) (by omega)
        have hne4 := zmod_ne_of_lt (W := W) (a := W - 1) (b := 4) (by omega) (by omega) (by omega)
        have hne5 := zmod_ne_of_lt (W := W) (a := W - 1) (b := 5) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne4), if_neg (by simpa using hne5), if_pos rfl]
        rfl
      · -- 0
        have h1 : ((W - 1 : ℕ) : ZMod W) + (1 : ℕ) = 0 := by
          rw [← neg_one_eq_natCast W (by omega)]; simp
        rw [h1, if_pos rfl]; rfl
      · -- 1
        have h1 : ((W - 1 : ℕ) : ZMod W) + (2 : ℕ) = ((1 : ℕ) : ZMod W) := by
          rw [← neg_one_eq_natCast W (by omega)]; push_cast; ring
        rw [h1]
        have hne0 := zmod_ne_zero_of_lt (W := W) (a := 1) (by omega) (by omega)
        have hne4 := zmod_ne_of_lt (W := W) (a := 1) (b := 4) (by omega) (by omega) (by omega)
        have hne5 := zmod_ne_of_lt (W := W) (a := 1) (b := 5) (by omega) (by omega) (by omega)
        have hneW := zmod_ne_of_lt (W := W) (a := 1) (b := W - 1) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne4), if_neg (by simpa using hne5), if_neg hneW]
        rfl
      · -- 2
        have h1 : ((W - 1 : ℕ) : ZMod W) + (3 : ℕ) = ((2 : ℕ) : ZMod W) := by
          rw [← neg_one_eq_natCast W (by omega)]; push_cast; ring
        rw [h1]
        have hne0 := zmod_ne_zero_of_lt (W := W) (a := 2) (by omega) (by omega)
        have hne4 := zmod_ne_of_lt (W := W) (a := 2) (b := 4) (by omega) (by omega) (by omega)
        have hne5 := zmod_ne_of_lt (W := W) (a := 2) (b := 5) (by omega) (by omega) (by omega)
        have hneW := zmod_ne_of_lt (W := W) (a := 2) (b := W - 1) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne4), if_neg (by simpa using hne5), if_neg hneW]
        rfl
      · -- 3
        have h1 : ((W - 1 : ℕ) : ZMod W) + (4 : ℕ) = ((3 : ℕ) : ZMod W) := by
          rw [← neg_one_eq_natCast W (by omega)]; push_cast; ring
        rw [h1]
        have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3) (by omega) (by omega)
        have hne4 := zmod_ne_of_lt (W := W) (a := 3) (b := 4) (by omega) (by omega) (by omega)
        have hne5 := zmod_ne_of_lt (W := W) (a := 3) (b := 5) (by omega) (by omega) (by omega)
        have hneW := zmod_ne_of_lt (W := W) (a := 3) (b := W - 1) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne4), if_neg (by simpa using hne5), if_neg hneW]
        rfl
      · -- 4
        have h1 : ((W - 1 : ℕ) : ZMod W) + (5 : ℕ) = ((4 : ℕ) : ZMod W) := by
          rw [← neg_one_eq_natCast W (by omega)]; push_cast; ring
        rw [h1]
        have hne0 := zmod_ne_zero_of_lt (W := W) (a := 4) (by omega) (by omega)
        rw [if_neg hne0, if_pos (by simp)]
        rfl
      · -- 5
        have h1 : ((W - 1 : ℕ) : ZMod W) + (6 : ℕ) = ((5 : ℕ) : ZMod W) := by
          rw [← neg_one_eq_natCast W (by omega)]; push_cast; ring
        rw [h1]
        have hne0 := zmod_ne_zero_of_lt (W := W) (a := 5) (by omega) (by omega)
        have hne4 := zmod_ne_of_lt (W := W) (a := 5) (b := 4) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne4), if_pos (by simp)]
        rfl
    · push Not at ha
      rw [hout1 a ha b]
      simp only [initState, fwdGrid, colMaskGrid]
      have hne0 : a ≠ 0 := by have := ha 1 (by omega); simpa using this
      have hne4 : a ≠ ((3 * 0 + 4 : ℕ) : ZMod W) := by
        have := ha 5 (by omega); intro h; apply this; rw [h]; push_cast; ring
      have hne5 : a ≠ ((3 * 0 + 5 : ℕ) : ZMod W) := by
        have := ha 6 (by omega); intro h; apply this; rw [h]; push_cast; ring
      have hneW : a ≠ (-1 : ZMod W) := by have := ha 0 (by omega); simpa using this
      rw [if_neg hne0, if_neg hne4, if_neg hne5, if_neg hneW, bitOf_zero]

private lemma fwd_step {n k : ℕ} (hn : 2 ≤ n) (hk : k + 2 < n) :
    antStep^[30] (fwdState n k) = fwdState n (k + 1) ∧
    (∀ t : ℕ, 1 ≤ t → t ≤ 30 → (antStep^[t] (fwdState n k)).grid ≠ fun _ _ => false) := by
  set W := 3 * n + 1
  set base : ZMod W := ((3 * k + 4 : ℕ) : ZMod W)
  have hW5 : 5 ≤ W := by omega
  have hmatch0 : WindowMatches base 5 fwdInit (fwdState n k) := by
    refine ⟨by simp [fwdState, fwdInit, base], rfl, rfl, ?_⟩
    intro i hi y hy
    simp only [fwdState, fwdGrid, colMaskGrid, ZMod.val_natCast, Nat.mod_eq_of_lt hy, base]
    rw [← Nat.cast_add, neg_one_eq_natCast W (by omega)]
    interval_cases i
    · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 4 + 0) (by omega) (by omega)
      rw [if_neg hne0, if_pos (by simp)]; rfl
    · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 4 + 1) (by omega) (by omega)
      have hne4 := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 1) (b := 3 * k + 4) (by omega) (by omega) (by omega)
      rw [if_neg hne0, if_neg hne4, if_pos (by push_cast; ring)]; rfl
    · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 4 + 2) (by omega) (by omega)
      have hne4 := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 2) (b := 3 * k + 4) (by omega) (by omega) (by omega)
      have hne5 := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 2) (b := 3 * k + 5) (by omega) (by omega) (by omega)
      have hneW := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 2) (b := W - 1) (by omega) (by omega) (by omega)
      rw [if_neg hne0, if_neg hne4, if_neg hne5, if_neg hneW]; rfl
    · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 4 + 3) (by omega) (by omega)
      have hne4 := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 3) (b := 3 * k + 4) (by omega) (by omega) (by omega)
      have hne5 := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 3) (b := 3 * k + 5) (by omega) (by omega) (by omega)
      have hneW := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 3) (b := W - 1) (by omega) (by omega) (by omega)
      rw [if_neg hne0, if_neg hne4, if_neg hne5, if_neg hneW]; rfl
    · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 4 + 4) (by omega) (by omega)
      have hne4 := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 4) (b := 3 * k + 4) (by omega) (by omega) (by omega)
      have hne5 := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 4) (b := 3 * k + 5) (by omega) (by omega) (by omega)
      have hneW := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 4) (b := W - 1) (by omega) (by omega) (by omega)
      rw [if_neg hne0, if_neg hne4, if_neg hne5, if_neg hneW]; rfl
  obtain ⟨hmatch1, hout1, hnz1⟩ := localRunNZ_sound hW5 base 30 fwdInit fwdEnd
    (fwdState n k) valid_fwd hmatch0 run_fwd
  refine ⟨?_, hnz1⟩
  have hx1 : (antStep^[30] (fwdState n k)).x = ((3 * (k + 1) + 4 : ℕ) : ZMod W) := by
    rw [hmatch1.1]; simp only [fwdEnd, base]; push_cast; ring
  have hy1 : (antStep^[30] (fwdState n k)).y = 2 := by rw [hmatch1.2.1]; rfl
  have hd1 : (antStep^[30] (fwdState n k)).dir = 3 := Fin.ext hmatch1.2.2.1
  cases hs : antStep^[30] (fwdState n k) with
  | mk sx sy sd sg =>
    simp only [hs] at hx1 hy1 hd1 hmatch1 hout1
    dsimp only [WindowMatches] at hmatch1
    simp only [fwdState, AntState.mk.injEq]
    refine ⟨hx1, hy1, hd1, ?_⟩
    funext a b
    obtain ⟨hb_eq, hb_lt⟩ := zmod3_cases b
    by_cases ha : ∃ i : ℕ, i < 5 ∧ a = base + (i : ZMod W)
    · obtain ⟨i, hi, rfl⟩ := ha
      rw [hb_eq, hmatch1.2.2.2 i hi b.val hb_lt]
      simp only [fwdGrid, colMaskGrid, ZMod.val_natCast, Nat.mod_eq_of_lt hb_lt, base]
      rw [← Nat.cast_add, neg_one_eq_natCast W (by omega)]
      interval_cases i
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 4 + 0) (by omega) (by omega)
        have hne4 := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 0) (b := 3 * (k + 1) + 4) (by omega) (by omega) (by omega)
        have hne5 := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 0) (b := 3 * (k + 1) + 5) (by omega) (by omega) (by omega)
        have hneW := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 0) (b := W - 1) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg hne4, if_neg hne5, if_neg hneW]; rfl
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 4 + 1) (by omega) (by omega)
        have hne4 := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 1) (b := 3 * (k + 1) + 4) (by omega) (by omega) (by omega)
        have hne5 := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 1) (b := 3 * (k + 1) + 5) (by omega) (by omega) (by omega)
        have hneW := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 1) (b := W - 1) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg hne4, if_neg hne5, if_neg hneW]; rfl
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 4 + 2) (by omega) (by omega)
        have hne4 := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 2) (b := 3 * (k + 1) + 4) (by omega) (by omega) (by omega)
        have hne5 := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 2) (b := 3 * (k + 1) + 5) (by omega) (by omega) (by omega)
        have hneW := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 2) (b := W - 1) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg hne4, if_neg hne5, if_neg hneW]; rfl
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 4 + 3) (by omega) (by omega)
        rw [if_neg hne0, if_pos (by push_cast; ring)]; rfl
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 4 + 4) (by omega) (by omega)
        have hne4 := zmod_ne_of_lt (W := W) (a := 3 * k + 4 + 4) (b := 3 * (k + 1) + 4) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg hne4, if_pos (by push_cast; ring)]; rfl
    · push Not at ha
      rw [hout1 a ha b]
      simp only [fwdState, fwdGrid, colMaskGrid]
      have hne4 : a ≠ ((3 * k + 4 : ℕ) : ZMod W) := by have := ha 0 (by omega); simpa [base] using this
      have hne5 : a ≠ ((3 * k + 5 : ℕ) : ZMod W) := by
        have := ha 1 (by omega); intro h; apply this; rw [h]; simp only [base]; push_cast; ring
      have hne7 : a ≠ ((3 * (k + 1) + 4 : ℕ) : ZMod W) := by
        have := ha 3 (by omega); intro h; apply this; rw [h]; simp only [base]; push_cast; ring
      have hne8 : a ≠ ((3 * (k + 1) + 5 : ℕ) : ZMod W) := by
        have := ha 4 (by omega); intro h; apply this; rw [h]; simp only [base]; push_cast; ring
      by_cases ha0 : a = 0
      · simp [ha0]
      · rw [if_neg ha0, if_neg ha0, if_neg hne4, if_neg hne5, if_neg hne7, if_neg hne8]

private lemma fwd_iter {n : ℕ} (hn : 2 ≤ n) :
    ∀ k ≤ n - 2,
      antStep^[30 * k] (fwdState n 0) = fwdState n k ∧
      (∀ t : ℕ, 1 ≤ t → t ≤ 30 * k → (antStep^[t] (fwdState n 0)).grid ≠ fun _ _ => false) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨rfl, fun t ht1 ht2 => by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨hprev, hnz_prev⟩ := ih (by omega)
    obtain ⟨hstep, hnz_step⟩ := fwd_step hn (by omega : k + 2 < n)
    refine ⟨?_, ?_⟩
    · rw [show 30 * (k + 1) = 30 + 30 * k by omega, Function.iterate_add_apply, hprev, hstep]
    · intro t ht1 ht2
      by_cases hle : t ≤ 30 * k
      · exact hnz_prev t ht1 hle
      · rw [show t = (t - 30 * k) + 30 * k by omega, Function.iterate_add_apply, hprev]
        exact hnz_step (t - 30 * k) (by omega) (by omega)

private lemma bounce_phase {n : ℕ} (hn : 2 ≤ n) :
    antStep^[40] (fwdState n (n - 2)) = bwdState n (n - 2) ∧
    (∀ t : ℕ, 1 ≤ t → t ≤ 40 →
      (antStep^[t] (fwdState n (n - 2))).grid ≠ fun _ _ => false) := by
  set W := 3 * n + 1
  set base : ZMod W := (-4 : ZMod W)
  have hW6 : 6 ≤ W := by omega
  have h3n2 : 3 * (n - 2) + 4 = W - 3 := by omega
  have h3n1 : 3 * (n - 2) + 5 = W - 2 := by omega
  have h3n3 : 3 * (n - 2) + 3 = W - 4 := by omega
  have hmatch0 : WindowMatches base 6 bncInit (fwdState n (n - 2)) := by
    refine ⟨?_, rfl, rfl, ?_⟩
    · simp only [fwdState, bncInit, base, h3n2]
      rw [neg_four_eq_natCast W (by omega), ← Nat.cast_add, show W - 4 + 1 = W - 3 by omega]
    · intro i hi y hy
      simp only [fwdState, fwdGrid, colMaskGrid, ZMod.val_natCast, Nat.mod_eq_of_lt hy,
        base, h3n2, h3n1]
      rw [neg_four_eq_natCast W (by omega), neg_one_eq_natCast W (by omega)]
      interval_cases i
      · -- W - 4
        have h1 : ((W - 4 : ℕ) : ZMod W) + (0 : ℕ) = ((W - 4 : ℕ) : ZMod W) := by simp
        rw [h1]
        have hne0 := zmod_ne_zero_of_lt (W := W) (a := W - 4) (by omega) (by omega)
        have hne3 := zmod_ne_of_lt (W := W) (a := W - 4) (b := W - 3) (by omega) (by omega) (by omega)
        have hne2 := zmod_ne_of_lt (W := W) (a := W - 4) (b := W - 2) (by omega) (by omega) (by omega)
        have hne1 := zmod_ne_of_lt (W := W) (a := W - 4) (b := W - 1) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg hne3, if_neg hne2, if_neg hne1]; rfl
      · -- W - 3
        have h1 : ((W - 4 : ℕ) : ZMod W) + (1 : ℕ) = ((W - 3 : ℕ) : ZMod W) := by
          rw [← Nat.cast_add, show W - 4 + 1 = W - 3 by omega]
        rw [h1]
        have hne0 := zmod_ne_zero_of_lt (W := W) (a := W - 3) (by omega) (by omega)
        rw [if_neg hne0, if_pos rfl]; rfl
      · -- W - 2
        have h1 : ((W - 4 : ℕ) : ZMod W) + (2 : ℕ) = ((W - 2 : ℕ) : ZMod W) := by
          rw [← Nat.cast_add, show W - 4 + 2 = W - 2 by omega]
        rw [h1]
        have hne0 := zmod_ne_zero_of_lt (W := W) (a := W - 2) (by omega) (by omega)
        have hne3 := zmod_ne_of_lt (W := W) (a := W - 2) (b := W - 3) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg hne3, if_pos rfl]; rfl
      · -- W - 1
        have h1 : ((W - 4 : ℕ) : ZMod W) + (3 : ℕ) = ((W - 1 : ℕ) : ZMod W) := by
          rw [← Nat.cast_add, show W - 4 + 3 = W - 1 by omega]
        rw [h1]
        have hne0 := zmod_ne_zero_of_lt (W := W) (a := W - 1) (by omega) (by omega)
        have hne3 := zmod_ne_of_lt (W := W) (a := W - 1) (b := W - 3) (by omega) (by omega) (by omega)
        have hne2 := zmod_ne_of_lt (W := W) (a := W - 1) (b := W - 2) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg hne3, if_neg hne2, if_pos rfl]; rfl
      · -- 0
        have h1 : ((W - 4 : ℕ) : ZMod W) + (4 : ℕ) = 0 := by
          rw [← neg_four_eq_natCast W (by omega)]; push_cast; ring
        rw [h1, if_pos rfl]; rfl
      · -- 1
        have h1 : ((W - 4 : ℕ) : ZMod W) + (5 : ℕ) = ((1 : ℕ) : ZMod W) := by
          rw [← neg_four_eq_natCast W (by omega)]; push_cast; ring
        rw [h1]
        have hne0 := zmod_ne_zero_of_lt (W := W) (a := 1) (by omega) (by omega)
        have hne3 := zmod_ne_of_lt (W := W) (a := 1) (b := W - 3) (by omega) (by omega) (by omega)
        have hne2 := zmod_ne_of_lt (W := W) (a := 1) (b := W - 2) (by omega) (by omega) (by omega)
        have hne1 := zmod_ne_of_lt (W := W) (a := 1) (b := W - 1) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg hne3, if_neg hne2, if_neg hne1]; rfl
  obtain ⟨hmatch1, hout1, hnz1⟩ := localRunNZ_sound hW6 base 40 bncInit bncEnd
    (fwdState n (n - 2)) valid_bnc hmatch0 run_bnc
  refine ⟨?_, hnz1⟩
  have hx1 : (antStep^[40] (fwdState n (n - 2))).x = ((3 * (n - 2) + 4 : ℕ) : ZMod W) := by
    rw [hmatch1.1, h3n2]; simp only [bncEnd, base]
    rw [neg_four_eq_natCast W (by omega), ← Nat.cast_add, show W - 4 + 1 = W - 3 by omega]
  have hy1 : (antStep^[40] (fwdState n (n - 2))).y = 0 := by rw [hmatch1.2.1]; rfl
  have hd1 : (antStep^[40] (fwdState n (n - 2))).dir = 3 := Fin.ext hmatch1.2.2.1
  cases hs : antStep^[40] (fwdState n (n - 2)) with
  | mk sx sy sd sg =>
    simp only [hs] at hx1 hy1 hd1 hmatch1 hout1
    dsimp only [WindowMatches] at hmatch1
    simp only [bwdState, AntState.mk.injEq]
    refine ⟨hx1, hy1, hd1, ?_⟩
    funext a b
    obtain ⟨hb_eq, hb_lt⟩ := zmod3_cases b
    by_cases ha : ∃ i : ℕ, i < 6 ∧ a = base + (i : ZMod W)
    · obtain ⟨i, hi, rfl⟩ := ha
      rw [hb_eq, hmatch1.2.2.2 i hi b.val hb_lt]
      simp only [bwdGrid, colMaskGrid, ZMod.val_natCast, Nat.mod_eq_of_lt hb_lt,
        base, h3n3, h3n2]
      simp only [neg_four_eq_natCast W (by omega), neg_two_eq_natCast W (by omega)]
      interval_cases i
      · -- W - 4
        have h1 : ((W - 4 : ℕ) : ZMod W) + (0 : ℕ) = ((W - 4 : ℕ) : ZMod W) := by simp
        rw [h1]
        have hne0 := zmod_ne_zero_of_lt (W := W) (a := W - 4) (by omega) (by omega)
        have hne1 := zmod_ne_of_lt (W := W) (a := W - 4) (b := 1) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne1), if_pos rfl]; rfl
      · -- W - 3
        have h1 : ((W - 4 : ℕ) : ZMod W) + (1 : ℕ) = ((W - 3 : ℕ) : ZMod W) := by
          rw [← Nat.cast_add, show W - 4 + 1 = W - 3 by omega]
        rw [h1]
        have hne0 := zmod_ne_zero_of_lt (W := W) (a := W - 3) (by omega) (by omega)
        have hne1 := zmod_ne_of_lt (W := W) (a := W - 3) (b := 1) (by omega) (by omega) (by omega)
        have hne4 := zmod_ne_of_lt (W := W) (a := W - 3) (b := W - 4) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne1), if_neg hne4, if_pos rfl]; rfl
      · -- W - 2
        have h1 : ((W - 4 : ℕ) : ZMod W) + (2 : ℕ) = ((W - 2 : ℕ) : ZMod W) := by
          rw [← Nat.cast_add, show W - 4 + 2 = W - 2 by omega]
        rw [h1]
        have hne0 := zmod_ne_zero_of_lt (W := W) (a := W - 2) (by omega) (by omega)
        have hne1 := zmod_ne_of_lt (W := W) (a := W - 2) (b := 1) (by omega) (by omega) (by omega)
        have hne4 := zmod_ne_of_lt (W := W) (a := W - 2) (b := W - 4) (by omega) (by omega) (by omega)
        have hne3 := zmod_ne_of_lt (W := W) (a := W - 2) (b := W - 3) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne1), if_neg hne4, if_neg hne3, if_pos rfl]; rfl
      · -- W - 1
        have h1 : ((W - 4 : ℕ) : ZMod W) + (3 : ℕ) = ((W - 1 : ℕ) : ZMod W) := by
          rw [← Nat.cast_add, show W - 4 + 3 = W - 1 by omega]
        rw [h1]
        have hne0 := zmod_ne_zero_of_lt (W := W) (a := W - 1) (by omega) (by omega)
        have hne1 := zmod_ne_of_lt (W := W) (a := W - 1) (b := 1) (by omega) (by omega) (by omega)
        have hne4 := zmod_ne_of_lt (W := W) (a := W - 1) (b := W - 4) (by omega) (by omega) (by omega)
        have hne3 := zmod_ne_of_lt (W := W) (a := W - 1) (b := W - 3) (by omega) (by omega) (by omega)
        have hne2 := zmod_ne_of_lt (W := W) (a := W - 1) (b := W - 2) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne1), if_neg hne4, if_neg hne3, if_neg hne2]; rfl
      · -- 0
        have h1 : ((W - 4 : ℕ) : ZMod W) + (4 : ℕ) = 0 := by
          rw [← neg_four_eq_natCast W (by omega)]; push_cast; ring
        rw [h1, if_pos rfl]; rfl
      · -- 1
        have h1 : ((W - 4 : ℕ) : ZMod W) + (5 : ℕ) = ((1 : ℕ) : ZMod W) := by
          rw [← neg_four_eq_natCast W (by omega)]; push_cast; ring
        rw [h1]
        have hne0 := zmod_ne_zero_of_lt (W := W) (a := 1) (by omega) (by omega)
        rw [if_neg hne0, if_pos (by simp)]; rfl
    · push Not at ha
      rw [hout1 a ha b]
      simp only [fwdState, fwdGrid, bwdGrid, colMaskGrid, h3n3, h3n2, h3n1]
      have hne0 : a ≠ 0 := by have := ha 4 (by omega); intro h; apply this; rw [h]; simp [base]
      have hne1 : a ≠ 1 := by have := ha 5 (by omega); intro h; apply this; rw [h]; simp [base]; ring
      have hne4 : a ≠ ((W - 4 : ℕ) : ZMod W) := by
        have := ha 0 (by omega); intro h; apply this; rw [h, ← neg_four_eq_natCast W (by omega)]; simp [base]
      have hne3 : a ≠ ((W - 3 : ℕ) : ZMod W) := by
        have := ha 1 (by omega); intro h; apply this; rw [h]; simp only [base]
        rw [neg_four_eq_natCast W (by omega), ← Nat.cast_add, show W - 4 + 1 = W - 3 by omega]
      have hne2 : a ≠ ((W - 2 : ℕ) : ZMod W) := by
        have := ha 2 (by omega); intro h; apply this; rw [h]; simp only [base]
        rw [neg_four_eq_natCast W (by omega), ← Nat.cast_add, show W - 4 + 2 = W - 2 by omega]
      have hne1' : a ≠ (-1 : ZMod W) := by
        have := ha 3 (by omega); intro h; apply this; rw [h]; simp only [base]; push_cast; ring
      have hne2' : a ≠ (-2 : ZMod W) := by
        rw [neg_two_eq_natCast W (by omega)]; exact hne2
      rw [if_neg hne0, if_neg hne3, if_neg hne2, if_neg hne1',
        if_neg hne0, if_neg hne1, if_neg hne4, if_neg hne3, if_neg hne2']

private lemma bwd_step {n k : ℕ} (hn : 2 ≤ n) (hk : k + 2 < n) :
    antStep^[18] (bwdState n (k + 1)) = bwdState n k ∧
    (∀ t : ℕ, 1 ≤ t → t ≤ 18 → (antStep^[t] (bwdState n (k + 1))).grid ≠ fun _ _ => false) := by
  set W := 3 * n + 1
  set base : ZMod W := ((3 * k + 3 : ℕ) : ZMod W)
  have hW5 : 5 ≤ W := by omega
  have hmatch0 : WindowMatches base 5 bwdInit (bwdState n (k + 1)) := by
    refine ⟨?_, rfl, rfl, ?_⟩
    · simp only [bwdState, bwdInit, base]; push_cast; ring
    · intro i hi y hy
      simp only [bwdState, bwdGrid, colMaskGrid, ZMod.val_natCast, Nat.mod_eq_of_lt hy, base]
      rw [← Nat.cast_add, neg_two_eq_natCast W (by omega)]
      interval_cases i
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 3 + 0) (by omega) (by omega)
        have hne1 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 0) (b := 1) (by omega) (by omega) (by omega)
        have hne6 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 0) (b := 3 * (k + 1) + 3) (by omega) (by omega) (by omega)
        have hne7 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 0) (b := 3 * (k + 1) + 4) (by omega) (by omega) (by omega)
        have hneW := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 0) (b := W - 2) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne1), if_neg hne6, if_neg hne7, if_neg hneW]; rfl
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 3 + 1) (by omega) (by omega)
        have hne1 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 1) (b := 1) (by omega) (by omega) (by omega)
        have hne6 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 1) (b := 3 * (k + 1) + 3) (by omega) (by omega) (by omega)
        have hne7 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 1) (b := 3 * (k + 1) + 4) (by omega) (by omega) (by omega)
        have hneW := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 1) (b := W - 2) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne1), if_neg hne6, if_neg hne7, if_neg hneW]; rfl
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 3 + 2) (by omega) (by omega)
        have hne1 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 2) (b := 1) (by omega) (by omega) (by omega)
        have hne6 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 2) (b := 3 * (k + 1) + 3) (by omega) (by omega) (by omega)
        have hne7 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 2) (b := 3 * (k + 1) + 4) (by omega) (by omega) (by omega)
        have hneW := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 2) (b := W - 2) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne1), if_neg hne6, if_neg hne7, if_neg hneW]; rfl
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 3 + 3) (by omega) (by omega)
        have hne1 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 3) (b := 1) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne1), if_pos (by push_cast; ring)]; rfl
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 3 + 4) (by omega) (by omega)
        have hne1 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 4) (b := 1) (by omega) (by omega) (by omega)
        have hne6 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 4) (b := 3 * (k + 1) + 3) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne1), if_neg hne6, if_pos (by push_cast; ring)]; rfl
  obtain ⟨hmatch1, hout1, hnz1⟩ := localRunNZ_sound hW5 base 18 bwdInit bwdEnd
    (bwdState n (k + 1)) valid_bwd hmatch0 run_bwd
  refine ⟨?_, hnz1⟩
  have hx1 : (antStep^[18] (bwdState n (k + 1))).x = ((3 * k + 4 : ℕ) : ZMod W) := by
    rw [hmatch1.1]; simp only [bwdEnd, base]; push_cast; ring
  have hy1 : (antStep^[18] (bwdState n (k + 1))).y = 0 := by rw [hmatch1.2.1]; rfl
  have hd1 : (antStep^[18] (bwdState n (k + 1))).dir = 3 := Fin.ext hmatch1.2.2.1
  cases hs : antStep^[18] (bwdState n (k + 1)) with
  | mk sx sy sd sg =>
    simp only [hs] at hx1 hy1 hd1 hmatch1 hout1
    dsimp only [WindowMatches] at hmatch1
    simp only [bwdState, AntState.mk.injEq]
    refine ⟨hx1, hy1, hd1, ?_⟩
    funext a b
    obtain ⟨hb_eq, hb_lt⟩ := zmod3_cases b
    by_cases ha : ∃ i : ℕ, i < 5 ∧ a = base + (i : ZMod W)
    · obtain ⟨i, hi, rfl⟩ := ha
      rw [hb_eq, hmatch1.2.2.2 i hi b.val hb_lt]
      simp only [bwdGrid, colMaskGrid, ZMod.val_natCast, Nat.mod_eq_of_lt hb_lt, base]
      rw [← Nat.cast_add, neg_two_eq_natCast W (by omega)]
      interval_cases i
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 3 + 0) (by omega) (by omega)
        have hne1 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 0) (b := 1) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne1), if_pos (by simp)]; rfl
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 3 + 1) (by omega) (by omega)
        have hne1 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 1) (b := 1) (by omega) (by omega) (by omega)
        have hne3 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 1) (b := 3 * k + 3) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne1), if_neg hne3, if_pos (by push_cast; ring)]; rfl
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 3 + 2) (by omega) (by omega)
        have hne1 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 2) (b := 1) (by omega) (by omega) (by omega)
        have hne3 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 2) (b := 3 * k + 3) (by omega) (by omega) (by omega)
        have hne4 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 2) (b := 3 * k + 4) (by omega) (by omega) (by omega)
        have hneW := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 2) (b := W - 2) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne1), if_neg hne3, if_neg hne4, if_neg hneW]; rfl
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 3 + 3) (by omega) (by omega)
        have hne1 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 3) (b := 1) (by omega) (by omega) (by omega)
        have hne3 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 3) (b := 3 * k + 3) (by omega) (by omega) (by omega)
        have hne4 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 3) (b := 3 * k + 4) (by omega) (by omega) (by omega)
        have hneW := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 3) (b := W - 2) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne1), if_neg hne3, if_neg hne4, if_neg hneW]; rfl
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3 * k + 3 + 4) (by omega) (by omega)
        have hne1 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 4) (b := 1) (by omega) (by omega) (by omega)
        have hne3 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 4) (b := 3 * k + 3) (by omega) (by omega) (by omega)
        have hne4 := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 4) (b := 3 * k + 4) (by omega) (by omega) (by omega)
        have hneW := zmod_ne_of_lt (W := W) (a := 3 * k + 3 + 4) (b := W - 2) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne1), if_neg hne3, if_neg hne4, if_neg hneW]; rfl
    · push Not at ha
      rw [hout1 a ha b]
      simp only [bwdState, bwdGrid, colMaskGrid]
      have hne3 : a ≠ ((3 * k + 3 : ℕ) : ZMod W) := by have := ha 0 (by omega); simpa [base] using this
      have hne4 : a ≠ ((3 * k + 4 : ℕ) : ZMod W) := by
        have := ha 1 (by omega); intro h; apply this; rw [h]; simp only [base]; push_cast; ring
      have hne6 : a ≠ ((3 * (k + 1) + 3 : ℕ) : ZMod W) := by
        have := ha 3 (by omega); intro h; apply this; rw [h]; simp only [base]; push_cast; ring
      have hne7 : a ≠ ((3 * (k + 1) + 4 : ℕ) : ZMod W) := by
        have := ha 4 (by omega); intro h; apply this; rw [h]; simp only [base]; push_cast; ring
      by_cases ha0 : a = 0
      · simp [ha0]
      · by_cases ha1 : a = 1
        · simp [ha1]
        · rw [if_neg ha0, if_neg ha1, if_neg ha0, if_neg ha1,
            if_neg hne6, if_neg hne7, if_neg hne3, if_neg hne4]

private lemma bwd_iter {n : ℕ} (hn : 2 ≤ n) :
    ∀ k ≤ n - 2,
      antStep^[18 * k] (bwdState n k) = bwdState n 0 ∧
      (∀ t : ℕ, 1 ≤ t → t ≤ 18 * k → (antStep^[t] (bwdState n k)).grid ≠ fun _ _ => false) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨rfl, fun t ht1 ht2 => by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨hstep, hnz_step⟩ := bwd_step hn (by omega : k + 2 < n)
    obtain ⟨hrest, hnz_rest⟩ := ih (by omega)
    refine ⟨?_, ?_⟩
    · rw [show 18 * (k + 1) = 18 * k + 18 by omega, Function.iterate_add_apply, hstep, hrest]
    · intro t ht1 ht2
      by_cases hle : t ≤ 18
      · exact hnz_step t ht1 hle
      · rw [show t = (t - 18) + 18 by omega, Function.iterate_add_apply, hstep]
        exact hnz_rest (t - 18) (by omega) (by omega)

private lemma finish_phase {n : ℕ} (hn : 2 ≤ n) :
    antStep^[16] (bwdState n 0) = halfState n ∧
    (∀ t : ℕ, 1 ≤ t → t ≤ 16 → (antStep^[t] (bwdState n 0)).grid ≠ fun _ _ => false) := by
  set W := 3 * n + 1
  have hW5 : 5 ≤ W := by omega
  have hmatch0 : WindowMatches (0 : ZMod W) 5 finInit (bwdState n 0) := by
    refine ⟨by simp [bwdState, finInit], rfl, rfl, ?_⟩
    intro i hi y hy
    simp only [bwdState, bwdGrid, colMaskGrid, ZMod.val_natCast, Nat.mod_eq_of_lt hy, zero_add]
    rw [neg_two_eq_natCast W (by omega)]
    interval_cases i
    · simp [finInit]
    · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 1) (by omega) (by omega)
      rw [if_neg hne0, if_pos (by simp)]; rfl
    · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 2) (by omega) (by omega)
      have hne1 := zmod_ne_of_lt (W := W) (a := 2) (b := 1) (by omega) (by omega) (by omega)
      have hne3 := zmod_ne_of_lt (W := W) (a := 2) (b := 3) (by omega) (by omega) (by omega)
      have hne4 := zmod_ne_of_lt (W := W) (a := 2) (b := 4) (by omega) (by omega) (by omega)
      have hneW := zmod_ne_of_lt (W := W) (a := 2) (b := W - 2) (by omega) (by omega) (by omega)
      rw [if_neg hne0, if_neg (by simpa using hne1), if_neg (by simpa using hne3),
        if_neg (by simpa using hne4), if_neg hneW]; rfl
    · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3) (by omega) (by omega)
      have hne1 := zmod_ne_of_lt (W := W) (a := 3) (b := 1) (by omega) (by omega) (by omega)
      rw [if_neg hne0, if_neg (by simpa using hne1), if_pos (by simp)]; rfl
    · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 4) (by omega) (by omega)
      have hne1 := zmod_ne_of_lt (W := W) (a := 4) (b := 1) (by omega) (by omega) (by omega)
      have hne3 := zmod_ne_of_lt (W := W) (a := 4) (b := 3) (by omega) (by omega) (by omega)
      rw [if_neg hne0, if_neg (by simpa using hne1), if_neg (by simpa using hne3), if_pos (by simp)]; rfl
  obtain ⟨hmatch1, hout1, hnz1⟩ := localRunNZ_sound hW5 (0 : ZMod W) 16 finInit finEnd
    (bwdState n 0) valid_fin hmatch0 run_fin
  refine ⟨?_, hnz1⟩
  have hx1 : (antStep^[16] (bwdState n 0)).x = 0 := by rw [hmatch1.1]; simp [finEnd]
  have hy1 : (antStep^[16] (bwdState n 0)).y = 2 := by rw [hmatch1.2.1]; rfl
  have hd1 : (antStep^[16] (bwdState n 0)).dir = 3 := Fin.ext hmatch1.2.2.1
  cases hs : antStep^[16] (bwdState n 0) with
  | mk sx sy sd sg =>
    simp only [hs] at hx1 hy1 hd1 hmatch1 hout1
    dsimp only [WindowMatches] at hmatch1
    simp only [halfState, AntState.mk.injEq]
    refine ⟨hx1, hy1, hd1, ?_⟩
    funext a b
    obtain ⟨hb_eq, hb_lt⟩ := zmod3_cases b
    by_cases ha : ∃ i : ℕ, i < 5 ∧ a = (0 : ZMod W) + (i : ZMod W)
    · obtain ⟨i, hi, rfl⟩ := ha
      rw [hb_eq, hmatch1.2.2.2 i hi b.val hb_lt]
      simp only [halfGrid, colMaskGrid, ZMod.val_natCast, Nat.mod_eq_of_lt hb_lt, zero_add]
      rw [neg_two_eq_natCast W (by omega)]
      interval_cases i
      · simp [finEnd]
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 1) (by omega) (by omega)
        have hne2 := zmod_ne_of_lt (W := W) (a := 1) (b := 2) (by omega) (by omega) (by omega)
        have hneW := zmod_ne_of_lt (W := W) (a := 1) (b := W - 2) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne2), if_neg hneW]; rfl
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 2) (by omega) (by omega)
        rw [if_neg hne0, if_pos (by simp)]; rfl
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 3) (by omega) (by omega)
        have hne2 := zmod_ne_of_lt (W := W) (a := 3) (b := 2) (by omega) (by omega) (by omega)
        have hneW := zmod_ne_of_lt (W := W) (a := 3) (b := W - 2) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne2), if_neg hneW]; rfl
      · have hne0 := zmod_ne_zero_of_lt (W := W) (a := 4) (by omega) (by omega)
        have hne2 := zmod_ne_of_lt (W := W) (a := 4) (b := 2) (by omega) (by omega) (by omega)
        have hneW := zmod_ne_of_lt (W := W) (a := 4) (b := W - 2) (by omega) (by omega) (by omega)
        rw [if_neg hne0, if_neg (by simpa using hne2), if_neg hneW]; rfl
    · push Not at ha
      rw [hout1 a ha b]
      simp only [bwdState, bwdGrid, halfGrid, colMaskGrid]
      have hne0 : a ≠ 0 := by have := ha 0 (by omega); simpa using this
      have hne1 : a ≠ 1 := by have := ha 1 (by omega); simpa using this
      have hne2 : a ≠ 2 := by have := ha 2 (by omega); simpa using this
      have hne3 : a ≠ ((3 * 0 + 3 : ℕ) : ZMod W) := by have := ha 3 (by omega); simpa using this
      have hne4 : a ≠ ((3 * 0 + 4 : ℕ) : ZMod W) := by have := ha 4 (by omega); simpa using this
      rw [if_neg hne0, if_neg hne1, if_neg hne3, if_neg hne4, if_neg hne0, if_neg hne2]

private lemma revRot180_halfState {n : ℕ} (hn : 2 ≤ n) :
    revRot180 (halfState n) = halfState n := by
  set W := 3 * n + 1
  simp only [revRot180, halfState, AntState.mk.injEq]
  refine ⟨?_, ?_, trivial, ?_⟩
  · have : dx W 3 = 0 := rfl
    rw [this]; ring
  · have : dy 3 = -1 := by decide
    rw [this]; decide
  · funext a b
    simp only [halfGrid, colMaskGrid]
    have h2ne : (2 : ZMod W) ≠ -2 := by
      rw [neg_two_eq_natCast W (by omega)]
      exact zmod_ne_of_lt (W := W) (a := 2) (b := W - 2) (by omega) (by omega) (by omega)
    have h2ne0 : (2 : ZMod W) ≠ 0 :=
      zmod_ne_zero_of_lt (W := W) (a := 2) (by omega) (by omega)
    have hm2ne0 : (-2 : ZMod W) ≠ 0 := by
      rw [neg_two_eq_natCast W (by omega)]
      exact zmod_ne_zero_of_lt (W := W) (a := W - 2) (by omega) (by omega)
    by_cases ha0 : a = 0
    · subst ha0
      simp only [neg_zero, ↓reduceIte]
      fin_cases b <;> decide
    · have hna0 : -a ≠ 0 := fun h => ha0 (by have := congrArg Neg.neg h; simpa using this)
      by_cases ha2 : a = 2
      · subst ha2
        rw [if_neg hna0, if_neg (Ne.symm h2ne), if_pos rfl, if_neg ha0, if_pos rfl]
        fin_cases b <;> decide
      · by_cases ham2 : a = -2
        · subst ham2
          rw [neg_neg, if_neg h2ne0, if_pos rfl, if_neg hm2ne0, if_neg (Ne.symm h2ne), if_pos rfl]
          fin_cases b <;> decide
        · have hna2 : -a ≠ 2 := fun h => ham2 (by have := congrArg Neg.neg h; simpa using this)
          have hnam2 : -a ≠ -2 := fun h => ha2 (by have := congrArg Neg.neg h; simpa using this)
          rw [if_neg hna0, if_neg hna2, if_neg hnam2, if_neg ha0, if_neg ha2, if_neg ham2,
            bitOf_zero, bitOf_zero]

/-! ### Part 5: Combining the 5 phases and time-reversal symmetry -/

private lemma half_trajectory {n : ℕ} (hn : 2 ≤ n) :
    antStep^[48 * n + 8] (initState (3 * n + 1)) = halfState n ∧
    (∀ t : ℕ, 1 ≤ t → t ≤ 48 * n + 8 →
      (antStep^[t] (initState (3 * n + 1))).grid ≠ fun _ _ => false) := by
  obtain ⟨h1, hnz1⟩ := start_phase hn
  obtain ⟨h2, hnz2⟩ := fwd_iter hn (n - 2) le_rfl
  obtain ⟨h3, hnz3⟩ := bounce_phase hn
  obtain ⟨h4, hnz4⟩ := bwd_iter hn (n - 2) le_rfl
  obtain ⟨h5, hnz5⟩ := finish_phase hn
  have h12 : antStep^[30 * n - 12] (initState (3 * n + 1)) = fwdState n (n - 2) := by
    rw [show 30 * n - 12 = 30 * (n - 2) + 48 by omega, Function.iterate_add_apply, h1, h2]
  have h123 : antStep^[30 * n + 28] (initState (3 * n + 1)) = bwdState n (n - 2) := by
    rw [show 30 * n + 28 = 40 + (30 * n - 12) by omega, Function.iterate_add_apply, h12, h3]
  have h1234 : antStep^[48 * n - 8] (initState (3 * n + 1)) = bwdState n 0 := by
    rw [show 48 * n - 8 = 18 * (n - 2) + (30 * n + 28) by omega, Function.iterate_add_apply, h123, h4]
  have h12345 : antStep^[48 * n + 8] (initState (3 * n + 1)) = halfState n := by
    rw [show 48 * n + 8 = 16 + (48 * n - 8) by omega, Function.iterate_add_apply, h1234, h5]
  refine ⟨h12345, fun t ht1 ht2 => ?_⟩
  by_cases c1 : t ≤ 48
  · exact hnz1 t ht1 c1
  · by_cases c2 : t ≤ 30 * n - 12
    · rw [show t = (t - 48) + 48 by omega, Function.iterate_add_apply, h1]
      exact hnz2 (t - 48) (by omega) (by omega)
    · by_cases c3 : t ≤ 30 * n + 28
      · rw [show t = (t - (30 * n - 12)) + (30 * n - 12) by omega, Function.iterate_add_apply, h12]
        exact hnz3 (t - (30 * n - 12)) (by omega) (by omega)
      · by_cases c4 : t ≤ 48 * n - 8
        · rw [show t = (t - (30 * n + 28)) + (30 * n + 28) by omega, Function.iterate_add_apply, h123]
          exact hnz4 (t - (30 * n + 28)) (by omega) (by omega)
        · rw [show t = (t - (48 * n - 8)) + (48 * n - 8) by omega, Function.iterate_add_apply, h1234]
          exact hnz5 (t - (48 * n - 8)) (by omega) (by omega)

theorem solve : type_of% @OMA.S_oeis_a386970.main := by
  intro n hn
  obtain ⟨hhalf, hnz⟩ := half_trajectory hn
  have hfix : revRot180 (antStep^[48 * n + 8] (initState (3 * n + 1))) =
      antStep^[48 * n + 8] (initState (3 * n + 1)) := by
    rw [hhalf]
    exact revRot180_halfState hn
  have hp := period_of_half_fixed (W := 3 * n + 1) (H := 48 * n + 8) (by omega) hfix hnz
  rwa [show 2 * (48 * n + 8) = 96 * n + 16 by omega] at hp

end A386970Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a386970.main :=
  A386970Proof.solve
