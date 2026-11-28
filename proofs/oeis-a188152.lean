import OMAStatements.S_oeis_a188152

/-!
# Seven-site self-avoiding walks on a square

Hardin recorded the eventual quadratic empirically, and Barker conjectured the
generating function and recurrence in OEIS A188152. Count translations of each
walk by its bounding rectangle, as in Guttmann, Jensen and Owczarek (2022), §3.
-/

namespace A188152Proof
open OMA.S_oeis_a188152 Finset

abbrev Dir := Fin 6 → Fin 4
abbrev Point := ℤ × ℤ

def step (v : Fin 4) : Point :=
  match v.val with
  | 0 => (1, 0)
  | 1 => (-1, 0)
  | 2 => (0, 1)
  | _ => (0, -1)

def walkAux (d : Dir) : ℕ → Point
  | 0 => 0
  | k+1 => walkAux d k + step (d ⟨k % 6, Nat.mod_lt _ (by decide)⟩)

def walk (d : Dir) (i : Fin 7) : Point := walkAux d i.val

def valid (d : Dir) : Prop := Function.Injective (walk d)
instance (d : Dir) : Decidable (valid d) :=
  inferInstanceAs (Decidable (∀ i j : Fin 7, walk d i = walk d j → i = j))

def coord (axis : Bool) (z : Point) : ℤ := if axis then z.1 else z.2

def lo (d : Dir) (axis : Bool) : ℤ :=
  univ.inf' univ_nonempty (fun i => coord axis (walk d i))

def hi (d : Dir) (axis : Bool) : ℤ :=
  univ.sup' univ_nonempty (fun i => coord axis (walk d i))

def width (d : Dir) (axis : Bool) : ℕ := (hi d axis - lo d axis).toNat

/-- Translate an integer coordinate profile into the interval [0,n). -/
noncomputable def translationEquivOfBounds (n : ℕ) (z : Fin 7 → ℤ) (lo hi : ℤ)
    (hlo : ∀ i, lo ≤ z i) (hhi : ∀ i, z i ≤ hi)
    (elo : ∃ i, z i = lo) (ehi : ∃ i, z i = hi) :
    {t : ℤ // ∀ i, 0 ≤ t + z i ∧ t + z i < n} ≃ Fin (n - (hi - lo).toNat) := by
  let il := elo.choose
  let ih := ehi.choose
  have eil : z il = lo := elo.choose_spec
  have eih : z ih = hi := ehi.choose_spec
  have hlh := hlo ih
  rw [eih] at hlh
  exact {
    toFun := fun t => ⟨(t.val + lo).toNat, by
      have h₀ := (t.property il).1
      have h₁ := (t.property ih).2
      rw [eil] at h₀
      rw [eih] at h₁
      omega⟩
    invFun := fun k => ⟨(k.val : ℤ) - lo, fun i => by
      have := k.isLt
      have := hlo i
      have := hhi i
      omega⟩
    left_inv := fun t => Subtype.ext (by
      have h₀ := (t.property il).1
      rw [eil] at h₀
      dsimp
      omega)
    right_inv := fun k => Fin.ext (by dsimp; omega) }

/-- Available placements along one axis are the integers from -lo to n-1-hi. -/
noncomputable def axisEquiv (n : ℕ) (d : Dir) (axis : Bool) :
    {t : ℤ // ∀ i, 0 ≤ t + coord axis (walk d i) ∧ t + coord axis (walk d i) < n} ≃
      Fin (n - width d axis) := by
  let z := fun i => coord axis (walk d i)
  apply translationEquivOfBounds n z (lo d axis) (hi d axis)
  · exact fun i => Finset.inf'_le z (Finset.mem_univ i)
  · exact fun i => Finset.le_sup' z (Finset.mem_univ i)
  · obtain ⟨i, _, he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty z
    exact ⟨i, he.symm⟩
  · obtain ⟨i, _, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty z
    exact ⟨i, he.symm⟩

private abbrev BoardWalk (n : ℕ) := {w : Fin 7 → Fin n × Fin n //
  Function.Injective w ∧ ∀ i : Fin 6, Adjacent (w i.castSucc) (w i.succ)}

private abbrev Offset (n : ℕ) (d : Dir) (b : Bool) :=
  {t : ℤ // ∀ i, 0 ≤ t + coord b (walk d i) ∧ t + coord b (walk d i) < n}

private def cell {n : ℕ} (p : Fin n × Fin n) : Point := ((p.1.val : ℤ), (p.2.val : ℤ))

private theorem cell_inj {n : ℕ} : Function.Injective (@cell n) := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  exact Prod.ext (Fin.ext (by simpa [cell] using hx)) (Fin.ext (by simpa [cell] using hy))

private def readDir (p q : Point) : Fin 4 :=
  if q.1 = p.1 + 1 then 0 else if q.1 = p.1 - 1 then 1
  else if q.2 = p.2 + 1 then 2 else 3

private theorem step_readDir {n : ℕ} (p q : Fin n × Fin n) (ha : Adjacent p q) :
    cell p + step (readDir (cell p) (cell q)) = cell q := by
  simp only [Adjacent] at ha
  have dirs :
      ((q.1 : ℤ) = p.1 + 1 ∧ (q.2 : ℤ) = p.2) ∨
      ((q.1 : ℤ) = p.1 - 1 ∧ (q.2 : ℤ) = p.2) ∨
      ((q.1 : ℤ) = p.1 ∧ (q.2 : ℤ) = p.2 + 1) ∨
      ((q.1 : ℤ) = p.1 ∧ (q.2 : ℤ) = p.2 - 1) := by
    rw [abs_eq_max_neg, abs_eq_max_neg, max_def, max_def] at ha
    split_ifs at ha <;> omega
  rcases dirs with h | h | h | h
  all_goals
    apply Prod.ext <;>
      simp [cell, readDir, step, h.1, h.2, sub_eq_add_neg]

private theorem readDir_step (p : Point) (v : Fin 4) :
    readDir p (p + step v) = v := by
  fin_cases v <;> simp [readDir, step] <;> omega

private theorem walk_succ (d : Dir) (i : Fin 6) :
    walk d i.succ = walk d i.castSucc + step (d i) := by
  change walkAux d (i.val + 1) = walkAux d i.val + step (d i)
  simp [walkAux, Nat.mod_eq_of_lt i.isLt]

private def wordOf {n : ℕ} (w : BoardWalk n) : Dir :=
  fun i => readDir (cell (w.val i.castSucc)) (cell (w.val i.succ))

private theorem position_eq {n : ℕ} (w : BoardWalk n) (i : Fin 7) :
    cell (w.val i) = cell (w.val 0) + walk (wordOf w) i := by
  induction i using Fin.induction with
  | zero => simp [walk, walkAux]
  | succ i ih =>
    rw [walk_succ, ← add_assoc, ← ih]
    exact (step_readDir _ _ (w.property.2 i)).symm

private theorem word_valid {n : ℕ} (w : BoardWalk n) : valid (wordOf w) := by
  intro i j eq
  apply w.property.1
  apply cell_inj
  rw [position_eq w i, position_eq w j, eq]

private def anchor {n : ℕ} (w : BoardWalk n) (b : Bool) : Offset n (wordOf w) b :=
  ⟨coord b (cell (w.val 0)), fun i => by
    have eq := congrArg (coord b) (position_eq w i)
    cases b <;> simp [coord, cell] at eq ⊢ <;> omega⟩

private def draw {n : ℕ} {d : Dir} (x : Offset n d true) (y : Offset n d false)
    (i : Fin 7) : Fin n × Fin n :=
  (⟨(x.val + (walk d i).1).toNat, by have h := x.property i; simp [coord] at h; omega⟩,
   ⟨(y.val + (walk d i).2).toNat, by have h := y.property i; simp [coord] at h; omega⟩)

private theorem cell_draw {n : ℕ} {d : Dir} (x : Offset n d true) (y : Offset n d false)
    (i : Fin 7) : cell (draw x y i) = (x.val, y.val) + walk d i := by
  have hx := (x.property i).1
  have hy := (y.property i).1
  simp only [coord, if_true, Bool.false_eq_true, if_false] at hx hy
  apply Prod.ext <;> simp [draw, cell, hx, hy]

private def drawWalk {n : ℕ} (d : {d : Dir // valid d})
    (x : Offset n d.val true) (y : Offset n d.val false) : BoardWalk n :=
  ⟨draw x y, by
    constructor
    · intro i j eq
      apply d.property
      have h := congrArg cell eq
      simpa only [cell_draw, add_right_inj] using h
    · intro i
      have eq : cell (draw x y i.succ) = cell (draw x y i.castSucc) + step (d.val i) := by
        rw [cell_draw, cell_draw, walk_succ, add_assoc]
      have hx := congrArg Prod.fst eq
      have hy := congrArg Prod.snd eq
      have ds : ∀ v : Fin 4, |(step v).1| + |(step v).2| = 1 := by decide
      have hs := ds (d.val i)
      simp only [cell, Prod.fst_add, Prod.snd_add] at hx hy
      simp only [Adjacent, hx, hy]
      simpa using hs⟩

private theorem drawn_word {n : ℕ} (d : {d : Dir // valid d})
    (x : Offset n d.val true) (y : Offset n d.val false) :
    wordOf (drawWalk d x y) = d.val := by
  funext i
  change readDir (cell (draw x y i.castSucc)) (cell (draw x y i.succ)) = d.val i
  rw [cell_draw, cell_draw, walk_succ, ← add_assoc, readDir_step]

private abbrev Placed (n : ℕ) := Σ d : {d : Dir // valid d},
    Offset n d.val true × Offset n d.val false

private def toBoard {n : ℕ} (s : Placed n) : BoardWalk n :=
  drawWalk s.1 s.2.1 s.2.2

private def fromBoard {n : ℕ} (w : BoardWalk n) : Placed n :=
  ⟨⟨wordOf w, word_valid w⟩, anchor w true, anchor w false⟩

private theorem to_from {n : ℕ} (w : BoardWalk n) : toBoard (fromBoard w) = w := by
  apply Subtype.ext
  funext i
  apply cell_inj
  change cell (draw (anchor w true) (anchor w false) i) = cell (w.val i)
  rw [cell_draw, position_eq w i]
  rfl

private theorem toBoard_inj {n : ℕ} : Function.Injective (@toBoard n) := by
  rintro ⟨d, x, y⟩ ⟨d', x', y'⟩ eq
  change drawWalk d x y = drawWalk d' x' y' at eq
  have deq := congrArg wordOf eq
  rw [drawn_word, drawn_word] at deq
  have he : d = d' := Subtype.ext deq
  subst d'
  have origin := congrArg (fun w : BoardWalk n => cell (w.val 0)) eq
  change cell (draw x y 0) = cell (draw x' y' 0) at origin
  simp only [cell_draw, add_left_inj, Prod.mk.injEq] at origin
  have hx : x = x' := Subtype.ext origin.1
  have hy : y = y' := Subtype.ext origin.2
  subst x'
  subst y'
  rfl

private noncomputable def placements (n : ℕ) : BoardWalk n ≃ Placed n :=
  (Equiv.ofBijective toBoard ⟨toBoard_inj, fun w => ⟨fromBoard w, to_from w⟩⟩).symm

private theorem count_by_equiv (n : ℕ)
    (e : {w : Fin 7 → Fin n × Fin n // Function.Injective w ∧
          ∀ i : Fin 6, Adjacent (w i.castSucc) (w i.succ)} ≃
      (Σ d : {d : Dir // valid d}, Fin (n-width d.val true) × Fin (n-width d.val false))) :
    a n = ∑ d : Dir, if valid d then (n-width d true)*(n-width d false) else 0 := by
  rw [a, ← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (p := valid) (univ.filter valid)
    (fun d => by simp only [mem_filter, mem_univ, true_and])
    (fun d => (n - width d true) * (n - width d false))).symm

/-- Every walk is specified by its direction word and one allowed translation in each axis. -/
theorem count_arrays (n : ℕ) :
    a n = ∑ d : Dir, if valid d then (n-width d true)*(n-width d false) else 0 := by
  apply count_by_equiv
  exact (placements n).trans (Equiv.sigmaCongrRight fun d =>
    (axisEquiv n d.val true).prodCongr (axisEquiv n d.val false))

private abbrev SpanPair := ℕ × ℕ

private def spans : Multiset SpanPair :=
  ((Finset.univ.filter valid).val.map (fun d => (width d true, width d false)))

/-- Width and height of the bounding rectangle of each six-move self-avoiding walk. -/
private def spanTable : List SpanPair :=
  List.replicate 2 ((0, 6)) ++
  List.replicate 40 ((1, 3)) ++
  List.replicate 48 ((1, 4)) ++
  List.replicate 24 ((1, 5)) ++
  List.replicate 112 ((2, 2)) ++
  List.replicate 120 ((2, 3)) ++
  List.replicate 60 ((2, 4)) ++
  List.replicate 40 ((3, 1)) ++
  List.replicate 120 ((3, 2)) ++
  List.replicate 80 ((3, 3)) ++
  List.replicate 48 ((4, 1)) ++
  List.replicate 60 ((4, 2)) ++
  List.replicate 24 ((5, 1)) ++
  List.replicate 2 ((6, 0))

set_option maxHeartbeats 6000000 in
private theorem span_counts : spans = (spanTable : Multiset SpanPair) := by
  decide +kernel

private def placementCount (n : ℕ) (s : SpanPair) : ℕ :=
  (n - s.1) * (n - s.2)

private theorem walk_counts
    (count : ∀ n, a n = ∑ d : Dir,
      if valid d then (n - width d true) * (n - width d false) else 0) :
    (a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 112 ∧ a 4 = 1248 ∧ a 5 = 4152) ∧
    ∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 780*(n:ℤ)^2 - 3960*n + 4432 := by
  have hc (n : ℕ) : a n = (spanTable.map (placementCount n)).sum := by
    rw [count, ← Finset.sum_filter, Finset.sum_eq_multiset_sum]
    change ((Finset.univ.filter valid).val.map
      ((placementCount n) ∘ fun d => (width d true, width d false))).sum = _
    rw [← Multiset.map_map]
    change (spans.map (placementCount n)).sum = _
    rw [span_counts, Multiset.map_coe, Multiset.sum_coe]
  constructor
  · simp only [hc]
    decide +kernel
  intro n hn
  rw [hc]
  simp only [spanTable, List.map_append, List.sum_append, List.map_replicate,
    List.sum_replicate, nsmul_eq_mul, placementCount]
  push_cast [Nat.cast_sub (show 0 ≤ n by omega), Nat.cast_sub (show 1 ≤ n by omega),
    Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega),
    Nat.cast_sub (show 4 ≤ n by omega), Nat.cast_sub (show 5 ≤ n by omega), Nat.cast_sub hn]
  ring

open PowerSeries

private theorem finish (a : ℕ → ℕ)
    (small : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 112 ∧ a 4 = 1248 ∧ a 5 = 4152)
    (large : ∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 780*(n : ℤ)^2 - 3960*(n : ℤ) + 4432) :
    (mk (fun n => (a n : ℤ)) * (1-X)^3 =
      4*X^3*(28+228*X+186*X^2-18*X^3-29*X^4-5*X^5)) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 3*a (n-1) - 3*a (n-2) + a (n-3) := by
  have recurrence (n : ℕ) (hn : 8 < n) :
      (a n : ℤ) = 3*a (n-1) - 3*a (n-2) + a (n-3) := by
    simp (disch := omega) only [large, Nat.cast_sub, Nat.cast_ofNat, Nat.cast_one]
    ring
  refine ⟨?_, recurrence⟩
  let S := mk (fun n => (a n : ℤ))
  change S*(1-X)^3 = _
  rw [show S*(1-X)^3 = S - C 3*(S*X^1) + C 3*(S*X^2) - S*X^3 by
        simp only [map_ofNat]; ring,
      show (4*X^3*(28+228*X+186*X^2-18*X^3-29*X^4-5*X^5) : ℤ⟦X⟧) =
        C 112*X^3 + C 912*X^4 + C 744*X^5 - C 72*X^6 - C 116*X^7 - C 20*X^8 by
        simp only [map_ofNat]; ring]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_C, S, coeff_mk]
  by_cases hn : n ≤ 8
  · obtain ⟨h0,h1,h2,h3,h4,h5⟩ := small
    interval_cases n <;> norm_num [h0,h1,h2,h3,h4,h5,large]
  · simp (disch := omega) only [if_pos, if_neg, add_zero, sub_zero]
    linarith [recurrence n (by omega)]

end A188152Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a188152.main := by
  obtain ⟨hs, hp⟩ := A188152Proof.walk_counts A188152Proof.count_arrays
  exact A188152Proof.finish _ hs hp
