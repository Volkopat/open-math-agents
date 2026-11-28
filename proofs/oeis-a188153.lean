import OMAStatements.S_oeis_a188153

/-! An ordered walk on a square board determines an origin-anchored self-avoiding
path and one translation on each axis. The twenty bounding rectangles for seven
moves are counted by kernel computation. Their placement counts give the small
board values and the eventual quadratic, hence both identities of A188153.
The adjacent seven-site problem also uses the bounding-rectangle idea (PR 28679).
Credit: @ryansolves
-/

namespace EightSites

abbrev Point := ℤ × ℤ
abbrev Trace := Point × List Point

def neighbors (p : Point) : List Point :=
  [(p.1+1,p.2),(p.1-1,p.2),(p.1,p.2+1),(p.1,p.2-1)]

def extend (t : Trace) : List Trace :=
  let old := t.1 :: t.2
  ((neighbors t.1).filter fun q => q ∉ old).map fun q => (q, old)

def paths : ℕ → List Trace
  | 0 => [((0,0),[])]
  | k+1 => (paths k).flatMap extend

def axisSpan (f : Point → ℤ) (t : Trace) : ℕ :=
  let values := t.2.map f
  ((values.foldl max (f t.1)) - values.foldl min (f t.1)).toNat

def span (t : Trace) : ℕ × ℕ := (axisSpan Prod.fst t, axisSpan Prod.snd t)

abbrev Counts := List ((ℕ × ℕ) × ℕ)

def increment (key : ℕ × ℕ) : Counts → Counts
  | [] => [(key,1)]
  | (s,m) :: rest =>
    if s = key then (s,m+1) :: rest else (s,m) :: increment key rest

def tally (l : List Trace) : Counts := l.foldl (fun acc t => increment (span t) acc) []

def weighted (f : ℕ × ℕ → ℕ) (table : Counts) :=
  (table.map fun e => e.2 * f e.1).sum

theorem weighted_increment (f : ℕ × ℕ → ℕ) (s : ℕ × ℕ) (table : Counts) :
    weighted f (increment s table) = weighted f table + f s := by
  induction table with
  | nil => simp [increment, weighted]
  | cons e t ih =>
    obtain ⟨key,m⟩ := e
    by_cases he : key = s
    · subst key; simp [increment, weighted, Nat.add_mul]; omega
    · simp [increment, he, weighted] at ih ⊢; omega

theorem weighted_fold (f : ℕ × ℕ → ℕ) (l : List Trace) (acc : Counts) :
    weighted f (l.foldl (fun c t => increment (span t) c) acc) =
      weighted f acc + (l.map fun t => f (span t)).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons p t ih => simp [ih, weighted_increment, Nat.add_assoc]

def census : Counts :=
  [((7,0),2), ((6,1),28), ((5,1),68), ((5,2),84), ((4,1),72),
   ((4,2),208), ((4,3),140), ((3,1),28), ((3,2),280), ((3,3),240),
   ((3,4),140), ((2,2),112), ((2,3),280), ((2,4),208), ((2,5),84),
   ((1,3),28), ((1,4),72), ((1,5),68), ((1,6),28), ((0,7),2)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 3000000 in
theorem census_correct : tally (paths 7) = census := by
  decide +kernel

end EightSites

namespace EightSites

def sites (t : Trace) := t.1 :: t.2
def base (t : Trace) := t.2.getLastD t.1
def nextTo (a b : Point) : Prop := |a.1-b.1| + |a.2-b.2| = 1

theorem mem_neighbors (a b : Point) : a ∈ neighbors b ↔ nextTo a b := by
  rcases a with ⟨x,y⟩
  rcases b with ⟨u,v⟩
  simp [neighbors, nextTo, Prod.ext_iff]
  rcases le_total 0 (x-u) with hx|hx <;> rcases le_total 0 (y-v) with hy|hy <;>
    first | rw [abs_of_nonneg hx] | rw [abs_of_nonpos hx]
  all_goals first | rw [abs_of_nonneg hy] | rw [abs_of_nonpos hy]
  all_goals omega

theorem prev_mem (q p : Point) (l : List Point) (w : Trace) :
    (q,p::l) ∈ extend w ↔ w = (p,l) ∧ nextTo q p ∧ q ∉ p::l := by
  rcases w with ⟨v,t⟩
  simp only [extend, List.mem_map, List.mem_filter, decide_eq_true_eq, mem_neighbors,
    Prod.mk.injEq, List.cons.injEq]
  constructor
  · rintro ⟨a, ⟨ha,hn⟩, rfl, rfl, rfl⟩
    exact ⟨⟨rfl,rfl⟩,ha,hn⟩
  · rintro ⟨⟨rfl,rfl⟩,ha,hn⟩
    exact ⟨_,⟨ha,hn⟩,rfl,rfl,rfl⟩

theorem path_spec (k : ℕ) (t : Trace) : t ∈ paths k ↔
    t.2.length = k ∧ base t = 0 ∧ (sites t).Nodup ∧ (sites t).IsChain nextTo := by
  induction k generalizing t with
  | zero =>
    obtain ⟨p,l⟩ := t
    cases l <;> simp [paths, sites, base, Prod.ext_iff]
  | succ k ih =>
    obtain ⟨q,l⟩ := t
    cases l with
    | nil => simp [paths, extend, sites, List.mem_flatMap]
    | cons p l =>
      simp only [paths, List.mem_flatMap, prev_mem]
      have hb : base (q,p::l) = base (p,l) := List.getLastD_cons
      simp [ih, sites, hb, List.isChain_cons_cons,
        and_assoc, and_comm, and_left_comm]

theorem paths_nodup (k : ℕ) : (paths k).Nodup := by
  induction k with
  | zero => simp [paths]
  | succ k ih =>
    apply List.nodup_flatMap.mpr
    constructor
    · intro t _
      apply List.Nodup.map (fun _ _ h => congrArg Prod.fst h)
      apply List.Nodup.filter
      rcases t with ⟨⟨x,y⟩,l⟩
      simp [neighbors, Prod.ext_iff] <;> omega
    · apply ih.imp
      intro s t hs w hw hv
      rcases List.mem_map.mp hw with ⟨x,_,rfl⟩
      rcases List.mem_map.mp hv with ⟨y,_,hy⟩
      have he := congrArg Prod.snd hy
      exact hs (Prod.ext (List.cons.inj he.symm).1 (List.cons.inj he.symm).2)

theorem fold_lower (a x : ℤ) (l : List ℤ) :
    a ≤ l.foldl min x ↔ a ≤ x ∧ ∀ y ∈ l, a ≤ y := by
  induction l generalizing x with
  | nil => simp
  | cons y ys ih => simp [ih, le_min_iff, and_assoc]

theorem fold_upper (a x : ℤ) (l : List ℤ) :
    l.foldl max x < a ↔ x < a ∧ ∀ y ∈ l, y < a := by
  induction l generalizing x with
  | nil => simp
  | cons y ys ih => simp [ih, max_lt_iff, and_assoc]

def legalShift (n : ℕ) (f : Point → ℤ) (t : Trace) (a : ℤ) : Prop :=
  ∀ p ∈ sites t, 0 ≤ a + f p ∧ a + f p < n

def lower (f : Point → ℤ) (t : Trace) := (t.2.map f).foldl min (f t.1)
def upper (f : Point → ℤ) (t : Trace) := (t.2.map f).foldl max (f t.1)

theorem shift_bounds (n : ℕ) (f : Point → ℤ) (t : Trace) (a : ℤ) :
    legalShift n f t a ↔ -a ≤ lower f t ∧ upper f t < (n:ℤ)-a := by
  simp only [legalShift, sites, lower, upper, fold_lower, fold_upper,
    List.forall_mem_cons, List.forall_mem_map]
  constructor
  · rintro ⟨hx,h⟩
    exact ⟨⟨by omega,fun y hy => by have := h y hy; omega⟩,
      ⟨by omega,fun y hy => by have := h y hy; omega⟩⟩
  · rintro ⟨⟨hx,h⟩,⟨hy,g⟩⟩
    exact ⟨by omega,fun y hm => by have := h y hm; have := g y hm; omega⟩

theorem lower_le_upper (f : Point → ℤ) (t : Trace) : lower f t ≤ upper f t := by
  have hl := ((fold_lower (lower f t) (f t.1) (t.2.map f)).mp le_rfl).1
  have hu := ((fold_upper (upper f t + 1) (f t.1) (t.2.map f)).mp (by
    change upper f t < upper f t + 1; omega)).1
  omega

def shiftEquiv (n : ℕ) (f : Point → ℤ) (t : Trace) :
    {a : ℤ // legalShift n f t a} ≃ Fin (n - axisSpan f t) where
  toFun a := ⟨(a.val + lower f t).toNat, by
    have hb := (shift_bounds n f t a).mp a.property
    have hl := lower_le_upper f t
    change _ < n - (upper f t - lower f t).toNat
    omega⟩
  invFun i := ⟨(i.val : ℤ) - lower f t, by
    apply (shift_bounds _ _ _ _).mpr
    have hi := i.isLt
    change i.val < n - (upper f t - lower f t).toNat at hi
    omega⟩
  left_inv a := by
    apply Subtype.ext
    have := (shift_bounds _ _ _ _).mp a.property
    dsimp
    omega
  right_inv i := by apply Fin.ext; simp

end EightSites

namespace EightSites

def move (v : Point) (t : Trace) : Trace := (v + t.1, t.2.map (v + ·))

theorem sites_move (v : Point) (t : Trace) : sites (move v t) = (sites t).map (v + ·) := rfl
theorem base_move (v : Point) (t : Trace) : base (move v t) = v + base t :=
  List.getLastD_map

theorem move_move (u v : Point) (t : Trace) : move u (move v t) = move (u+v) t := by
  simp [move, List.map_map, Function.comp_def, add_assoc]

theorem move_zero (t : Trace) : move 0 t = t := by simp [move]

theorem shape_move (v : Point) (t : Trace) :
    ((sites (move v t)).Nodup ∧ (sites (move v t)).IsChain nextTo) ↔
      (sites t).Nodup ∧ (sites t).IsChain nextTo := by
  simp only [sites_move, List.nodup_map_iff (add_right_injective v), List.isChain_map]
  simp [nextTo]
  intro _
  rfl

def inside (n : ℕ) (p : Point) : Prop :=
  (0 ≤ p.1 ∧ p.1 < n) ∧ (0 ≤ p.2 ∧ p.2 < n)

abbrev OnBoard (n : ℕ) := {t : Trace // t.2.length = 7 ∧
  ((sites t).Nodup ∧ (sites t).IsChain nextTo) ∧ ∀ p ∈ sites t, inside n p}

def shapeSet : Finset Trace := ⟨(paths 7 : Multiset Trace), paths_nodup 7⟩
abbrev Shifts (n : ℕ) (t : Trace) :=
  {x : ℤ // legalShift n Prod.fst t x} × {y : ℤ // legalShift n Prod.snd t y}
abbrev Placed (n : ℕ) := Σ t : ↥shapeSet, Shifts n t.val

theorem onBoard_move (n : ℕ) (v : Point) (t : Trace) :
    (∀ p ∈ sites (move v t), inside n p) ↔
    legalShift n Prod.fst t v.1 ∧ legalShift n Prod.snd t v.2 := by
  simp only [sites_move, List.forall_mem_map, inside, legalShift, Prod.fst_add, Prod.snd_add]
  constructor
  · intro h
    exact ⟨fun p hp => (h p hp).1, fun p hp => (h p hp).2⟩
  · intro ⟨h,g⟩ p hp
    exact ⟨h p hp,g p hp⟩

theorem spec_shape (t : ↥shapeSet) :
    t.val.2.length = 7 ∧ base t.val = 0 ∧ (sites t.val).Nodup ∧ (sites t.val).IsChain nextTo :=
  (path_spec 7 t.val).mp t.property

def place {n : ℕ} (s : Placed n) : OnBoard n := by
  obtain ⟨t,x,y⟩ := s
  let v : Point := (x.val,y.val)
  refine ⟨move v t.val, ?_, (shape_move v t.val).mpr (spec_shape t).2.2, ?_⟩
  · simpa [move] using (spec_shape t).1
  · exact (onBoard_move n v t.val).mpr ⟨x.property,y.property⟩

theorem place_bijective (n : ℕ) : Function.Bijective (@place n) := by
  constructor
  · rintro ⟨s,x,y⟩ ⟨t,a,b⟩ eq
    have ht : move (x.val,y.val) s.val = move (a.val,b.val) t.val := congrArg Subtype.val eq
    have hv := congrArg base ht
    simp only [base_move, (spec_shape s).2.1, (spec_shape t).2.1, add_zero] at hv
    have hs := congrArg (move (-(x.val,y.val))) ht
    rw [← hv, move_move, move_move, neg_add_cancel, move_zero, move_zero] at hs
    have hst : s = t := Subtype.ext hs
    subst t
    have hx : x = a := Subtype.ext (congrArg Prod.fst hv)
    have hy : y = b := Subtype.ext (congrArg Prod.snd hv)
    cases hx; cases hy; rfl
  · intro t
    let v := base t.val
    let s := move (-v) t.val
    have back : move v s = t.val := by simp [s, move_move, move_zero]
    have hs : s ∈ shapeSet := by
      apply (path_spec 7 s).mpr
      refine ⟨?_, ?_, (shape_move (-v) t.val).mpr t.property.2.1⟩
      · simpa [s,move] using t.property.1
      · simp [s, base_move, v]
    have hfit := (onBoard_move n v s).mp (back ▸ t.property.2.2)
    exact ⟨⟨⟨s,hs⟩, ⟨v.1,hfit.1⟩, ⟨v.2,hfit.2⟩⟩, Subtype.ext back⟩

end EightSites

namespace EightSites
open OMA.S_oeis_a188153

abbrev Board (n : ℕ) := {w : Fin 8 → Fin n × Fin n // Function.Injective w ∧
  ∀ i : Fin 7, Adjacent (w i.castSucc) (w i.succ)}

def cell {n : ℕ} (p : Fin n × Fin n) : Point := (p.1.val,p.2.val)
theorem cell_inj {n : ℕ} : Function.Injective (@cell n) := by
  rintro ⟨x,y⟩ ⟨a,b⟩ h
  simp [cell, Prod.ext_iff] at h
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
theorem cell_inside {n : ℕ} (p : Fin n × Fin n) : inside n (cell p) := by
  simp [inside,cell]

def traceFn (f : Fin 8 → Point) : Trace := (f 0, List.ofFn fun i : Fin 7 => f i.succ)
theorem sites_fn (f : Fin 8 → Point) : sites (traceFn f) = List.ofFn f := List.ofFn_succ.symm
theorem sites_inj : Function.Injective sites := by
  rintro ⟨p,s⟩ ⟨q,t⟩ h
  obtain ⟨rfl,rfl⟩ := List.cons.inj h; rfl

theorem chain_fn (f : Fin 8 → Point) : (List.ofFn f).IsChain nextTo ↔
    ∀ i : Fin 7, nextTo (f i.castSucc) (f i.succ) := by
  rw [List.isChain_ofFn]
  constructor
  · intro h i; exact h i.val (by omega)
  · intro h j hj; exact h ⟨j,by omega⟩

def traceBoard {n : ℕ} (w : Board n) : OnBoard n := by
  let f := cell ∘ w.val
  refine ⟨traceFn f, by simp [traceFn], ?_, ?_⟩
  · rw [sites_fn, List.nodup_ofFn, chain_fn]
    exact ⟨cell_inj.comp w.property.1,w.property.2⟩
  · rw [sites_fn]
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact cell_inside _

theorem traceBoard_bijective (n : ℕ) : Function.Bijective (@traceBoard n) := by
  constructor
  · intro w z h
    have he := congrArg (fun x : OnBoard n => sites x.val) h
    change sites (traceFn (cell ∘ w.val)) = sites (traceFn (cell ∘ z.val)) at he
    rw [sites_fn,sites_fn] at he
    have hfn := List.ofFn_injective he
    exact Subtype.ext (funext fun i => cell_inj (congrFun hfn i))
  · intro t
    have hl : (sites t.val).length = 8 := by simp [sites,t.property.1]
    let pos (i : Fin 8) := (sites t.val)[i.val]'(by omega)
    have inside_pos (i : Fin 8) : inside n (pos i) :=
      t.property.2.2 (pos i) (List.getElem_mem _)
    let w (i : Fin 8) : Fin n × Fin n :=
      (⟨(pos i).1.toNat, by have := (inside_pos i).1; omega⟩,
       ⟨(pos i).2.toNat, by have := (inside_pos i).2; omega⟩)
    have recover : cell ∘ w = pos := by
      funext i
      exact Prod.ext (Int.toNat_of_nonneg (inside_pos i).1.1)
        (Int.toNat_of_nonneg (inside_pos i).2.1)
    have restore : List.ofFn pos = sites t.val := by
      apply List.ext_getElem
      · simp [hl]
      · intro j h₁ h₂; rw [List.getElem_ofFn]
    have inj := t.property.2.1.1
    have adj := t.property.2.1.2
    rw [← restore,List.nodup_ofFn] at inj
    rw [← restore,chain_fn,← recover] at adj
    have winj : Function.Injective w := fun i j e => inj (by rw [← recover]; exact congrArg cell e)
    refine ⟨⟨w,winj,adj⟩,Subtype.ext (sites_inj ?_)⟩
    change sites (traceFn (cell ∘ w)) = sites t.val
    rw [sites_fn,recover,restore]

end EightSites

/-! Eight-site square lattice walks. A seven-move word gives a translated
path, and its horizontal and vertical spans determine the number of placements. -/

namespace EightSites
open OMA.S_oeis_a188153 PowerSeries

def quadratic (x : ℤ) : ℤ := 2172 * x^2 - 12500 * x + 16096

def initial : ℕ → ℤ
  | 0 | 1 | 2 => 0
  | 3 => 112
  | 4 => 1976
  | 5 => 8160
  | 6 => 19312
  | n => quadratic n

set_option maxRecDepth 12000 in
theorem evaluate_series (seq : ℕ → ℤ) (count : ∀ n, seq n = initial n) :
    (mk seq * (1 - X)^3 =
      8 * X^3 * (2 + X) * (7 + 99*X + 111*X^2 - 15*X^3 - 18*X^4 - 3*X^5)) ∧
    ∀ n : ℕ, 9 < n → seq n = 3*seq (n-1) - 3*seq (n-2) + seq (n-3) := by
  have stable (n : ℕ) (hn : 7 ≤ n) : seq n = quadratic n := by
    rw [count]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.add_comm 7 k]
    rfl
  have difference (n : ℕ) (hn : 9 < n) :
      seq n = 3*seq (n-1) - 3*seq (n-2) + seq (n-3) := by
    simp (disch := omega) only [stable, quadratic, Nat.cast_sub, Nat.cast_one, Nat.cast_ofNat]
    ring
  refine ⟨?_, difference⟩
  let F := mk seq
  change F*(1-X)^3 = _
  rw [show F*(1-X)^3 = F - C 3*(F*X^1) + C 3*(F*X^2) - F*X^3 by
        simp only [map_ofNat]; ring,
    show (8*X^3*(2+X)*(7+99*X+111*X^2-15*X^3-18*X^4-3*X^5) : ℤ⟦X⟧) =
      C 112*X^3 + C 1640*X^4 + C 2568*X^5 + C 648*X^6 -
      C 408*X^7 - C 192*X^8 - C 24*X^9 by simp only [map_ofNat]; ring]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_C, F, coeff_mk]
  by_cases hn : n ≤ 9
  · interval_cases n <;> norm_num [count, initial, quadratic]
  · simp (disch := omega) only [if_pos, if_neg, add_zero, sub_zero]
    linarith [difference n (by omega)]

end EightSites

namespace EightSites
open OMA.S_oeis_a188153

def placements (n : ℕ) (s : ℕ × ℕ) := (n-s.1)*(n-s.2)

theorem enumerate_board (n : ℕ) : a n = weighted (placements n) census := by
  classical
  let e := (Equiv.ofBijective _ (traceBoard_bijective n)).trans
    ((Equiv.ofBijective _ (place_bijective n)).symm.trans
      (Equiv.sigmaCongrRight fun t : ↥shapeSet =>
        (shiftEquiv n Prod.fst t.val).prodCongr (shiftEquiv n Prod.snd t.val)))
  have cardBoard : a n = Fintype.card (Board n) := by
    unfold a Board
    rw [Fintype.card_subtype]
  rw [cardBoard,Fintype.card_congr e,Fintype.card_sigma]
  simp only [Fintype.card_prod,Fintype.card_fin]
  change (∑ t : ↥shapeSet, placements n (span t.val)) = _
  calc
    _ = ∑ t ∈ shapeSet, placements n (span t) := Finset.sum_attach _ _
    _ = ((paths 7).map fun t => placements n (span t)).sum := by
      rw [Finset.sum_eq_multiset_sum]; rfl
    _ = weighted (placements n) (tally (paths 7)) := by
      simpa [tally, weighted] using (weighted_fold (placements n) (paths 7) []).symm
    _ = _ := by rw [census_correct]

set_option maxRecDepth 24000 in
theorem evaluate_census (n : ℕ) : (weighted (placements n) census : ℤ) = initial n := by
  by_cases hn : n < 7
  · interval_cases n <;> decide
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show 7 ≤ n by omega)
  rw [Nat.add_comm] at hk
  subst n
  change _ = quadratic (k+7 : ℕ)
  simp only [weighted, census, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    placements, quadratic]
  push_cast [Nat.cast_sub (show 0 ≤ k+7 by omega),Nat.cast_sub (show 1 ≤ k+7 by omega),
    Nat.cast_sub (show 2 ≤ k+7 by omega),Nat.cast_sub (show 3 ≤ k+7 by omega),
    Nat.cast_sub (show 4 ≤ k+7 by omega),Nat.cast_sub (show 5 ≤ k+7 by omega),
    Nat.cast_sub (show 6 ≤ k+7 by omega),Nat.cast_sub (show 7 ≤ k+7 by omega)]
  ring

end EightSites

open EightSites OMA.S_oeis_a188153 in
theorem OMA.solution : type_of% @OMA.S_oeis_a188153.main := by
  apply evaluate_series
  intro n
  rw [enumerate_board]
  exact evaluate_census n
