import OMAStatements.S_oeis_a165378
import Mathlib

/-!
# Proof of OEIS A165378

We prove Colin Barker's closed form `9 * n ^ 2 + 4 * n - 2` (for all `n > 3`) for the number
of R. H. Hardin's slanted `n x 4` arrays with entries in `Fin 4` having fixed corners
`(0, 0) = 0`, `(0, 3) = 1`, `(n - 1, 0) = 2`, `(n - 1, 3) = 3`, each color orthogonally
connected, and every cell having at most two orthogonal neighbors of its own color.

## Proof Strategy

1. **Row-by-row deterministic transfer automaton**: We track a finite state `(row, deg123, comp, cl0, cl1)`
   encoding the current row colors, the prefix degrees of columns `1, 2, 3`, the connected-component
   partition of the current row inside rows `0..k`, and which of colors `0, 1` have already closed.
   Using a Cut-Row Lemma and a prefix-connectivity invariant `PrefixOk`, we prove an exact bijection
   between valid `n`-row boards and accepting `n`-row automaton runs, reducing the cardinality to the
   backward continuation count `ways`.
2. **Closed-form quadratic transfer vector**: Starting from the 16 initial states, only 390 states
   are reachable (forbidding closing colors `2` and `3`, which must appear in the final row).
   We verify the exact transition table on all 390 states and prove by linearity of the transfer
   operator `T` that for every `m : ℕ` and every reachable state `i`,
   `ways (m + 3) (stateOf i) = a0Vec i + a1Vec i * m + a2Vec i * m ^ 2`.
   Summing over the 16 initial states yields `158 + 76 * m + 9 * m ^ 2 = 9 * n ^ 2 + 4 * n - 2`.
-/

namespace OMA.Allow165378
open OMA.S_oeis_a165378

/-! ### Part 1: Finite types and automaton definitions -/

private inductive C4
  | a0 | a1 | a2 | a3
  deriving DecidableEq

private inductive D3
  | d0 | d1 | d2
  deriving DecidableEq

private inductive C8
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7
  deriving DecidableEq

private def C4.eqb : C4 → C4 → Bool
  | .a0, .a0 => true | .a1, .a1 => true | .a2, .a2 => true | .a3, .a3 => true | _, _ => false

private def D3.eqb : D3 → D3 → Bool
  | .d0, .d0 => true | .d1, .d1 => true | .d2, .d2 => true | _, _ => false

private def C8.eqb : C8 → C8 → Bool
  | .x0, .x0 => true | .x1, .x1 => true | .x2, .x2 => true | .x3, .x3 => true
  | .x4, .x4 => true | .x5, .x5 => true | .x6, .x6 => true | .x7, .x7 => true | _, _ => false

private lemma C4.eqb_iff (a b : C4) : a.eqb b = true ↔ a = b := by
  cases a <;> cases b <;> decide

private lemma D3.eqb_iff (a b : D3) : a.eqb b = true ↔ a = b := by
  cases a <;> cases b <;> decide

private lemma C8.eqb_iff (a b : C8) : a.eqb b = true ↔ a = b := by
  cases a <;> cases b <;> decide

private def C4.toFin : C4 → Fin 4
  | .a0 => 0 | .a1 => 1 | .a2 => 2 | .a3 => 3

private def C4.ofFin : Fin 4 → C4
  | ⟨0, _⟩ => .a0 | ⟨1, _⟩ => .a1 | ⟨2, _⟩ => .a2 | ⟨3, _⟩ => .a3

private def c4Equiv : C4 ≃ Fin 4 where
  toFun := C4.toFin
  invFun := C4.ofFin
  left_inv x := by cases x <;> rfl
  right_inv x := by fin_cases x <;> rfl

private lemma C4.toFin_injective : Function.Injective C4.toFin := c4Equiv.injective
private lemma C4.ofFin_injective : Function.Injective C4.ofFin := c4Equiv.symm.injective
private lemma C4.toFin_ofFin (x : Fin 4) : (C4.ofFin x).toFin = x := c4Equiv.right_inv x
private lemma C4.ofFin_toFin (x : C4) : C4.ofFin x.toFin = x := c4Equiv.left_inv x

private def C4.toC8 : C4 → C8
  | .a0 => .x0 | .a1 => .x1 | .a2 => .x2 | .a3 => .x3

private lemma C4.toC8_injective : Function.Injective C4.toC8 := by
  intro a b h; cases a <;> cases b <;> simp_all [C4.toC8]

private def D3.toNat : D3 → ℕ
  | .d0 => 0 | .d1 => 1 | .d2 => 2

private structure Row where
  c0 : C4
  c1 : C4
  c2 : C4
  c3 : C4
  deriving DecidableEq

private def Row.get (r : Row) : Fin 4 → C4
  | ⟨0, _⟩ => r.c0 | ⟨1, _⟩ => r.c1 | ⟨2, _⟩ => r.c2 | ⟨3, _⟩ => r.c3

private def Row.ofFn (g : Fin 4 → C4) : Row := ⟨g 0, g 1, g 2, g 3⟩

private def rowEquiv : Row ≃ (Fin 4 → C4) where
  toFun := Row.get
  invFun := Row.ofFn
  left_inv r := by cases r; rfl
  right_inv g := by funext j; fin_cases j <;> rfl

private instance : Fintype C4 := Fintype.ofEquiv (Fin 4) c4Equiv.symm
private instance : Fintype Row := Fintype.ofEquiv (Fin 4 → C4) rowEquiv.symm

private def Row.eqb (r s : Row) : Bool :=
  r.c0.eqb s.c0 && r.c1.eqb s.c1 && r.c2.eqb s.c2 && r.c3.eqb s.c3

private lemma Row.eqb_iff (r s : Row) : r.eqb s = true ↔ r = s := by
  cases r; cases s
  simp [Row.eqb, C4.eqb_iff, and_assoc]

private structure State where
  r0 : C4
  r1 : C4
  r2 : C4
  r3 : C4
  d1 : D3
  d2 : D3
  d3 : D3
  p0 : C4
  p1 : C4
  p2 : C4
  p3 : C4
  cl0 : Bool
  cl1 : Bool
  deriving DecidableEq

private def State.eqb (s t : State) : Bool :=
  s.r0.eqb t.r0 && s.r1.eqb t.r1 && s.r2.eqb t.r2 && s.r3.eqb t.r3 &&
  s.d1.eqb t.d1 && s.d2.eqb t.d2 && s.d3.eqb t.d3 &&
  s.p0.eqb t.p0 && s.p1.eqb t.p1 && s.p2.eqb t.p2 && s.p3.eqb t.p3 &&
  (s.cl0 == t.cl0) && (s.cl1 == t.cl1)

private lemma State.eqb_iff (s t : State) : s.eqb t = true ↔ s = t := by
  cases s; cases t
  simp [State.eqb, C4.eqb_iff, D3.eqb_iff, and_assoc]

private def State.row (s : State) : Fin 4 → C4
  | ⟨0, _⟩ => s.r0 | ⟨1, _⟩ => s.r1 | ⟨2, _⟩ => s.r2 | ⟨3, _⟩ => s.r3

private def State.comp (s : State) : Fin 4 → C4
  | ⟨0, _⟩ => s.p0 | ⟨1, _⟩ => s.p1 | ⟨2, _⟩ => s.p2 | ⟨3, _⟩ => s.p3

private def State.closed (s : State) : C4 → Bool
  | .a0 => s.cl0 | .a1 => s.cl1 | .a2 => false | .a3 => false

private structure Comp8 where
  c0 : C8
  c1 : C8
  c2 : C8
  c3 : C8
  c4 : C8
  c5 : C8
  c6 : C8
  c7 : C8

private def Comp8.get (c : Comp8) : Fin 8 → C8
  | ⟨0, _⟩ => c.c0 | ⟨1, _⟩ => c.c1 | ⟨2, _⟩ => c.c2 | ⟨3, _⟩ => c.c3
  | ⟨4, _⟩ => c.c4 | ⟨5, _⟩ => c.c5 | ⟨6, _⟩ => c.c6 | ⟨7, _⟩ => c.c7

private def Comp8.union (c : Comp8) (ca cb : C8) : Comp8 :=
  if ca.eqb cb then c else
  let rep (x : C8) := if x.eqb cb then ca else x
  ⟨rep c.c0, rep c.c1, rep c.c2, rep c.c3, rep c.c4, rep c.c5, rep c.c6, rep c.c7⟩

private lemma Comp8.union_get (c : Comp8) (ca cb : C8) (x : Fin 8) :
    (c.union ca cb).get x = if c.get x = cb then ca else c.get x := by
  unfold Comp8.union
  by_cases h : ca = cb
  · subst h
    have h1 : ca.eqb ca = true := (C8.eqb_iff _ _).2 rfl
    rw [if_pos h1]
    split_ifs with hx
    · exact hx
    · rfl
  · have h1 : ca.eqb cb = false := by
      cases he : ca.eqb cb
      · rfl
      · exact absurd ((C8.eqb_iff _ _).1 he) h
    rw [if_neg (by simp [h1])]
    fin_cases x <;> simp only [Comp8.get, C8.eqb_iff] <;> split_ifs <;> simp_all

private lemma Comp8.union_eq_iff (c : Comp8) (a b x y : Fin 8) :
    (c.union (c.get a) (c.get b)).get x = (c.union (c.get a) (c.get b)).get y ↔
      c.get x = c.get y ∨
        (c.get x = c.get a ∧ c.get y = c.get b) ∨
          (c.get x = c.get b ∧ c.get y = c.get a) := by
  rw [Comp8.union_get, Comp8.union_get]
  by_cases hx : c.get x = c.get b <;> by_cases hy : c.get y = c.get b
  · rw [if_pos hx, if_pos hy]
    exact ⟨fun _ => Or.inl (hx.trans hy.symm), fun _ => rfl⟩
  · rw [if_pos hx, if_neg hy]
    constructor
    · intro h; exact Or.inr (Or.inr ⟨hx, h.symm⟩)
    · rintro (h | ⟨_, h2⟩ | ⟨_, h2⟩)
      · exact absurd (h.symm.trans hx) hy
      · exact absurd h2 hy
      · exact h2.symm
  · rw [if_neg hx, if_pos hy]
    constructor
    · intro h; exact Or.inr (Or.inl ⟨h, hy⟩)
    · rintro (h | ⟨h1, _⟩ | ⟨h1, _⟩)
      · exact absurd (h.trans hy) hx
      · exact h1
      · exact absurd h1 hx
  · rw [if_neg hx, if_neg hy]
    constructor
    · exact Or.inl
    · rintro (h | ⟨_, h2⟩ | ⟨h1, _⟩)
      · exact h
      · exact absurd h2 hy
      · exact absurd h1 hx

private lemma Comp8.union_rtg {c : Comp8} {R : Fin 8 → Fin 8 → Prop}
    (hR : Equivalence R) (hc : ∀ x y, c.get x = c.get y ↔ R x y) (a b : Fin 8) :
    ∀ x y, (c.union (c.get a) (c.get b)).get x = (c.union (c.get a) (c.get b)).get y ↔
      Relation.ReflTransGen (fun u v => R u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a)) x y := by
  intro x y
  let E : Fin 8 → Fin 8 → Prop := fun u v => R u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a)
  change _ ↔ Relation.ReflTransGen E x y
  rw [Comp8.union_eq_iff]
  constructor
  · intro h
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Relation.ReflTransGen.single (Or.inl ((hc x y).1 h))
    · have s1 : Relation.ReflTransGen E x a := .single (Or.inl ((hc x a).1 h1))
      have s2 : Relation.ReflTransGen E a b := .single (Or.inr (Or.inl ⟨rfl, rfl⟩))
      have s3 : Relation.ReflTransGen E b y := .single (Or.inl (hR.symm ((hc y b).1 h2)))
      exact (s1.trans s2).trans s3
    · have s1 : Relation.ReflTransGen E x b := .single (Or.inl ((hc x b).1 h1))
      have s2 : Relation.ReflTransGen E b a := .single (Or.inr (Or.inr ⟨rfl, rfl⟩))
      have s3 : Relation.ReflTransGen E a y := .single (Or.inl (hR.symm ((hc y a).1 h2)))
      exact (s1.trans s2).trans s3
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @tail u v _ huv ih =>
      rcases huv with hRuv | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hceq : c.get u = c.get v := (hc u v).2 hRuv
        rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (h1.trans hceq)
        · exact Or.inr (Or.inl ⟨h1, hceq.symm.trans h2⟩)
        · exact Or.inr (Or.inr ⟨h1, hceq.symm.trans h2⟩)
      · rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨h1, rfl⟩)
        · exact Or.inr (Or.inl ⟨h1, rfl⟩)
        · exact Or.inl h1
      · rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inr ⟨h1, rfl⟩)
        · exact Or.inl h1
        · exact Or.inr (Or.inr ⟨h1, rfl⟩)

private def deg2 (a b : Bool) : D3 :=
  match a, b with
  | false, false => .d0
  | true, false | false, true => .d1
  | true, true => .d2

private def deg3 (a b c : Bool) : Option D3 :=
  match a, b, c with
  | false, false, false => some .d0
  | true, false, false | false, true, false | false, false, true => some .d1
  | true, true, false | true, false, true | false, true, true => some .d2
  | true, true, true => none

private def okAdd (d : D3) (v : Bool) : Bool :=
  match d, v with
  | .d2, true => false
  | _, _ => true

private lemma okAdd_iff (d : D3) (v : Bool) :
    okAdd d v = true ↔ d.toNat + (if v then 1 else 0) ≤ 2 := by
  cases d <;> cases v <;> decide

private lemma deg3_iff (a b c : Bool) (d : D3) :
    deg3 a b c = some d ↔ d.toNat = (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private lemma deg3_none_iff (a b c : Bool) :
    deg3 a b c = none ↔ (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) > 2 := by
  cases a <;> cases b <;> cases c <;> decide

private lemma deg2_toNat (a b : Bool) :
    (deg2 a b).toNat = (if a then 1 else 0) + (if b then 1 else 0) := by
  cases a <;> cases b <;> decide

private def inRow (r0 r1 r2 r3 col : C4) : Bool :=
  r0.eqb col || r1.eqb col || r2.eqb col || r3.eqb col

private lemma inRow_iff (r : Row) (col : C4) :
    inRow r.c0 r.c1 r.c2 r.c3 col = true ↔ ∃ j : Fin 4, r.get j = col := by
  simp only [inRow, Bool.or_eq_true, C4.eqb_iff]
  constructor
  · rintro (((h | h) | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  · rintro ⟨j, hj⟩
    fin_cases j <;> simp_all [Row.get]

private lemma inRow_state_iff (s : State) (col : C4) :
    inRow s.r0 s.r1 s.r2 s.r3 col = true ↔ ∃ j : Fin 4, s.row j = col := by
  simp only [inRow, Bool.or_eq_true, C4.eqb_iff]
  constructor
  · rintro (((h | h) | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  · rintro ⟨j, hj⟩
    fin_cases j <;> simp_all [State.row]

private def sameComp (s : State) (col : C4) : Bool :=
  let ok (x y px py : C4) := !(x.eqb col && y.eqb col) || px.eqb py
  ok s.r0 s.r1 s.p0 s.p1 && ok s.r0 s.r2 s.p0 s.p2 && ok s.r0 s.r3 s.p0 s.p3 &&
  ok s.r1 s.r2 s.p1 s.p2 && ok s.r1 s.r3 s.p1 s.p3 && ok s.r2 s.r3 s.p2 s.p3

private lemma sameComp_iff (s : State) (col : C4) :
    sameComp s col = true ↔ ∀ i j : Fin 4, s.row i = col → s.row j = col → s.comp i = s.comp j := by
  simp only [sameComp, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, C4.eqb_iff, ne_eq]
  constructor
  · intro h i j hi hj
    fin_cases i <;> fin_cases j <;> simp_all [State.row, State.comp]
  · intro h
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · by_cases h0 : s.r0 = col ∧ s.r1 = col
      · exact Or.inr (h 0 1 h0.1 h0.2)
      · exact Or.inl h0
    · by_cases h0 : s.r0 = col ∧ s.r2 = col
      · exact Or.inr (h 0 2 h0.1 h0.2)
      · exact Or.inl h0
    · by_cases h0 : s.r0 = col ∧ s.r3 = col
      · exact Or.inr (h 0 3 h0.1 h0.2)
      · exact Or.inl h0
    · by_cases h0 : s.r1 = col ∧ s.r2 = col
      · exact Or.inr (h 1 2 h0.1 h0.2)
      · exact Or.inl h0
    · by_cases h0 : s.r1 = col ∧ s.r3 = col
      · exact Or.inr (h 1 3 h0.1 h0.2)
      · exact Or.inl h0
    · by_cases h0 : s.r2 = col ∧ s.r3 = col
      · exact Or.inr (h 2 3 h0.1 h0.2)
      · exact Or.inl h0

private def initState (r : Row) : Option State :=
  if r.c0.eqb .a0 && r.c3.eqb .a1 then
    let h0 := r.c0.eqb r.c1
    let h1 := r.c1.eqb r.c2
    let h2 := r.c2.eqb r.c3
    let id1 := deg2 h0 h1
    let id2 := deg2 h1 h2
    let id3 := if h2 then D3.d1 else D3.d0
    let p1 : C4 := if h0 then .a0 else .a1
    let p2 : C4 := if h1 then p1 else if h0 then .a1 else .a2
    let p3 : C4 := if h2 then p2 else if h0 then (if h1 then .a1 else .a2) else if h1 then .a2 else .a3
    some ⟨r.c0, r.c1, r.c2, r.c3, id1, id2, id3, .a0, p1, p2, p3, false, false⟩
  else none

private def stepComp (s : State) (nr : Row) : Comp8 :=
  let v0 := s.r1.eqb nr.c0
  let v1 := s.r2.eqb nr.c1
  let v2 := s.r3.eqb nr.c2
  let h0 := nr.c0.eqb nr.c1
  let h1 := nr.c1.eqb nr.c2
  let h2 := nr.c2.eqb nr.c3
  let c : Comp8 := ⟨s.p0.toC8, s.p1.toC8, s.p2.toC8, s.p3.toC8, .x4, .x5, .x6, .x7⟩
  let c := if v0 then c.union c.c1 c.c4 else c
  let c := if v1 then c.union c.c2 c.c5 else c
  let c := if v2 then c.union c.c3 c.c6 else c
  let c := if h0 then c.union c.c4 c.c5 else c
  let c := if h1 then c.union c.c5 c.c6 else c
  let c := if h2 then c.union c.c6 c.c7 else c
  c

private def canon4 (a b c d : C8) : C4 × C4 × C4 × C4 :=
  let np1 : C4 := if b.eqb a then .a0 else .a1
  let np2 : C4 := if c.eqb a then .a0 else if c.eqb b then np1 else if b.eqb a then .a1 else .a2
  let np3 : C4 := if d.eqb a then .a0 else if d.eqb b then np1 else if d.eqb c then np2
    else if b.eqb a then (if c.eqb a then .a1 else .a2)
    else if c.eqb a || c.eqb b then .a2 else .a3
  (.a0, np1, np2, np3)

private lemma canon4_iff (a b c d : C8) :
    let (p0, p1, p2, p3) := canon4 a b c d
    let pf : Fin 4 → C4 := fun j => match j with | ⟨0,_⟩ => p0 | ⟨1,_⟩ => p1 | ⟨2,_⟩ => p2 | ⟨3,_⟩ => p3
    let cf : Fin 4 → C8 := fun j => match j with | ⟨0,_⟩ => a | ⟨1,_⟩ => b | ⟨2,_⟩ => c | ⟨3,_⟩ => d
    ∀ i j : Fin 4, pf i = pf j ↔ cf i = cf j := by
  intro i j
  dsimp only [canon4]
  fin_cases i <;> fin_cases j <;> dsimp only <;> simp only [Bool.or_eq_true, C8.eqb_iff]
  all_goals
    by_cases hba : b = a <;> by_cases hca : c = a <;> by_cases hcb : c = b <;>
    by_cases hda : d = a <;> by_cases hdb : d = b <;> by_cases hdc : d = c <;>
    simp_all <;>
    first
    | rfl
    | (intro h; exact absurd h.symm (by assumption))

private def step (s : State) (nr : Row) : Option State :=
  if s.closed nr.c0 || !okAdd s.d1 (s.r1.eqb nr.c0) then none else
  if s.closed nr.c1 || !okAdd s.d2 (s.r2.eqb nr.c1) then none else
  let v1 := s.r2.eqb nr.c1
  let h0 := nr.c0.eqb nr.c1
  if s.closed nr.c2 || !okAdd s.d3 (s.r3.eqb nr.c2) then none else
  let v2 := s.r3.eqb nr.c2
  let h1 := nr.c1.eqb nr.c2
  match deg3 v1 h0 h1 with
  | none => none
  | some nd1 =>
    if s.closed nr.c3 then none else
    let h2 := nr.c2.eqb nr.c3
    match deg3 v2 h1 h2 with
    | none => none
    | some nd2 =>
      let d0 := inRow s.r0 s.r1 s.r2 s.r3 .a0 && !inRow nr.c0 nr.c1 nr.c2 nr.c3 .a0
      let d1 := inRow s.r0 s.r1 s.r2 s.r3 .a1 && !inRow nr.c0 nr.c1 nr.c2 nr.c3 .a1
      let d2 := inRow s.r0 s.r1 s.r2 s.r3 .a2 && !inRow nr.c0 nr.c1 nr.c2 nr.c3 .a2
      let d3 := inRow s.r0 s.r1 s.r2 s.r3 .a3 && !inRow nr.c0 nr.c1 nr.c2 nr.c3 .a3
      if d2 || d3 then none
      else if (d0 && !sameComp s .a0) || (d1 && !sameComp s .a1) then none
      else
      let c := stepComp s nr
      let surv (col : C4) (cx : C8) : Bool :=
        !inRow nr.c0 nr.c1 nr.c2 nr.c3 col || cx.eqb c.c4 || cx.eqb c.c5 || cx.eqb c.c6 || cx.eqb c.c7
      if !(surv s.r0 c.c0 && surv s.r1 c.c1 && surv s.r2 c.c2 && surv s.r3 c.c3) then none
      else
      let (np0, np1, np2, np3) := canon4 c.c4 c.c5 c.c6 c.c7
      some ⟨nr.c0, nr.c1, nr.c2, nr.c3, nd1, nd2, if h2 then .d1 else .d0, np0, np1, np2, np3, s.cl0 || d0, s.cl1 || d1⟩

private def isFinal (s : State) : Bool :=
  s.r0.eqb .a2 && s.r3.eqb .a3 &&
  sameComp s .a0 && sameComp s .a1 && sameComp s .a2 && sameComp s .a3

private lemma isFinal_iff (s : State) :
    isFinal s = true ↔ s.r0 = .a2 ∧ s.r3 = .a3 ∧
      ∀ i j : Fin 4, s.row i = s.row j → s.comp i = s.comp j := by
  simp only [isFinal, Bool.and_eq_true, C4.eqb_iff, sameComp_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨h0, h3⟩, c0⟩, c1⟩, c2⟩, c3⟩
    refine ⟨h0, h3, fun i j hij => ?_⟩
    cases hr : s.row i
    · exact c0 i j hr (hij.symm.trans hr)
    · exact c1 i j hr (hij.symm.trans hr)
    · exact c2 i j hr (hij.symm.trans hr)
    · exact c3 i j hr (hij.symm.trans hr)
  · rintro ⟨h0, h3, hc⟩
    exact ⟨⟨⟨⟨⟨h0, h3⟩,
      fun i j hi hj => hc i j (hi.trans hj.symm)⟩,
      fun i j hi hj => hc i j (hi.trans hj.symm)⟩,
      fun i j hi hj => hc i j (hi.trans hj.symm)⟩,
      fun i j hi hj => hc i j (hi.trans hj.symm)⟩

private def runFrom : (k : ℕ) → State → (Fin k → Row) → Option State
  | 0, s, _ => some s
  | k + 1, s, w =>
    match step s (w 0) with
    | none => none
    | some t => runFrom k t (fun i => w i.succ)

private def runBoard (k : ℕ) (w : Fin (k + 1) → Row) : Option State :=
  match initState (w 0) with
  | none => none
  | some s => runFrom k s (fun i => w i.succ)

private def ways : ℕ → State → ℕ
  | 0, s => if isFinal s then 1 else 0
  | k + 1, s => ∑ r : Row, match step s r with | none => 0 | some t => ways k t

/-! ### Part 2: Board graph properties, prefix degrees, and Cut-Row Lemma -/

private def rowOf {n : ℕ} (f : Cell n → Fin 4) (i : Fin n) : Row :=
  ⟨C4.ofFin (f (i, 0)), C4.ofFin (f (i, 1)), C4.ofFin (f (i, 2)), C4.ofFin (f (i, 3))⟩

private lemma rowOf_get {n : ℕ} (f : Cell n → Fin 4) (i : Fin n) (j : Fin 4) :
    (rowOf f i).get j = C4.ofFin (f (i, j)) := by
  fin_cases j <;> rfl

private lemma rowOf_get_toFin {n : ℕ} (f : Cell n → Fin 4) (i : Fin n) (j : Fin 4) :
    ((rowOf f i).get j).toFin = f (i, j) := by
  rw [rowOf_get, C4.toFin_ofFin]

private def boardEquiv (n : ℕ) : (Cell n → Fin 4) ≃ (Fin n → Row) where
  toFun f i := rowOf f i
  invFun w c := ((w c.1).get c.2).toFin
  left_inv f := by
    funext ⟨i, j⟩
    exact rowOf_get_toFin f i j
  right_inv w := by
    funext i
    apply rowEquiv.injective
    funext j
    change (rowOf (fun c => ((w c.1).get c.2).toFin) i).get j = (w i).get j
    rw [rowOf_get, C4.ofFin_toFin]

private lemma neighbors_symm {n : ℕ} {c d : Cell n} (h : neighbors c d) : neighbors d c := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, Or.inr h2⟩
  · exact Or.inl ⟨h1.symm, Or.inl h2⟩
  · exact Or.inr (Or.inr ⟨h1, h2.symm⟩)
  · exact Or.inr (Or.inl ⟨h1, h2.symm⟩)

private lemma sameAdj_symm {n : ℕ} {f : Cell n → Fin 4} {c d : Cell n} (h : sameAdj f c d) :
    sameAdj f d c :=
  ⟨neighbors_symm h.1, h.2.symm⟩

private lemma neighbors_row_step {n : ℕ} {c d : Cell n} (h : neighbors c d) :
    c.1.val = d.1.val ∨ c.1.val + 1 = d.1.val ∨ d.1.val + 1 = c.1.val := by
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
  · exact Or.inl (congrArg Fin.val h1)
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

private def bnat (P : Prop) [Decidable P] : ℕ := if P then 1 else 0

private def hLeft {n : ℕ} (f : Cell n → Fin 4) (i : Fin n) (j : Fin 4) : ℕ :=
  if hj : 0 < j.val then bnat (f (i, ⟨j.val - 1, by omega⟩) = f (i, j)) else 0

private def hRight {n : ℕ} (f : Cell n → Fin 4) (i : Fin n) (j : Fin 4) : ℕ :=
  if hj : j.val + 1 < 4 then bnat (f (i, ⟨j.val + 1, hj⟩) = f (i, j)) else 0

private def vUp {n : ℕ} (f : Cell n → Fin 4) (i : Fin n) (j : Fin 4) : ℕ :=
  if h : 0 < i.val ∧ j.val + 1 < 4 then
    bnat (f (⟨i.val - 1, by omega⟩, ⟨j.val + 1, h.2⟩) = f (i, j))
  else 0

private def vDown {n : ℕ} (f : Cell n → Fin 4) (i : Fin n) (j : Fin 4) : ℕ :=
  if h : i.val + 1 < n ∧ 0 < j.val then
    bnat (f (⟨i.val + 1, h.1⟩, ⟨j.val - 1, by omega⟩) = f (i, j))
  else 0

private def prefixDeg {n : ℕ} (f : Cell n → Fin 4) (i : Fin n) (j : Fin 4) : ℕ :=
  hLeft f i j + hRight f i j + vUp f i j

private lemma card_filter_eq_bnat {α : Type*} [Fintype α] [DecidableEq α]
    (P : α → Prop) [DecidablePred P] (a : α) (honly : ∀ x, P x → x = a) :
    (Finset.univ.filter P).card = bnat (P a) := by
  by_cases ha : P a
  · have hset : Finset.univ.filter P = {a} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨honly x, fun hx => hx ▸ ha⟩
    simp [hset, bnat, ha]
  · have hset : Finset.univ.filter P = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hx
      exact ha (honly x hx ▸ hx)
    simp [hset, bnat, ha]

private lemma bnat_eq_ite {P : Prop} [Decidable P] {b : Bool} (h : b = true ↔ P) :
    bnat P = if b then 1 else 0 := by
  cases b
  · have hnp : ¬ P := fun hp => by have := h.2 hp; cases this
    simp [bnat, hnp]
  · simp [bnat, h.1 rfl]

private lemma neighborSame_eq {n : ℕ} (f : Cell n → Fin 4) (i : Fin n) (j : Fin 4) :
    neighborSame f (i, j) = prefixDeg f i j + vDown f i j := by
  classical
  unfold neighborSame prefixDeg
  let P1 : Cell n → Prop := fun d => d.1 = i ∧ d.2.val + 1 = j.val ∧ f d = f (i, j)
  let P2 : Cell n → Prop := fun d => d.1 = i ∧ j.val + 1 = d.2.val ∧ f d = f (i, j)
  let P3 : Cell n → Prop := fun d => d.1.val + 1 = i.val ∧ absCol (i, j) = absCol d ∧ f d = f (i, j)
  let P4 : Cell n → Prop := fun d => i.val + 1 = d.1.val ∧ absCol (i, j) = absCol d ∧ f d = f (i, j)
  let S1 := Finset.univ.filter P1
  let S2 := Finset.univ.filter P2
  let S3 := Finset.univ.filter P3
  let S4 := Finset.univ.filter P4
  have hunion :
      (Finset.univ.filter fun d => neighbors (i, j) d ∧ f d = f (i, j)) =
        S1 ∪ S2 ∪ S3 ∪ S4 := by
    apply Finset.ext
    intro d
    dsimp only [S1, S2, S3, S4]
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_union, Finset.mem_union,
      Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, P1, P2, P3, P4, neighbors]
    constructor
    · rintro ⟨⟨h1, h2 | h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩, hf⟩
      · exact Or.inl (Or.inl (Or.inr ⟨h1.symm, h2, hf⟩))
      · exact Or.inl (Or.inl (Or.inl ⟨h1.symm, h2, hf⟩))
      · exact Or.inr ⟨h1, h2, hf⟩
      · exact Or.inl (Or.inr ⟨h1, h2, hf⟩)
    · rintro (((⟨h1, h2, hf⟩ | ⟨h1, h2, hf⟩) | ⟨h1, h2, hf⟩) | ⟨h1, h2, hf⟩)
      · exact ⟨Or.inl ⟨h1.symm, Or.inr h2⟩, hf⟩
      · exact ⟨Or.inl ⟨h1.symm, Or.inl h2⟩, hf⟩
      · exact ⟨Or.inr (Or.inr ⟨h1, h2⟩), hf⟩
      · exact ⟨Or.inr (Or.inl ⟨h1, h2⟩), hf⟩
  have hd12 : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]; intro d h1 h2
    dsimp only [S1, S2] at h1 h2
    simp only [Finset.mem_filter, P1, P2] at h1 h2; omega
  have hd12_3 : Disjoint (S1 ∪ S2) S3 := by
    rw [Finset.disjoint_left]; intro d h1 h2
    dsimp only [S1, S2, S3] at h1 h2
    simp only [Finset.mem_union, Finset.mem_filter, P1, P2, P3] at h1 h2
    rcases h1 with ⟨_, h1, _⟩ | ⟨_, h1, _⟩ <;> omega
  have hd123_4 : Disjoint (S1 ∪ S2 ∪ S3) S4 := by
    rw [Finset.disjoint_left]; intro d h1 h2
    dsimp only [S1, S2, S3, S4] at h1 h2
    simp only [Finset.mem_union, Finset.mem_filter, P1, P2, P3, P4] at h1 h2
    rcases h1 with (⟨_, h1, _⟩ | ⟨_, h1, _⟩) | ⟨_, h1, _⟩ <;> omega
  rw [hunion, Finset.card_union_of_disjoint hd123_4, Finset.card_union_of_disjoint hd12_3,
    Finset.card_union_of_disjoint hd12]
  have hc1 : S1.card = hLeft f i j := by
    unfold hLeft
    split_ifs with hj
    · let a : Cell n := (i, ⟨j.val - 1, by omega⟩)
      have hcard := card_filter_eq_bnat P1 a (fun d hd => by
        rcases d with ⟨di, dj⟩; rcases hd with ⟨h1, h2, _⟩
        dsimp only at h1 h2
        exact Prod.ext h1 (Fin.ext (by dsimp [a]; omega)))
      convert hcard using 1
      simp only [bnat, P1, a]
      have : j.val - 1 + 1 = j.val := by omega
      simp [this]
    · have h0 : S1 = ∅ := by
        apply Finset.ext; intro d; dsimp only [S1]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, P1]; intro h; omega
      simp [h0]
  have hc2 : S2.card = hRight f i j := by
    unfold hRight
    split_ifs with hj
    · let a : Cell n := (i, ⟨j.val + 1, hj⟩)
      have hcard := card_filter_eq_bnat P2 a (fun d hd => by
        rcases d with ⟨di, dj⟩; rcases hd with ⟨h1, h2, _⟩
        dsimp only at h1 h2
        exact Prod.ext h1 (Fin.ext (by dsimp [a]; omega)))
      convert hcard using 1
      simp [bnat, P2, a]
    · have h0 : S2 = ∅ := by
        apply Finset.ext; intro d; dsimp only [S2]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, P2]; intro h; have := d.2.isLt; omega
      simp [h0]
  have hc3 : S3.card = vUp f i j := by
    unfold vUp
    split_ifs with h
    · let a : Cell n := (⟨i.val - 1, by omega⟩, ⟨j.val + 1, h.2⟩)
      have hcard := card_filter_eq_bnat P3 a (fun d hd => by
        rcases d with ⟨di, dj⟩; rcases hd with ⟨h1, h2, _⟩
        dsimp only [absCol] at h1 h2
        exact Prod.ext (Fin.ext (by dsimp [a]; omega)) (Fin.ext (by dsimp [a]; omega)))
      convert hcard using 1
      simp only [bnat, P3, absCol, a]
      have h1 : i.val - 1 + 1 = i.val := by omega
      have h2 : i.val + j.val = i.val - 1 + (j.val + 1) := by omega
      simp [h1, h2]
    · have h0 : S3 = ∅ := by
        apply Finset.ext; intro d; dsimp only [S3]
        rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, P3, absCol]
        rintro ⟨h1, h2, _⟩; have := d.2.isLt; omega
      simp [h0]
  have hc4 : S4.card = vDown f i j := by
    unfold vDown
    split_ifs with h
    · let a : Cell n := (⟨i.val + 1, h.1⟩, ⟨j.val - 1, by omega⟩)
      have hcard := card_filter_eq_bnat P4 a (fun d hd => by
        rcases d with ⟨di, dj⟩; rcases hd with ⟨h1, h2, _⟩
        dsimp only [absCol] at h1 h2
        exact Prod.ext (Fin.ext (by dsimp [a]; omega)) (Fin.ext (by dsimp [a]; omega)))
      convert hcard using 1
      simp only [bnat, P4, absCol, a]
      have h2 : i.val + j.val = i.val + 1 + (j.val - 1) := by omega
      simp [h2]
    · have h0 : S4 = ∅ := by
        apply Finset.ext; intro d; dsimp only [S4]
        rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, P4, absCol]
        rintro ⟨h1, h2, _⟩; have := d.1.isLt; omega
      simp [h0]
  rw [hc1, hc2, hc3, hc4]

private lemma prefixDeg_zero_eval {n : ℕ} (f : Cell n → Fin 4) (hn : 0 < n) :
    let r := rowOf f ⟨0, hn⟩
    let h0 := r.c0.eqb r.c1
    let h1 := r.c1.eqb r.c2
    let h2 := r.c2.eqb r.c3
    prefixDeg f ⟨0, hn⟩ 0 = (if h0 then 1 else 0) ∧
    prefixDeg f ⟨0, hn⟩ 1 = (if h0 then 1 else 0) + (if h1 then 1 else 0) ∧
    prefixDeg f ⟨0, hn⟩ 2 = (if h1 then 1 else 0) + (if h2 then 1 else 0) ∧
    prefixDeg f ⟨0, hn⟩ 3 = (if h2 then 1 else 0) := by
  have heq : ∀ j1 j2 : Fin 4,
      ((rowOf f ⟨0, hn⟩).get j1).eqb ((rowOf f ⟨0, hn⟩).get j2) = true ↔
        f (⟨0, hn⟩, j1) = f (⟨0, hn⟩, j2) := fun j1 j2 => by
    rw [C4.eqb_iff, rowOf_get, rowOf_get]
    exact C4.ofFin_injective.eq_iff
  have h01 : ((rowOf f ⟨0, hn⟩).c0.eqb (rowOf f ⟨0, hn⟩).c1 = true) ↔
      f (⟨0, hn⟩, 0) = f (⟨0, hn⟩, 1) := by simpa [Row.get] using heq 0 1
  have h12 : ((rowOf f ⟨0, hn⟩).c1.eqb (rowOf f ⟨0, hn⟩).c2 = true) ↔
      f (⟨0, hn⟩, 1) = f (⟨0, hn⟩, 2) := by simpa [Row.get] using heq 1 2
  have h23 : ((rowOf f ⟨0, hn⟩).c2.eqb (rowOf f ⟨0, hn⟩).c3 = true) ↔
      f (⟨0, hn⟩, 2) = f (⟨0, hn⟩, 3) := by simpa [Row.get] using heq 2 3
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold prefixDeg hLeft hRight vUp
    simp only [Fin.val_zero, lt_self_iff_false, dite_false, zero_add, add_zero,
      show (0 + 1 < 4) by decide, dite_true, false_and]
    change bnat (f (⟨0, hn⟩, 1) = f (⟨0, hn⟩, 0)) = _
    exact bnat_eq_ite (h01.trans eq_comm)
  · unfold prefixDeg hLeft hRight vUp
    simp only [Fin.val_one, Nat.zero_lt_one, dite_true, show (1 + 1 < 4) by decide,
      lt_self_iff_false, false_and, dite_false, add_zero]
    change bnat (f (⟨0, hn⟩, 0) = f (⟨0, hn⟩, 1)) + bnat (f (⟨0, hn⟩, 2) = f (⟨0, hn⟩, 1)) = _
    rw [bnat_eq_ite h01, bnat_eq_ite (h12.trans eq_comm)]
  · unfold prefixDeg hLeft hRight vUp
    simp only [Fin.val_two, Nat.zero_lt_two, dite_true, show (2 + 1 < 4) by decide,
      lt_self_iff_false, false_and, dite_false, add_zero]
    change bnat (f (⟨0, hn⟩, 1) = f (⟨0, hn⟩, 2)) + bnat (f (⟨0, hn⟩, 3) = f (⟨0, hn⟩, 2)) = _
    rw [bnat_eq_ite h12, bnat_eq_ite (h23.trans eq_comm)]
  · unfold prefixDeg hLeft hRight vUp
    have h3 : (3 : Fin 4).val = 3 := rfl
    simp only [h3, Nat.zero_lt_succ, dite_true, show ¬(3 + 1 < 4) by decide, dite_false,
      and_false, add_zero]
    change bnat (f (⟨0, hn⟩, 2) = f (⟨0, hn⟩, 3)) = _
    exact bnat_eq_ite h23

private lemma prefixDeg_succ_eval {n : ℕ} (f : Cell n → Fin 4) {k : ℕ} (hk1 : k + 1 < n) :
    let hk : k < n := by omega
    let r := rowOf f ⟨k, hk⟩
    let nr := rowOf f ⟨k + 1, hk1⟩
    let v0 := r.c1.eqb nr.c0
    let v1 := r.c2.eqb nr.c1
    let v2 := r.c3.eqb nr.c2
    let h0 := nr.c0.eqb nr.c1
    let h1 := nr.c1.eqb nr.c2
    let h2 := nr.c2.eqb nr.c3
    prefixDeg f ⟨k + 1, hk1⟩ 0 = (if v0 then 1 else 0) + (if h0 then 1 else 0) ∧
    prefixDeg f ⟨k + 1, hk1⟩ 1 = (if v1 then 1 else 0) + (if h0 then 1 else 0) + (if h1 then 1 else 0) ∧
    prefixDeg f ⟨k + 1, hk1⟩ 2 = (if v2 then 1 else 0) + (if h1 then 1 else 0) + (if h2 then 1 else 0) ∧
    prefixDeg f ⟨k + 1, hk1⟩ 3 = (if h2 then 1 else 0) := by
  have hk : k < n := by omega
  have heqV : ∀ j1 j2 : Fin 4,
      ((rowOf f ⟨k, hk⟩).get j1).eqb ((rowOf f ⟨k + 1, hk1⟩).get j2) = true ↔
        f (⟨k, hk⟩, j1) = f (⟨k + 1, hk1⟩, j2) := fun j1 j2 => by
    rw [C4.eqb_iff, rowOf_get, rowOf_get]; exact C4.ofFin_injective.eq_iff
  have heqH : ∀ j1 j2 : Fin 4,
      ((rowOf f ⟨k + 1, hk1⟩).get j1).eqb ((rowOf f ⟨k + 1, hk1⟩).get j2) = true ↔
        f (⟨k + 1, hk1⟩, j1) = f (⟨k + 1, hk1⟩, j2) := fun j1 j2 => by
    rw [C4.eqb_iff, rowOf_get, rowOf_get]; exact C4.ofFin_injective.eq_iff
  have hv0 : ((rowOf f ⟨k, hk⟩).c1.eqb (rowOf f ⟨k + 1, hk1⟩).c0 = true) ↔
      f (⟨k, hk⟩, 1) = f (⟨k + 1, hk1⟩, 0) := by simpa [Row.get] using heqV 1 0
  have hv1 : ((rowOf f ⟨k, hk⟩).c2.eqb (rowOf f ⟨k + 1, hk1⟩).c1 = true) ↔
      f (⟨k, hk⟩, 2) = f (⟨k + 1, hk1⟩, 1) := by simpa [Row.get] using heqV 2 1
  have hv2 : ((rowOf f ⟨k, hk⟩).c3.eqb (rowOf f ⟨k + 1, hk1⟩).c2 = true) ↔
      f (⟨k, hk⟩, 3) = f (⟨k + 1, hk1⟩, 2) := by simpa [Row.get] using heqV 3 2
  have hh0 : ((rowOf f ⟨k + 1, hk1⟩).c0.eqb (rowOf f ⟨k + 1, hk1⟩).c1 = true) ↔
      f (⟨k + 1, hk1⟩, 0) = f (⟨k + 1, hk1⟩, 1) := by simpa [Row.get] using heqH 0 1
  have hh1 : ((rowOf f ⟨k + 1, hk1⟩).c1.eqb (rowOf f ⟨k + 1, hk1⟩).c2 = true) ↔
      f (⟨k + 1, hk1⟩, 1) = f (⟨k + 1, hk1⟩, 2) := by simpa [Row.get] using heqH 1 2
  have hh2 : ((rowOf f ⟨k + 1, hk1⟩).c2.eqb (rowOf f ⟨k + 1, hk1⟩).c3 = true) ↔
      f (⟨k + 1, hk1⟩, 2) = f (⟨k + 1, hk1⟩, 3) := by simpa [Row.get] using heqH 2 3
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold prefixDeg hLeft hRight vUp
    simp only [Fin.val_zero, lt_self_iff_false, dite_false, zero_add, Nat.zero_lt_succ,
      show (0 + 1 < 4) by decide, and_self, dite_true, Nat.add_sub_cancel]
    change bnat (f (⟨k + 1, hk1⟩, 1) = f (⟨k + 1, hk1⟩, 0)) +
        bnat (f (⟨k, hk⟩, 1) = f (⟨k + 1, hk1⟩, 0)) = _
    rw [bnat_eq_ite (hh0.trans eq_comm), bnat_eq_ite hv0, add_comm]
  · unfold prefixDeg hLeft hRight vUp
    simp only [Fin.val_one, show (1 + 1 < 4) by decide, Nat.zero_lt_succ,
      and_self, dite_true, Nat.add_sub_cancel]
    change bnat (f (⟨k + 1, hk1⟩, 0) = f (⟨k + 1, hk1⟩, 1)) +
        bnat (f (⟨k + 1, hk1⟩, 2) = f (⟨k + 1, hk1⟩, 1)) +
        bnat (f (⟨k, hk⟩, 2) = f (⟨k + 1, hk1⟩, 1)) = _
    rw [bnat_eq_ite hh0, bnat_eq_ite (hh1.trans eq_comm), bnat_eq_ite hv1]; omega
  · unfold prefixDeg hLeft hRight vUp
    simp only [Fin.val_two, show (2 + 1 < 4) by decide, Nat.zero_lt_succ,
      and_self, dite_true, Nat.add_sub_cancel]
    change bnat (f (⟨k + 1, hk1⟩, 1) = f (⟨k + 1, hk1⟩, 2)) +
        bnat (f (⟨k + 1, hk1⟩, 3) = f (⟨k + 1, hk1⟩, 2)) +
        bnat (f (⟨k, hk⟩, 3) = f (⟨k + 1, hk1⟩, 2)) = _
    rw [bnat_eq_ite hh1, bnat_eq_ite (hh2.trans eq_comm), bnat_eq_ite hv2]; omega
  · unfold prefixDeg hLeft hRight vUp
    have h3 : (3 : Fin 4).val = 3 := rfl
    simp only [h3, Nat.zero_lt_succ, dite_true, show ¬(3 + 1 < 4) by decide, dite_false,
      and_false, add_zero]
    change bnat (f (⟨k + 1, hk1⟩, 2) = f (⟨k + 1, hk1⟩, 3)) = _
    exact bnat_eq_ite hh2

private lemma vDown_eval {n : ℕ} (f : Cell n → Fin 4) {k : ℕ} (hk1 : k + 1 < n) :
    let hk : k < n := by omega
    let r := rowOf f ⟨k, hk⟩
    let nr := rowOf f ⟨k + 1, hk1⟩
    vDown f ⟨k, hk⟩ 0 = 0 ∧
    vDown f ⟨k, hk⟩ 1 = (if r.c1.eqb nr.c0 then 1 else 0) ∧
    vDown f ⟨k, hk⟩ 2 = (if r.c2.eqb nr.c1 then 1 else 0) ∧
    vDown f ⟨k, hk⟩ 3 = (if r.c3.eqb nr.c2 then 1 else 0) := by
  have hk : k < n := by omega
  have heqV : ∀ j1 j2 : Fin 4,
      ((rowOf f ⟨k, hk⟩).get j1).eqb ((rowOf f ⟨k + 1, hk1⟩).get j2) = true ↔
        f (⟨k + 1, hk1⟩, j2) = f (⟨k, hk⟩, j1) := fun j1 j2 => by
    rw [C4.eqb_iff, rowOf_get, rowOf_get, eq_comm]; exact C4.ofFin_injective.eq_iff
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold vDown; simp
  · unfold vDown
    simp only [Fin.val_one, Nat.zero_lt_one, hk1, and_self, dite_true]
    exact bnat_eq_ite (by simpa [Row.get] using heqV 1 0)
  · unfold vDown
    simp only [Fin.val_two, Nat.zero_lt_two, hk1, and_self, dite_true]
    exact bnat_eq_ite (by simpa [Row.get] using heqV 2 1)
  · unfold vDown
    have h3 : (3 : Fin 4).val = 3 := rfl
    simp only [h3, Nat.zero_lt_succ, hk1, and_self, dite_true]
    exact bnat_eq_ite (by simpa [Row.get] using heqV 3 2)

/-! ### Prefix reachability, Border-Crossing, and Cut-Row Lemma -/

private def prefixAdj {n : ℕ} (f : Cell n → Fin 4) (k : ℕ) (c d : Cell n) : Prop :=
  c.1.val ≤ k ∧ d.1.val ≤ k ∧ sameAdj f c d

private def Reach {n : ℕ} (f : Cell n → Fin 4) (k : ℕ) (c d : Cell n) : Prop :=
  Relation.ReflTransGen (prefixAdj f k) c d

private lemma prefixAdj_symm {n : ℕ} {f : Cell n → Fin 4} {k : ℕ} {c d : Cell n}
    (h : prefixAdj f k c d) : prefixAdj f k d c :=
  ⟨h.2.1, h.1, sameAdj_symm h.2.2⟩

private lemma Reach_symm {n : ℕ} {f : Cell n → Fin 4} {k : ℕ} {c d : Cell n}
    (h : Reach f k c d) : Reach f k d c := by
  induction h with
  | refl => exact .refl
  | tail _ huv ih => exact .trans (.single (prefixAdj_symm huv)) ih

private lemma Reach_trans {n : ℕ} {f : Cell n → Fin 4} {k : ℕ} {a b c : Cell n}
    (h1 : Reach f k a b) (h2 : Reach f k b c) : Reach f k a c :=
  Relation.ReflTransGen.trans h1 h2

private lemma Reach_color {n : ℕ} {f : Cell n → Fin 4} {k : ℕ} {c d : Cell n}
    (h : Reach f k c d) : f c = f d := by
  induction h with
  | refl => rfl
  | tail _ huv ih => exact ih.trans huv.2.2.2

private lemma Reach_mono {n : ℕ} {f : Cell n → Fin 4} {k m : ℕ} (hkm : k ≤ m)
    {c d : Cell n} (h : Reach f k c d) : Reach f m c d :=
  Relation.ReflTransGen.mono (fun _ _ h => ⟨le_trans h.1 hkm, le_trans h.2.1 hkm, h.2.2⟩) c d h

private lemma Reach_to_full {n : ℕ} {f : Cell n → Fin 4} {k : ℕ} {c d : Cell n}
    (h : Reach f k c d) : Relation.ReflTransGen (sameAdj f) c d :=
  Relation.ReflTransGen.mono (fun _ _ h => h.2.2) c d h

private lemma Reach_full_iff {n : ℕ} {f : Cell n → Fin 4} (hn : 0 < n) (c d : Cell n) :
    Reach f (n - 1) c d ↔ Relation.ReflTransGen (sameAdj f) c d := by
  constructor
  · exact Reach_to_full
  · intro h
    exact Relation.ReflTransGen.mono (fun u v h => ⟨by omega, by omega, h⟩) c d h

private lemma Reach_dst_le {n : ℕ} {f : Cell n → Fin 4} {k : ℕ} {c d : Cell n}
    (hc : c.1.val ≤ k) (h : Reach f k c d) : d.1.val ≤ k := by
  cases h with
  | refl => exact hc
  | tail _ huv => exact huv.2.1

private lemma path_dichotomy {n : ℕ} {f : Cell n → Fin 4} {k : ℕ} (hk : k < n)
    {c d : Cell n} (hc : c.1.val ≤ k) (hcd : Relation.ReflTransGen (sameAdj f) c d) :
    Reach f k c d ∨
      ∃ (hk1 : k + 1 < n) (j j' : Fin 4),
        Reach f k c (⟨k, hk⟩, j) ∧
          sameAdj f (⟨k, hk⟩, j) (⟨k + 1, hk1⟩, j') ∧
            Relation.ReflTransGen (sameAdj f) (⟨k + 1, hk1⟩, j') d := by
  induction hcd with
  | refl => exact Or.inl .refl
  | @tail u v _ huv ih =>
    rcases ih with hreach | ⟨hk1, j, j', h1, h2, h3⟩
    · have hu_le : u.1.val ≤ k := Reach_dst_le hc hreach
      by_cases hv : v.1.val ≤ k
      · exact Or.inl (hreach.tail ⟨hu_le, hv, huv⟩)
      · have hstep := neighbors_row_step huv.1
        have huk : u.1.val = k := by omega
        have hvk : v.1.val = k + 1 := by omega
        have hk1 : k + 1 < n := hvk ▸ v.1.isLt
        have hu_eq : u = (⟨k, hk⟩, u.2) := by
          rcases u with ⟨ui, uj⟩; ext; exact huk; rfl
        have hv_eq : v = (⟨k + 1, hk1⟩, v.2) := by
          rcases v with ⟨vi, vj⟩; ext; exact hvk; rfl
        exact Or.inr ⟨hk1, u.2, v.2, hu_eq ▸ hreach, hu_eq ▸ hv_eq ▸ huv, hv_eq ▸ .refl⟩
    · exact Or.inr ⟨hk1, j, j', h1, h2, h3.tail huv⟩

private lemma border_crossing {n : ℕ} {f : Cell n → Fin 4} {k : ℕ} (hk : k < n)
    {c d : Cell n} (hcd : Relation.ReflTransGen (sameAdj f) c d)
    (hc : c.1.val ≤ k) (hd : k < d.1.val) :
    ∃ (hk1 : k + 1 < n) (j j' : Fin 4),
      Reach f k c (⟨k, hk⟩, j) ∧
        sameAdj f (⟨k, hk⟩, j) (⟨k + 1, hk1⟩, j') ∧
          Relation.ReflTransGen (sameAdj f) (⟨k + 1, hk1⟩, j') d := by
  rcases path_dichotomy hk hc hcd with hreach | hcross
  · have := Reach_dst_le hc hreach; omega
  · exact hcross

private lemma trapped_reach {n : ℕ} {f : Cell n → Fin 4} {k : ℕ} (hk : k < n)
    {c d : Cell n} (hc : c.1.val ≤ k)
    (htrap : ∀ j : Fin 4, ¬ Reach f k c (⟨k, hk⟩, j))
    (hcd : Relation.ReflTransGen (sameAdj f) c d) :
    Reach f k c d := by
  rcases path_dichotomy hk hc hcd with hreach | ⟨_, j, _, h1, _, _⟩
  · exact hreach
  · exact absurd h1 (htrap j)

/-! ### Cut-Row Lemma for k → k + 1 -/

private def emb {n : ℕ} {k : ℕ} (hk1 : k + 1 < n) : Fin 8 → Cell n
  | ⟨0, _⟩ => (⟨k, by omega⟩, 0)
  | ⟨1, _⟩ => (⟨k, by omega⟩, 1)
  | ⟨2, _⟩ => (⟨k, by omega⟩, 2)
  | ⟨3, _⟩ => (⟨k, by omega⟩, 3)
  | ⟨4, _⟩ => (⟨k + 1, hk1⟩, 0)
  | ⟨5, _⟩ => (⟨k + 1, hk1⟩, 1)
  | ⟨6, _⟩ => (⟨k + 1, hk1⟩, 2)
  | ⟨7, _⟩ => (⟨k + 1, hk1⟩, 3)

private def embLow (j : Fin 4) : Fin 8 :=
  ⟨j.val, by omega⟩

private def embHigh (j : Fin 4) : Fin 8 :=
  ⟨j.val + 4, by omega⟩

private lemma emb_embLow {n : ℕ} {k : ℕ} (hk1 : k + 1 < n) (j : Fin 4) :
    emb hk1 (embLow j) = (⟨k, by omega⟩, j) := by
  fin_cases j <;> rfl

private lemma emb_embHigh {n : ℕ} {k : ℕ} (hk1 : k + 1 < n) (j : Fin 4) :
    emb hk1 (embHigh j) = (⟨k + 1, hk1⟩, j) := by
  fin_cases j <;> rfl

private lemma emb_row_le {n : ℕ} {k : ℕ} (hk1 : k + 1 < n) (x : Fin 8) :
    (emb hk1 x).1.val ≤ k + 1 := by
  fin_cases x <;> dsimp [emb] <;> omega

private def rel8 {n : ℕ} (f : Cell n → Fin 4) {k : ℕ} (hk1 : k + 1 < n) (x y : Fin 8) : Prop :=
  (x.val < 4 ∧ y.val < 4 ∧ Reach f k (emb hk1 x) (emb hk1 y)) ∨
    sameAdj f (emb hk1 x) (emb hk1 y)

private lemma reach_succ_emb {n : ℕ} (f : Cell n → Fin 4) {k : ℕ} (hk1 : k + 1 < n)
    (x y : Fin 8) :
    Reach f (k + 1) (emb hk1 x) (emb hk1 y) ↔ Relation.ReflTransGen (rel8 f hk1) x y := by
  constructor
  · intro h
    let attached (u : Cell n) (z : Fin 8) : Prop :=
      (u.1.val ≤ k ∧ z.val < 4 ∧ Reach f k u (emb hk1 z)) ∨
        (u.1.val = k + 1 ∧ 4 ≤ z.val ∧ u = emb hk1 z)
    have hstep : ∀ {u v : Cell n}, Reach f (k + 1) u v →
        ∀ z : Fin 8, attached u z →
          ∃ w : Fin 8, attached v w ∧ Relation.ReflTransGen (rel8 f hk1) z w := by
      intro u v huv
      induction huv with
      | refl => intro z hz; exact ⟨z, hz, .refl⟩
      | @tail a b _ hab ih =>
        intro z hz
        obtain ⟨w, hw, hzw⟩ := ih z hz
        rcases hw with ⟨ha_le, hw4, haw⟩ | ⟨ha_eq, hw4, haw⟩
        · by_cases hb_le : b.1.val ≤ k
          · refine ⟨w, Or.inl ⟨hb_le, hw4, Reach_trans (.single ⟨hb_le, ha_le, sameAdj_symm hab.2.2⟩) haw⟩, hzw⟩
          · have hbn : b.1.val = k + 1 := by have := hab.2.1; omega
            have han : a.1.val = k := by have := neighbors_row_step hab.2.2.1; omega
            let w' : Fin 8 := embLow a.2
            let w2 : Fin 8 := embHigh b.2
            have ha_emb : a = emb hk1 w' := by
              rw [emb_embLow]; rcases a with ⟨ai, aj⟩; ext; exact han; rfl
            have hb_emb : b = emb hk1 w2 := by
              rw [emb_embHigh]; rcases b with ⟨bi, bj⟩; ext; exact hbn; rfl
            have hww' : rel8 f hk1 w w' := Or.inl ⟨hw4, a.2.isLt, Reach_symm (ha_emb ▸ haw)⟩
            have hw'w2 : rel8 f hk1 w' w2 := Or.inr (ha_emb ▸ hb_emb ▸ hab.2.2)
            exact ⟨w2, Or.inr ⟨hbn, by dsimp [w2, embHigh]; omega, hb_emb⟩,
              (hzw.tail hww').tail hw'w2⟩
        · by_cases hb_le : b.1.val ≤ k
          · have hbn : b.1.val = k := by have := neighbors_row_step hab.2.2.1; omega
            let w2 : Fin 8 := embLow b.2
            have hb_emb : b = emb hk1 w2 := by
              rw [emb_embLow]; rcases b with ⟨bi, bj⟩; ext; exact hbn; rfl
            have hww2 : rel8 f hk1 w w2 := Or.inr (haw ▸ hb_emb ▸ hab.2.2)
            exact ⟨w2, Or.inl ⟨hb_le, b.2.isLt, hb_emb ▸ .refl⟩, hzw.tail hww2⟩
          · have hbn : b.1.val = k + 1 := by have := hab.2.1; omega
            let w2 : Fin 8 := embHigh b.2
            have hb_emb : b = emb hk1 w2 := by
              rw [emb_embHigh]; rcases b with ⟨bi, bj⟩; ext; exact hbn; rfl
            have hww2 : rel8 f hk1 w w2 := Or.inr (haw ▸ hb_emb ▸ hab.2.2)
            exact ⟨w2, Or.inr ⟨hbn, by dsimp [w2, embHigh]; omega, hb_emb⟩, hzw.tail hww2⟩
    have hx : attached (emb hk1 x) x := by
      fin_cases x <;> [exact Or.inl ⟨le_rfl, by decide, .refl⟩;
        exact Or.inl ⟨le_rfl, by decide, .refl⟩;
        exact Or.inl ⟨le_rfl, by decide, .refl⟩;
        exact Or.inl ⟨le_rfl, by decide, .refl⟩;
        exact Or.inr ⟨rfl, by decide, rfl⟩;
        exact Or.inr ⟨rfl, by decide, rfl⟩;
        exact Or.inr ⟨rfl, by decide, rfl⟩;
        exact Or.inr ⟨rfl, by decide, rfl⟩]
    obtain ⟨w, hw, hxw⟩ := hstep h x hx
    rcases hw with ⟨hy_le, hw4, hyw⟩ | ⟨hy_eq, hw4, hyw⟩
    · have hy4 : y.val < 4 := by
        fin_cases y <;> dsimp [emb] at hy_le ⊢ <;> omega
      exact hxw.tail (Or.inl ⟨hw4, hy4, Reach_symm hyw⟩)
    · have hwy : w = y := by
        have hinj : ∀ a b : Fin 8, emb hk1 a = emb hk1 b → a = b := by
          intro a b hab
          fin_cases a <;> fin_cases b <;> dsimp only [emb] at hab <;>
            simp only [Prod.mk.injEq, Fin.mk.injEq] at hab <;>
            first | rfl | omega
        exact hinj w y hyw.symm
      exact hwy ▸ hxw
  · intro h
    induction h with
    | refl => exact .refl
    | @tail u v _ huv ih =>
      rcases huv with ⟨_, _, hreach⟩ | hadj
      · exact Reach_trans ih (Reach_mono (Nat.le_succ k) hreach)
      · exact ih.tail ⟨emb_row_le hk1 u, emb_row_le hk1 v, hadj⟩

private lemma stepComp_iff_reach {n : ℕ} (f : Cell n → Fin 4) {k : ℕ} (hk1 : k + 1 < n)
    (s : State) (hrow : rowOf f ⟨k, by omega⟩ = ⟨s.r0, s.r1, s.r2, s.r3⟩)
    (hcomp : ∀ i j : Fin 4, s.comp i = s.comp j ↔ Reach f k (⟨k, by omega⟩, i) (⟨k, by omega⟩, j)) :
    let nr := rowOf f ⟨k + 1, hk1⟩
    let c := stepComp s nr
    ∀ x y : Fin 8, c.get x = c.get y ↔ Reach f (k + 1) (emb hk1 x) (emb hk1 y) := by
  intro nr c x y
  rw [reach_succ_emb f hk1]
  have hk : k < n := by omega
  -- Helper: relate s.r_i and nr.c_j equality to f equality
  have hr_eq : ∀ j : Fin 4, s.row j = C4.ofFin (f (⟨k, hk⟩, j)) := fun j => by
    have h1 := congrArg (fun r => r.get j) hrow
    rw [rowOf_get] at h1
    fin_cases j <;> simpa [State.row, Row.get] using h1.symm
  have hnr_eq : ∀ j : Fin 4, nr.get j = C4.ofFin (f (⟨k + 1, hk1⟩, j)) := fun j => rowOf_get f ⟨k + 1, hk1⟩ j
  have hv_iff : ∀ (j1 j2 : Fin 4),
      (s.row j1).eqb (nr.get j2) = true ↔ f (⟨k, hk⟩, j1) = f (⟨k + 1, hk1⟩, j2) := fun j1 j2 => by
    rw [C4.eqb_iff, hr_eq, hnr_eq]; exact C4.ofFin_injective.eq_iff
  have hh_iff : ∀ (j1 j2 : Fin 4),
      (nr.get j1).eqb (nr.get j2) = true ↔ f (⟨k + 1, hk1⟩, j1) = f (⟨k + 1, hk1⟩, j2) := fun j1 j2 => by
    rw [C4.eqb_iff, hnr_eq, hnr_eq]; exact C4.ofFin_injective.eq_iff
  -- Initial Comp8
  let c0 : Comp8 := ⟨s.p0.toC8, s.p1.toC8, s.p2.toC8, s.p3.toC8, .x4, .x5, .x6, .x7⟩
  let R0 : Fin 8 → Fin 8 → Prop := fun u v =>
    u = v ∨ (u.val < 4 ∧ v.val < 4 ∧ Reach f k (emb hk1 u) (emb hk1 v))
  have hc0_low : ∀ j : Fin 4, c0.get (embLow j) = (s.comp j).toC8 := fun j => by
    fin_cases j <;> rfl
  have hc0_high : ∀ j : Fin 4, c0.get (embHigh j) = match j with
      | ⟨0, _⟩ => .x4 | ⟨1, _⟩ => .x5 | ⟨2, _⟩ => .x6 | ⟨3, _⟩ => .x7 := fun j => by
    fin_cases j <;> rfl
  have hc0_ne : ∀ (a : C4) (j : Fin 4), a.toC8 ≠ c0.get (embHigh j) := by
    intro a j; rw [hc0_high]; cases a <;> fin_cases j <;> decide
  have hc0_high_inj : ∀ j1 j2 : Fin 4, c0.get (embHigh j1) = c0.get (embHigh j2) ↔ j1 = j2 := by
    intro j1 j2; rw [hc0_high, hc0_high]; fin_cases j1 <;> fin_cases j2 <;> decide
  have hc0 : ∀ u v : Fin 8, c0.get u = c0.get v ↔ R0 u v := by
    intro u v
    by_cases hu : u.val < 4 <;> by_cases hv : v.val < 4
    · let ju : Fin 4 := ⟨u.val, hu⟩
      let jv : Fin 4 := ⟨v.val, hv⟩
      have hu_eq : u = embLow ju := Fin.ext rfl
      have hv_eq : v = embLow jv := Fin.ext rfl
      rw [hu_eq, hv_eq, hc0_low, hc0_low, C4.toC8_injective.eq_iff, hcomp]
      dsimp only [R0]
      rw [emb_embLow, emb_embLow]
      constructor
      · intro h; exact Or.inr ⟨hu, hv, h⟩
      · rintro (h | ⟨_, _, h⟩)
        · have hj : ju = jv := Fin.ext (by simpa [embLow] using congrArg Fin.val h)
          rw [hj]; exact .refl
        · exact h
    · let ju : Fin 4 := ⟨u.val, hu⟩
      let jv : Fin 4 := ⟨v.val - 4, by omega⟩
      have hu_eq : u = embLow ju := Fin.ext rfl
      have hv_eq : v = embHigh jv := Fin.ext (by dsimp [embHigh, jv]; omega)
      rw [hu_eq, hv_eq, hc0_low]
      constructor
      · intro h; exact absurd h (hc0_ne _ jv)
      · rintro (h | ⟨_, h2, _⟩)
        · have := congrArg Fin.val h; dsimp [embLow, embHigh, ju, jv] at this; omega
        · dsimp [embHigh, jv] at h2; omega
    · let ju : Fin 4 := ⟨u.val - 4, by omega⟩
      let jv : Fin 4 := ⟨v.val, hv⟩
      have hu_eq : u = embHigh ju := Fin.ext (by dsimp [embHigh, ju]; omega)
      have hv_eq : v = embLow jv := Fin.ext rfl
      rw [hu_eq, hv_eq, hc0_low]
      constructor
      · intro h; exact absurd h.symm (hc0_ne _ ju)
      · rintro (h | ⟨h1, _, _⟩)
        · have := congrArg Fin.val h; dsimp [embLow, embHigh, ju, jv] at this; omega
        · dsimp [embHigh, ju] at h1; omega
    · let ju : Fin 4 := ⟨u.val - 4, by omega⟩
      let jv : Fin 4 := ⟨v.val - 4, by omega⟩
      have hu_eq : u = embHigh ju := Fin.ext (by dsimp [embHigh, ju]; omega)
      have hv_eq : v = embHigh jv := Fin.ext (by dsimp [embHigh, jv]; omega)
      rw [hu_eq, hv_eq, hc0_high_inj]
      dsimp only [R0]
      constructor
      · intro h; exact Or.inl (congrArg embHigh h)
      · rintro (h | ⟨h1, _, _⟩)
        · have := congrArg Fin.val h; dsimp [embHigh] at this; exact Fin.ext (by omega)
        · dsimp [embHigh, ju] at h1; omega
  -- Helper for conditional union step
  have step_cond : ∀ {cc : Comp8} {E : Fin 8 → Fin 8 → Prop},
      (∀ u v, cc.get u = cc.get v ↔ Relation.ReflTransGen E u v) →
      (∀ u v, E u v → E v u) →
      ∀ (flag : Bool) (a b : Fin 8) (P : Prop), (flag = true ↔ P) →
      ∀ u v, (if flag then cc.union (cc.get a) (cc.get b) else cc).get u =
             (if flag then cc.union (cc.get a) (cc.get b) else cc).get v ↔
             Relation.ReflTransGen (fun p q => E p q ∨ (P ∧ ((p = a ∧ q = b) ∨ (p = b ∧ q = a)))) u v := by
    intro cc E hcc hEsym flag a b P hP u v
    have hR_eq : Equivalence (Relation.ReflTransGen E) :=
      ⟨fun _ => .refl,
       fun h => by induction h with | refl => exact .refl | tail _ h1 ih => exact .trans (.single (hEsym _ _ h1)) ih,
       fun h1 h2 => h1.trans h2⟩
    by_cases hf : flag = true
    · rw [if_pos hf]
      have hp : P := hP.1 hf
      rw [Comp8.union_rtg hR_eq hcc a b u v]
      constructor
      · intro h
        induction h with
        | refl => exact .refl
        | tail _ h1 ih =>
          rcases h1 with hE | hpair
          · exact ih.trans (Relation.ReflTransGen.mono (fun _ _ h => Or.inl h) _ _ hE)
          · exact ih.tail (Or.inr ⟨hp, hpair⟩)
      · intro h
        induction h with
        | refl => exact .refl
        | tail _ h1 ih =>
          rcases h1 with hE | ⟨_, hpair⟩
          · exact ih.tail (Or.inl (.single hE))
          · exact ih.tail (Or.inr hpair)
    · rw [if_neg hf]
      have hnp : ¬ P := mt hP.2 hf
      rw [hcc]
      constructor
      · intro h; exact Relation.ReflTransGen.mono (fun _ _ h => Or.inl h) _ _ h
      · intro h; exact Relation.ReflTransGen.mono (fun _ _ h => h.elim id (fun h => absurd h.1 hnp)) _ _ h
  -- Start with E0 = R0 (which is already symmetric and transitive!)
  have hR0_sym : ∀ u v, R0 u v → R0 v u := by
    rintro u v (rfl | ⟨h1, h2, h3⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨h2, h1, Reach_symm h3⟩
  have hR0_rtg : ∀ u v, c0.get u = c0.get v ↔ Relation.ReflTransGen R0 u v := by
    intro u v
    rw [hc0]
    constructor
    · exact Relation.ReflTransGen.single
    · intro h
      induction h with
      | refl => exact Or.inl rfl
      | tail _ h1 ih =>
        rcases ih with rfl | ⟨hu, hw, h1'⟩
        · exact h1
        · rcases h1 with rfl | ⟨_, hv, h2'⟩
          · exact Or.inr ⟨hu, hw, h1'⟩
          · exact Or.inr ⟨hu, hv, Reach_trans h1' h2'⟩
  -- Apply the 6 conditional unions
  let v0 := s.r1.eqb nr.c0
  let v1 := s.r2.eqb nr.c1
  let v2 := s.r3.eqb nr.c2
  let h0 := nr.c0.eqb nr.c1
  let h1 := nr.c1.eqb nr.c2
  let h2 := nr.c2.eqb nr.c3
  let c1 := if v0 then c0.union c0.c1 c0.c4 else c0
  let c2 := if v1 then c1.union c1.c2 c1.c5 else c1
  let c3 := if v2 then c2.union c2.c3 c2.c6 else c2
  let c4 := if h0 then c3.union c3.c4 c3.c5 else c3
  let c5 := if h1 then c4.union c4.c5 c4.c6 else c4
  let c6 := if h2 then c5.union c5.c6 c5.c7 else c5
  have hc_eq : c = c6 := rfl
  rw [hc_eq]
  let E1 : Fin 8 → Fin 8 → Prop := fun u v =>
    R0 u v ∨ (f (⟨k, hk⟩, 1) = f (⟨k + 1, hk1⟩, 0) ∧ ((u = 1 ∧ v = 4) ∨ (u = 4 ∧ v = 1)))
  let E2 : Fin 8 → Fin 8 → Prop := fun u v =>
    E1 u v ∨ (f (⟨k, hk⟩, 2) = f (⟨k + 1, hk1⟩, 1) ∧ ((u = 2 ∧ v = 5) ∨ (u = 5 ∧ v = 2)))
  let E3 : Fin 8 → Fin 8 → Prop := fun u v =>
    E2 u v ∨ (f (⟨k, hk⟩, 3) = f (⟨k + 1, hk1⟩, 2) ∧ ((u = 3 ∧ v = 6) ∨ (u = 6 ∧ v = 3)))
  let E4 : Fin 8 → Fin 8 → Prop := fun u v =>
    E3 u v ∨ (f (⟨k + 1, hk1⟩, 0) = f (⟨k + 1, hk1⟩, 1) ∧ ((u = 4 ∧ v = 5) ∨ (u = 5 ∧ v = 4)))
  let E5 : Fin 8 → Fin 8 → Prop := fun u v =>
    E4 u v ∨ (f (⟨k + 1, hk1⟩, 1) = f (⟨k + 1, hk1⟩, 2) ∧ ((u = 5 ∧ v = 6) ∨ (u = 6 ∧ v = 5)))
  have h1s : ∀ u v, c1.get u = c1.get v ↔ Relation.ReflTransGen E1 u v :=
    step_cond hR0_rtg hR0_sym v0 1 4 (f (⟨k, hk⟩, 1) = f (⟨k + 1, hk1⟩, 0)) (by simpa [State.row, Row.get] using hv_iff 1 0)
  have hE1_sym : ∀ u v, E1 u v → E1 v u := by
    rintro u v (h | ⟨hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · exact Or.inl (hR0_sym _ _ h)
    · exact Or.inr ⟨hp, Or.inr ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨hp, Or.inl ⟨rfl, rfl⟩⟩
  have h2s : ∀ u v, c2.get u = c2.get v ↔ Relation.ReflTransGen E2 u v :=
    step_cond h1s hE1_sym v1 2 5 (f (⟨k, hk⟩, 2) = f (⟨k + 1, hk1⟩, 1)) (by simpa [State.row, Row.get] using hv_iff 2 1)
  have hE2_sym : ∀ u v, E2 u v → E2 v u := by
    rintro u v (h | ⟨hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · exact Or.inl (hE1_sym _ _ h)
    · exact Or.inr ⟨hp, Or.inr ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨hp, Or.inl ⟨rfl, rfl⟩⟩
  have h3s : ∀ u v, c3.get u = c3.get v ↔ Relation.ReflTransGen E3 u v :=
    step_cond h2s hE2_sym v2 3 6 (f (⟨k, hk⟩, 3) = f (⟨k + 1, hk1⟩, 2)) (by simpa [State.row, Row.get] using hv_iff 3 2)
  have hE3_sym : ∀ u v, E3 u v → E3 v u := by
    rintro u v (h | ⟨hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · exact Or.inl (hE2_sym _ _ h)
    · exact Or.inr ⟨hp, Or.inr ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨hp, Or.inl ⟨rfl, rfl⟩⟩
  have h4s : ∀ u v, c4.get u = c4.get v ↔ Relation.ReflTransGen E4 u v :=
    step_cond h3s hE3_sym h0 4 5 (f (⟨k + 1, hk1⟩, 0) = f (⟨k + 1, hk1⟩, 1)) (by simpa [Row.get] using hh_iff 0 1)
  have hE4_sym : ∀ u v, E4 u v → E4 v u := by
    rintro u v (h | ⟨hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · exact Or.inl (hE3_sym _ _ h)
    · exact Or.inr ⟨hp, Or.inr ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨hp, Or.inl ⟨rfl, rfl⟩⟩
  have h5s : ∀ u v, c5.get u = c5.get v ↔ Relation.ReflTransGen E5 u v :=
    step_cond h4s hE4_sym h1 5 6 (f (⟨k + 1, hk1⟩, 1) = f (⟨k + 1, hk1⟩, 2)) (by simpa [Row.get] using hh_iff 1 2)
  have hE5_sym : ∀ u v, E5 u v → E5 v u := by
    rintro u v (h | ⟨hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · exact Or.inl (hE4_sym _ _ h)
    · exact Or.inr ⟨hp, Or.inr ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨hp, Or.inl ⟨rfl, rfl⟩⟩
  have h6s : ∀ u v, c6.get u = c6.get v ↔
      Relation.ReflTransGen (fun p q => E5 p q ∨ (f (⟨k + 1, hk1⟩, 2) = f (⟨k + 1, hk1⟩, 3) ∧ ((p = 6 ∧ q = 7) ∨ (p = 7 ∧ q = 6)))) u v :=
    step_cond h5s hE5_sym h2 6 7 (f (⟨k + 1, hk1⟩, 2) = f (⟨k + 1, hk1⟩, 3)) (by simpa [Row.get] using hh_iff 2 3)
  rw [h6s x y]
  -- Show the final 6-edge relation has the exact same ReflTransGen as rel8 f hk1!
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ huv ih =>
      rcases huv with (((((hR0 | ⟨hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩) |
        ⟨hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩) | ⟨hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩) |
        ⟨hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩) | ⟨hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩) | ⟨hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · rcases hR0 with rfl | ⟨h1, h2, h3⟩
        · exact ih
        · exact ih.tail (Or.inl ⟨h1, h2, h3⟩)
      · exact ih.tail (Or.inr ⟨Or.inr (Or.inl ⟨rfl, by simp [emb, absCol]⟩), hp⟩)
      · exact ih.tail (Or.inr ⟨Or.inr (Or.inr ⟨rfl, by simp [emb, absCol]⟩), hp.symm⟩)
      · exact ih.tail (Or.inr ⟨Or.inr (Or.inl ⟨rfl, by simp [emb, absCol]⟩), hp⟩)
      · exact ih.tail (Or.inr ⟨Or.inr (Or.inr ⟨rfl, by simp [emb, absCol]⟩), hp.symm⟩)
      · exact ih.tail (Or.inr ⟨Or.inr (Or.inl ⟨rfl, by simp [emb, absCol]⟩), hp⟩)
      · exact ih.tail (Or.inr ⟨Or.inr (Or.inr ⟨rfl, by simp [emb, absCol]⟩), hp.symm⟩)
      · exact ih.tail (Or.inr ⟨Or.inl ⟨rfl, Or.inl rfl⟩, hp⟩)
      · exact ih.tail (Or.inr ⟨Or.inl ⟨rfl, Or.inr rfl⟩, hp.symm⟩)
      · exact ih.tail (Or.inr ⟨Or.inl ⟨rfl, Or.inl rfl⟩, hp⟩)
      · exact ih.tail (Or.inr ⟨Or.inl ⟨rfl, Or.inr rfl⟩, hp.symm⟩)
      · exact ih.tail (Or.inr ⟨Or.inl ⟨rfl, Or.inl rfl⟩, hp⟩)
      · exact ih.tail (Or.inr ⟨Or.inl ⟨rfl, Or.inr rfl⟩, hp.symm⟩)
  · intro h
    refine Relation.ReflTransGen.mono ?_ _ _ h
    intro u v huv
    rcases huv with ⟨h1, h2, h3⟩ | ⟨hnb, hfeq⟩
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨h1, h2, h3⟩))))))
    · fin_cases u <;> fin_cases v <;> dsimp only at hnb hfeq ⊢
      all_goals
        have hnb0 := hnb
        simp only [emb, neighbors, absCol, Fin.mk.injEq] at hnb hfeq
      all_goals
        first
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨by decide, by decide, .single ⟨le_rfl, le_rfl, hnb0, hfeq⟩⟩))))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hfeq, Or.inl ⟨rfl, rfl⟩⟩)))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hfeq.symm, Or.inr ⟨rfl, rfl⟩⟩)))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hfeq, Or.inl ⟨rfl, rfl⟩⟩))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hfeq.symm, Or.inr ⟨rfl, rfl⟩⟩))))
        | exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hfeq, Or.inl ⟨rfl, rfl⟩⟩)))
        | exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hfeq.symm, Or.inr ⟨rfl, rfl⟩⟩)))
        | exact Or.inl (Or.inl (Or.inr ⟨hfeq, Or.inl ⟨rfl, rfl⟩⟩))
        | exact Or.inl (Or.inl (Or.inr ⟨hfeq.symm, Or.inr ⟨rfl, rfl⟩⟩))
        | exact Or.inl (Or.inr ⟨hfeq, Or.inl ⟨rfl, rfl⟩⟩)
        | exact Or.inl (Or.inr ⟨hfeq.symm, Or.inr ⟨rfl, rfl⟩⟩)
        | exact Or.inr ⟨hfeq, Or.inl ⟨rfl, rfl⟩⟩
        | exact Or.inr ⟨hfeq.symm, Or.inr ⟨rfl, rfl⟩⟩
        | (exfalso; omega)

/-! ### Part 3: Prefix invariant and exact bijection with Valid -/

private structure PrefixOk {n : ℕ} (k : ℕ) (hk : k < n) (f : Cell n → Fin 4) (s : State) : Prop where
  rowMatch : rowOf f ⟨k, hk⟩ = ⟨s.r0, s.r1, s.r2, s.r3⟩
  degPrefix : ∀ (i : Fin n) (j : Fin 4), i.val ≤ k → prefixDeg f i j ≤ 2
  degFull : ∀ (i : Fin n) (j : Fin 4), i.val < k → neighborSame f (i, j) ≤ 2
  deg1 : prefixDeg f ⟨k, hk⟩ 1 = s.d1.toNat
  deg2 : prefixDeg f ⟨k, hk⟩ 2 = s.d2.toNat
  deg3 : prefixDeg f ⟨k, hk⟩ 3 = s.d3.toNat
  compMatch : ∀ i j : Fin 4, s.comp i = s.comp j ↔ Reach f k (⟨k, hk⟩, i) (⟨k, hk⟩, j)
  closedTrue : ∀ v : C4, s.closed v = true →
    (∀ j : Fin 4, f (⟨k, hk⟩, j) ≠ v.toFin) ∧
    (∃ c : Cell n, c.1.val ≤ k ∧ f c = v.toFin) ∧
    (∀ c d : Cell n, c.1.val ≤ k → d.1.val ≤ k → f c = v.toFin → f d = v.toFin → Reach f k c d)
  closedFalse : ∀ v : C4, s.closed v = false →
    ∀ c : Cell n, c.1.val ≤ k → f c = v.toFin → ∃ j : Fin 4, Reach f k c (⟨k, hk⟩, j)

private lemma row0_reach_iff {n : ℕ} (f : Cell n → Fin 4) (hn : 0 < n) (i j : Fin 4) :
    Reach f 0 (⟨0, hn⟩, i) (⟨0, hn⟩, j) ↔
      (i = j) ∨
      (i.val < j.val ∧ ∀ m : Fin 4, i.val ≤ m.val → (hm : m.val < j.val) →
        f (⟨0, hn⟩, m) = f (⟨0, hn⟩, ⟨m.val + 1, by have := j.isLt; omega⟩)) ∨
      (j.val < i.val ∧ ∀ m : Fin 4, j.val ≤ m.val → (hm : m.val < i.val) →
        f (⟨0, hn⟩, m) = f (⟨0, hn⟩, ⟨m.val + 1, by have := i.isLt; omega⟩)) := by
  have step_adj : ∀ a b : Fin 4, prefixAdj f 0 (⟨0, hn⟩, a) (⟨0, hn⟩, b) ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val) ∧ f (⟨0, hn⟩, a) = f (⟨0, hn⟩, b) := by
    intro a b
    unfold prefixAdj sameAdj neighbors
    simp only [le_refl, true_and, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, false_and, or_false]
  constructor
  · intro h
    suffices ∀ c d : Cell n, Reach f 0 c d → c.1.val = 0 →
        d.1.val = 0 ∧
        (c.2 = d.2 ∨
         (c.2.val < d.2.val ∧ ∀ m : Fin 4, c.2.val ≤ m.val → (hm : m.val < d.2.val) →
           f (⟨0, hn⟩, m) = f (⟨0, hn⟩, ⟨m.val + 1, by have := d.2.isLt; omega⟩)) ∨
         (d.2.val < c.2.val ∧ ∀ m : Fin 4, d.2.val ≤ m.val → (hm : m.val < c.2.val) →
           f (⟨0, hn⟩, m) = f (⟨0, hn⟩, ⟨m.val + 1, by have := c.2.isLt; omega⟩))) by
      exact (this _ _ h rfl).2
    intro c d hcd hc0
    induction hcd with
    | refl => exact ⟨hc0, Or.inl rfl⟩
    | @tail u v _ huv ih =>
      have hu0 : u.1 = ⟨0, hn⟩ := Fin.ext ih.1
      have hv0 : v.1 = ⟨0, hn⟩ := Fin.ext (Nat.eq_zero_of_le_zero huv.2.1)
      have hu_eq : u = (⟨0, hn⟩, u.2) := Prod.ext hu0 rfl
      have hv_eq : v = (⟨0, hn⟩, v.2) := Prod.ext hv0 rfl
      have huv' := (step_adj u.2 v.2).1 (hu_eq ▸ hv_eq ▸ huv)
      refine ⟨Nat.eq_zero_of_le_zero huv.2.1, ?_⟩
      rcases huv' with ⟨hstep | hstep, hfeq⟩
      · rcases ih.2 with heq | ⟨hlt, hall⟩ | ⟨hlt, hall⟩
        · right; left; refine ⟨by omega, fun m hm1 hm2 => ?_⟩
          have hm : m = u.2 := Fin.ext (by omega)
          subst hm; convert hfeq
        · right; left; refine ⟨by omega, fun m hm1 hm2 => ?_⟩
          by_cases hmu : m.val < u.2.val
          · exact hall m hm1 hmu
          · have hm : m = u.2 := Fin.ext (by omega)
            subst hm; convert hfeq
        · by_cases heq' : c.2 = v.2
          · exact Or.inl heq'
          · right; right; refine ⟨by omega, fun m hm1 hm2 => hall m (by omega) hm2⟩
      · rcases ih.2 with heq | ⟨hlt, hall⟩ | ⟨hlt, hall⟩
        · right; right; refine ⟨by omega, fun m hm1 hm2 => ?_⟩
          have hm : m = v.2 := Fin.ext (by omega)
          subst hm; convert hfeq.symm
        · by_cases heq' : c.2 = v.2
          · exact Or.inl heq'
          · right; left; refine ⟨by omega, fun m hm1 hm2 => hall m hm1 (by omega)⟩
        · right; right; refine ⟨by omega, fun m hm1 hm2 => ?_⟩
          by_cases hmv : u.2.val ≤ m.val
          · exact hall m hmv hm2
          · have hm : m = v.2 := Fin.ext (by omega)
            subst hm; convert hfeq.symm
  · have go : ∀ (a b : Fin 4), a.val ≤ b.val →
        (∀ m : Fin 4, a.val ≤ m.val → (hm : m.val < b.val) →
          f (⟨0, hn⟩, m) = f (⟨0, hn⟩, ⟨m.val + 1, by have := b.isLt; omega⟩)) →
        Reach f 0 (⟨0, hn⟩, a) (⟨0, hn⟩, b) := by
      intro a b hab h
      fin_cases a <;> fin_cases b <;> dsimp only at hab h ⊢
      all_goals first | exact .refl | omega | skip
      · exact Relation.ReflTransGen.single ((step_adj 0 1).2 ⟨Or.inl rfl, h 0 (by decide) (by decide)⟩)
      · exact (Relation.ReflTransGen.single ((step_adj 0 1).2 ⟨Or.inl rfl, h 0 (by decide) (by decide)⟩)).tail
          ((step_adj 1 2).2 ⟨Or.inl rfl, h 1 (by decide) (by decide)⟩)
      · exact ((Relation.ReflTransGen.single ((step_adj 0 1).2 ⟨Or.inl rfl, h 0 (by decide) (by decide)⟩)).tail
          ((step_adj 1 2).2 ⟨Or.inl rfl, h 1 (by decide) (by decide)⟩)).tail
          ((step_adj 2 3).2 ⟨Or.inl rfl, h 2 (by decide) (by decide)⟩)
      · exact Relation.ReflTransGen.single ((step_adj 1 2).2 ⟨Or.inl rfl, h 1 (by decide) (by decide)⟩)
      · exact (Relation.ReflTransGen.single ((step_adj 1 2).2 ⟨Or.inl rfl, h 1 (by decide) (by decide)⟩)).tail
          ((step_adj 2 3).2 ⟨Or.inl rfl, h 2 (by decide) (by decide)⟩)
      · exact Relation.ReflTransGen.single ((step_adj 2 3).2 ⟨Or.inl rfl, h 2 (by decide) (by decide)⟩)
    rintro (rfl | ⟨hlt, hall⟩ | ⟨hlt, hall⟩)
    · exact .refl
    · exact go i j (le_of_lt hlt) hall
    · exact Reach_symm (go j i (le_of_lt hlt) hall)

private def initCompOf (h0 h1 h2 : Bool) : Fin 4 → C4 :=
  let p1 : C4 := if h0 then .a0 else .a1
  let p2 : C4 := if h1 then p1 else if h0 then .a1 else .a2
  let p3 : C4 := if h2 then p2 else if h0 then (if h1 then .a1 else .a2) else if h1 then .a2 else .a3
  fun j => match j with | ⟨0, _⟩ => .a0 | ⟨1, _⟩ => p1 | ⟨2, _⟩ => p2 | ⟨3, _⟩ => p3

private def edgeOf3 (h0 h1 h2 : Bool) : Fin 4 → Bool
  | ⟨0, _⟩ => h0 | ⟨1, _⟩ => h1 | ⟨2, _⟩ => h2 | ⟨3, _⟩ => false

private lemma initCompOf_iff (h0 h1 h2 : Bool) (i j : Fin 4) :
    initCompOf h0 h1 h2 i = initCompOf h0 h1 h2 j ↔
      i = j ∨
      (i.val < j.val ∧ ∀ m : Fin 4, i.val ≤ m.val → m.val < j.val → edgeOf3 h0 h1 h2 m = true) ∨
      (j.val < i.val ∧ ∀ m : Fin 4, j.val ≤ m.val → m.val < i.val → edgeOf3 h0 h1 h2 m = true) := by
  revert h0 h1 h2 i j
  decide

private lemma initState_PrefixOk {n : ℕ} (f : Cell n → Fin 4) (hn : 0 < n) {s : State}
    (hs : initState (rowOf f ⟨0, hn⟩) = some s) :
    PrefixOk 0 hn f s ∧ f (⟨0, hn⟩, 0) = 0 ∧ f (⟨0, hn⟩, 3) = 1 := by
  unfold initState at hs
  split_ifs at hs with h03
  · cases hs
    simp only [Bool.and_eq_true, C4.eqb_iff] at h03
    have hf0 : f (⟨0, hn⟩, 0) = 0 := by
      have h1 := congrArg C4.toFin h03.1
      dsimp only [rowOf] at h1
      rw [C4.toFin_ofFin] at h1
      exact h1
    have hf3 : f (⟨0, hn⟩, 3) = 1 := by
      have h1 := congrArg C4.toFin h03.2
      dsimp only [rowOf] at h1
      rw [C4.toFin_ofFin] at h1
      exact h1
    have hd := prefixDeg_zero_eval f hn
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hf0, hf3⟩
    · rfl
    · intro i j hi
      have hi0 : i = ⟨0, hn⟩ := Fin.ext (Nat.eq_zero_of_le_zero hi)
      subst hi0
      fin_cases j
      · change prefixDeg f ⟨0, hn⟩ 0 ≤ 2; rw [hd.1]; split_ifs <;> omega
      · change prefixDeg f ⟨0, hn⟩ 1 ≤ 2; rw [hd.2.1]; split_ifs <;> omega
      · change prefixDeg f ⟨0, hn⟩ 2 ≤ 2; rw [hd.2.2.1]; split_ifs <;> omega
      · change prefixDeg f ⟨0, hn⟩ 3 ≤ 2; rw [hd.2.2.2]; split_ifs <;> omega
    · intro i j hi; omega
    · rw [hd.2.1, deg2_toNat]
    · rw [hd.2.2.1, deg2_toNat]
    · rw [hd.2.2.2]; split_ifs <;> rfl
    · intro i j
      rw [row0_reach_iff f hn]
      have h01 : ((rowOf f ⟨0, hn⟩).c0.eqb (rowOf f ⟨0, hn⟩).c1 = true) ↔
          f (⟨0, hn⟩, 0) = f (⟨0, hn⟩, 1) := by
        rw [C4.eqb_iff]; exact C4.ofFin_injective.eq_iff
      have h12 : ((rowOf f ⟨0, hn⟩).c1.eqb (rowOf f ⟨0, hn⟩).c2 = true) ↔
          f (⟨0, hn⟩, 1) = f (⟨0, hn⟩, 2) := by
        rw [C4.eqb_iff]; exact C4.ofFin_injective.eq_iff
      have h23 : ((rowOf f ⟨0, hn⟩).c2.eqb (rowOf f ⟨0, hn⟩).c3 = true) ↔
          f (⟨0, hn⟩, 2) = f (⟨0, hn⟩, 3) := by
        rw [C4.eqb_iff]; exact C4.ofFin_injective.eq_iff
      have hcomp_eq : ∀ l : Fin 4,
          State.comp ⟨(rowOf f ⟨0, hn⟩).c0, (rowOf f ⟨0, hn⟩).c1, (rowOf f ⟨0, hn⟩).c2, (rowOf f ⟨0, hn⟩).c3,
            deg2 ((rowOf f ⟨0, hn⟩).c0.eqb (rowOf f ⟨0, hn⟩).c1) ((rowOf f ⟨0, hn⟩).c1.eqb (rowOf f ⟨0, hn⟩).c2),
            deg2 ((rowOf f ⟨0, hn⟩).c1.eqb (rowOf f ⟨0, hn⟩).c2) ((rowOf f ⟨0, hn⟩).c2.eqb (rowOf f ⟨0, hn⟩).c3),
            if (rowOf f ⟨0, hn⟩).c2.eqb (rowOf f ⟨0, hn⟩).c3 then D3.d1 else D3.d0,
            C4.a0,
            if (rowOf f ⟨0, hn⟩).c0.eqb (rowOf f ⟨0, hn⟩).c1 then C4.a0 else C4.a1,
            if (rowOf f ⟨0, hn⟩).c1.eqb (rowOf f ⟨0, hn⟩).c2 then
              (if (rowOf f ⟨0, hn⟩).c0.eqb (rowOf f ⟨0, hn⟩).c1 then C4.a0 else C4.a1)
            else if (rowOf f ⟨0, hn⟩).c0.eqb (rowOf f ⟨0, hn⟩).c1 then C4.a1 else C4.a2,
            if (rowOf f ⟨0, hn⟩).c2.eqb (rowOf f ⟨0, hn⟩).c3 then
              (if (rowOf f ⟨0, hn⟩).c1.eqb (rowOf f ⟨0, hn⟩).c2 then
                (if (rowOf f ⟨0, hn⟩).c0.eqb (rowOf f ⟨0, hn⟩).c1 then C4.a0 else C4.a1)
               else if (rowOf f ⟨0, hn⟩).c0.eqb (rowOf f ⟨0, hn⟩).c1 then C4.a1 else C4.a2)
            else if (rowOf f ⟨0, hn⟩).c0.eqb (rowOf f ⟨0, hn⟩).c1 then
              (if (rowOf f ⟨0, hn⟩).c1.eqb (rowOf f ⟨0, hn⟩).c2 then C4.a1 else C4.a2)
            else if (rowOf f ⟨0, hn⟩).c1.eqb (rowOf f ⟨0, hn⟩).c2 then C4.a2 else C4.a3,
            false, false⟩ l =
          initCompOf ((rowOf f ⟨0, hn⟩).c0.eqb (rowOf f ⟨0, hn⟩).c1)
            ((rowOf f ⟨0, hn⟩).c1.eqb (rowOf f ⟨0, hn⟩).c2)
            ((rowOf f ⟨0, hn⟩).c2.eqb (rowOf f ⟨0, hn⟩).c3) l := fun l => by
        fin_cases l <;> rfl
      rw [hcomp_eq i, hcomp_eq j, initCompOf_iff]
      have hedge : ∀ (m : Fin 4) (hm : m.val < 3),
          edgeOf3 ((rowOf f ⟨0, hn⟩).c0.eqb (rowOf f ⟨0, hn⟩).c1)
            ((rowOf f ⟨0, hn⟩).c1.eqb (rowOf f ⟨0, hn⟩).c2)
            ((rowOf f ⟨0, hn⟩).c2.eqb (rowOf f ⟨0, hn⟩).c3) m = true ↔
          f (⟨0, hn⟩, m) = f (⟨0, hn⟩, ⟨m.val + 1, by omega⟩) := by
        intro m hm
        fin_cases m
        · exact h01
        · exact h12
        · exact h23
        · exfalso; dsimp only at hm; omega
      constructor
      · rintro (rfl | ⟨hlt, hall⟩ | ⟨hlt, hall⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨hlt, fun m hm1 hm2 => (hedge m (by have := j.isLt; omega)).1 (hall m hm1 hm2)⟩)
        · exact Or.inr (Or.inr ⟨hlt, fun m hm1 hm2 => (hedge m (by have := i.isLt; omega)).1 (hall m hm1 hm2)⟩)
      · rintro (rfl | ⟨hlt, hall⟩ | ⟨hlt, hall⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨hlt, fun m hm1 hm2 => (hedge m (by have := j.isLt; omega)).2 (hall m hm1 hm2)⟩)
        · exact Or.inr (Or.inr ⟨hlt, fun m hm1 hm2 => (hedge m (by have := i.isLt; omega)).2 (hall m hm1 hm2)⟩)
    · intro v hv; cases v <;> simp [State.closed] at hv
    · intro v _ c hc _
      have hc0 : c.1 = ⟨0, hn⟩ := Fin.ext (Nat.eq_zero_of_le_zero hc)
      exact ⟨c.2, by rcases c with ⟨ci, cj⟩; subst hc0; exact .refl⟩

private lemma step_PrefixOk {n : ℕ} (f : Cell n → Fin 4) {k : ℕ} (hk1 : k + 1 < n)
    {s t : State} (hs : PrefixOk k (by omega) f s)
    (hstep : step s (rowOf f ⟨k + 1, hk1⟩) = some t) :
    PrefixOk (k + 1) hk1 f t := by
  have hk : k < n := by omega
  let nr := rowOf f ⟨k + 1, hk1⟩
  have hrow_s : rowOf f ⟨k, hk⟩ = ⟨s.r0, s.r1, s.r2, s.r3⟩ := hs.rowMatch
  have hr_eq : ∀ j : Fin 4, s.row j = C4.ofFin (f (⟨k, hk⟩, j)) := fun j => by
    have h1 := congrArg (fun r => r.get j) hrow_s
    rw [rowOf_get] at h1
    fin_cases j <;> simpa [State.row, Row.get] using h1.symm
  have hnr_eq : ∀ j : Fin 4, nr.get j = C4.ofFin (f (⟨k + 1, hk1⟩, j)) := fun j => rowOf_get f ⟨k + 1, hk1⟩ j
  -- Unpack step s nr = some t cleanly
  change step s nr = some t at hstep
  unfold step at hstep
  by_cases hcl0 : (s.closed nr.c0 || !okAdd s.d1 (s.r1.eqb nr.c0)) = true
  · simp [hcl0] at hstep
  rw [if_neg hcl0] at hstep
  by_cases hcl1 : (s.closed nr.c1 || !okAdd s.d2 (s.r2.eqb nr.c1)) = true
  · simp [hcl1] at hstep
  rw [if_neg hcl1] at hstep
  by_cases hcl2 : (s.closed nr.c2 || !okAdd s.d3 (s.r3.eqb nr.c2)) = true
  · simp [hcl2] at hstep
  rw [if_neg hcl2] at hstep
  dsimp only at hstep
  cases hd1 : deg3 (s.r2.eqb nr.c1) (nr.c0.eqb nr.c1) (nr.c1.eqb nr.c2) with
  | none => simp [hd1] at hstep
  | some nd1 =>
    rw [hd1] at hstep; dsimp only at hstep
    by_cases hcl3 : s.closed nr.c3 = true
    · simp [hcl3] at hstep
    rw [if_neg hcl3] at hstep
    cases hd2 : deg3 (s.r3.eqb nr.c2) (nr.c1.eqb nr.c2) (nr.c2.eqb nr.c3) with
    | none => simp [hd2] at hstep
    | some nd2 =>
      rw [hd2] at hstep; dsimp only at hstep
      by_cases hd23 : ((inRow s.r0 s.r1 s.r2 s.r3 .a2 && !inRow nr.c0 nr.c1 nr.c2 nr.c3 .a2) ||
          (inRow s.r0 s.r1 s.r2 s.r3 .a3 && !inRow nr.c0 nr.c1 nr.c2 nr.c3 .a3)) = true
      · simp [hd23] at hstep
      rw [if_neg hd23] at hstep
      by_cases hd01 : (((inRow s.r0 s.r1 s.r2 s.r3 .a0 && !inRow nr.c0 nr.c1 nr.c2 nr.c3 .a0) && !sameComp s .a0) ||
          ((inRow s.r0 s.r1 s.r2 s.r3 .a1 && !inRow nr.c0 nr.c1 nr.c2 nr.c3 .a1) && !sameComp s .a1)) = true
      · simp [hd01] at hstep
      rw [if_neg hd01] at hstep
      by_cases hsurv : (!((!inRow nr.c0 nr.c1 nr.c2 nr.c3 s.r0 || (stepComp s nr).c0.eqb (stepComp s nr).c4 ||
            (stepComp s nr).c0.eqb (stepComp s nr).c5 || (stepComp s nr).c0.eqb (stepComp s nr).c6 ||
            (stepComp s nr).c0.eqb (stepComp s nr).c7) &&
          (!inRow nr.c0 nr.c1 nr.c2 nr.c3 s.r1 || (stepComp s nr).c1.eqb (stepComp s nr).c4 ||
            (stepComp s nr).c1.eqb (stepComp s nr).c5 || (stepComp s nr).c1.eqb (stepComp s nr).c6 ||
            (stepComp s nr).c1.eqb (stepComp s nr).c7) &&
          (!inRow nr.c0 nr.c1 nr.c2 nr.c3 s.r2 || (stepComp s nr).c2.eqb (stepComp s nr).c4 ||
            (stepComp s nr).c2.eqb (stepComp s nr).c5 || (stepComp s nr).c2.eqb (stepComp s nr).c6 ||
            (stepComp s nr).c2.eqb (stepComp s nr).c7) &&
          (!inRow nr.c0 nr.c1 nr.c2 nr.c3 s.r3 || (stepComp s nr).c3.eqb (stepComp s nr).c4 ||
            (stepComp s nr).c3.eqb (stepComp s nr).c5 || (stepComp s nr).c3.eqb (stepComp s nr).c6 ||
            (stepComp s nr).c3.eqb (stepComp s nr).c7))) = true
      · simp [hsurv] at hstep
      rw [if_neg hsurv] at hstep
      cases hstep
      -- Extract all boolean facts cleanly
      have h_not_cl : ∀ j : Fin 4, s.closed (nr.get j) = false := fun j => by
        fin_cases j
        · change s.closed nr.c0 = false; cases h : s.closed nr.c0 <;> simp_all
        · change s.closed nr.c1 = false; cases h : s.closed nr.c1 <;> simp_all
        · change s.closed nr.c2 = false; cases h : s.closed nr.c2 <;> simp_all
        · change s.closed nr.c3 = false; cases h : s.closed nr.c3 <;> simp_all
      have h_ok1 : okAdd s.d1 (s.r1.eqb nr.c0) = true := by
        cases h : okAdd s.d1 (s.r1.eqb nr.c0) <;> simp_all
      have h_ok2 : okAdd s.d2 (s.r2.eqb nr.c1) = true := by
        cases h : okAdd s.d2 (s.r2.eqb nr.c1) <;> simp_all
      have h_ok3 : okAdd s.d3 (s.r3.eqb nr.c2) = true := by
        cases h : okAdd s.d3 (s.r3.eqb nr.c2) <;> simp_all
      have hpd := prefixDeg_succ_eval f hk1
      have hvd := vDown_eval f hk1
      have hr1 : (rowOf f ⟨k, hk⟩).c1 = s.r1 := congrArg Row.c1 hrow_s
      have hr2 : (rowOf f ⟨k, hk⟩).c2 = s.r2 := congrArg Row.c2 hrow_s
      have hr3 : (rowOf f ⟨k, hk⟩).c3 = s.r3 := congrArg Row.c3 hrow_s
      have hnd1_eq : nd1.toNat = prefixDeg f ⟨k + 1, hk1⟩ 1 := by
        rw [(deg3_iff _ _ _ _).1 hd1, hpd.2.1, hr2]
      have hnd2_eq : nd2.toNat = prefixDeg f ⟨k + 1, hk1⟩ 2 := by
        rw [(deg3_iff _ _ _ _).1 hd2, hpd.2.2.1, hr3]
      have hnd3_eq : (if nr.c2.eqb nr.c3 then D3.d1 else D3.d0).toNat = prefixDeg f ⟨k + 1, hk1⟩ 3 := by
        rw [hpd.2.2.2]; split_ifs <;> rfl
      have hcomp8 := stepComp_iff_reach f hk1 s hrow_s hs.compMatch
      have hcanon := canon4_iff (stepComp s nr).c4 (stepComp s nr).c5 (stepComp s nr).c6 (stepComp s nr).c7
      -- Build PrefixOk (k + 1)
      refine ⟨rfl, ?_, ?_, hnd1_eq.symm, hnd2_eq.symm, hnd3_eq.symm, ?_, ?_, ?_⟩
      · -- degPrefix
        intro i j hi
        by_cases hik : i.val ≤ k
        · exact hs.degPrefix i j hik
        · have hi_eq : i = ⟨k + 1, hk1⟩ := Fin.ext (show i.val = k + 1 by omega)
          subst hi_eq
          fin_cases j
          · change prefixDeg f ⟨k + 1, hk1⟩ 0 ≤ 2; rw [hpd.1]; split_ifs <;> omega
          · change prefixDeg f ⟨k + 1, hk1⟩ 1 ≤ 2; rw [← hnd1_eq]; cases nd1 <;> decide
          · change prefixDeg f ⟨k + 1, hk1⟩ 2 ≤ 2; rw [← hnd2_eq]; cases nd2 <;> decide
          · change prefixDeg f ⟨k + 1, hk1⟩ 3 ≤ 2; rw [hpd.2.2.2]; split_ifs <;> omega
      · -- degFull
        intro i j hi
        by_cases hik : i.val < k
        · exact hs.degFull i j hik
        · have hi_eq : i = ⟨k, hk⟩ := Fin.ext (show i.val = k by omega)
          subst hi_eq
          rw [neighborSame_eq]
          fin_cases j
          · change prefixDeg f ⟨k, hk⟩ 0 + vDown f ⟨k, hk⟩ 0 ≤ 2
            rw [hvd.1, add_zero]; exact hs.degPrefix ⟨k, hk⟩ 0 le_rfl
          · change prefixDeg f ⟨k, hk⟩ 1 + vDown f ⟨k, hk⟩ 1 ≤ 2
            rw [hs.deg1, hvd.2.1, hr1]; exact (okAdd_iff _ _).1 h_ok1
          · change prefixDeg f ⟨k, hk⟩ 2 + vDown f ⟨k, hk⟩ 2 ≤ 2
            rw [hs.deg2, hvd.2.2.1, hr2]; exact (okAdd_iff _ _).1 h_ok2
          · change prefixDeg f ⟨k, hk⟩ 3 + vDown f ⟨k, hk⟩ 3 ≤ 2
            rw [hs.deg3, hvd.2.2.2, hr3]; exact (okAdd_iff _ _).1 h_ok3
      · -- compMatch
        intro i j
        have hc := hcanon i j
        have he : ∀ l : Fin 4,
            (match l with
             | ⟨0, _⟩ => (stepComp s nr).c4 | ⟨1, _⟩ => (stepComp s nr).c5
             | ⟨2, _⟩ => (stepComp s nr).c6 | ⟨3, _⟩ => (stepComp s nr).c7) =
            (stepComp s nr).get (embHigh l) := fun l => by fin_cases l <;> rfl
        have hcomp_eq : ∀ l : Fin 4,
            (match l with
             | ⟨0, _⟩ => (canon4 (stepComp s nr).c4 (stepComp s nr).c5 (stepComp s nr).c6 (stepComp s nr).c7).1
             | ⟨1, _⟩ => (canon4 (stepComp s nr).c4 (stepComp s nr).c5 (stepComp s nr).c6 (stepComp s nr).c7).2.1
             | ⟨2, _⟩ => (canon4 (stepComp s nr).c4 (stepComp s nr).c5 (stepComp s nr).c6 (stepComp s nr).c7).2.2.1
             | ⟨3, _⟩ => (canon4 (stepComp s nr).c4 (stepComp s nr).c5 (stepComp s nr).c6 (stepComp s nr).c7).2.2.2) =
            State.comp ⟨nr.c0, nr.c1, nr.c2, nr.c3, nd1, nd2, if nr.c2.eqb nr.c3 then D3.d1 else D3.d0,
              (canon4 (stepComp s nr).c4 (stepComp s nr).c5 (stepComp s nr).c6 (stepComp s nr).c7).1,
              (canon4 (stepComp s nr).c4 (stepComp s nr).c5 (stepComp s nr).c6 (stepComp s nr).c7).2.1,
              (canon4 (stepComp s nr).c4 (stepComp s nr).c5 (stepComp s nr).c6 (stepComp s nr).c7).2.2.1,
              (canon4 (stepComp s nr).c4 (stepComp s nr).c5 (stepComp s nr).c6 (stepComp s nr).c7).2.2.2,
              s.cl0 || (inRow s.r0 s.r1 s.r2 s.r3 .a0 && !inRow nr.c0 nr.c1 nr.c2 nr.c3 .a0),
              s.cl1 || (inRow s.r0 s.r1 s.r2 s.r3 .a1 && !inRow nr.c0 nr.c1 nr.c2 nr.c3 .a1)⟩ l := fun l => by
          fin_cases l <;> rfl
        rw [← hcomp_eq i, ← hcomp_eq j]
        dsimp only [canon4] at hc ⊢
        rw [hc, he i, he j, hcomp8, emb_embHigh, emb_embHigh]
      · -- closedTrue
        intro v hv
        have hcase : s.closed v = true ∨
            (s.closed v = false ∧ (v = .a0 ∨ v = .a1) ∧
              inRow s.r0 s.r1 s.r2 s.r3 v = true ∧ inRow nr.c0 nr.c1 nr.c2 nr.c3 v = false) := by
          cases v
          · simp only [State.closed, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hv
            rcases hv with h | ⟨h1, h2⟩
            · exact Or.inl h
            · cases hcl : s.cl0
              · exact Or.inr ⟨hcl, Or.inl rfl, h1, h2⟩
              · exact Or.inl hcl
          · simp only [State.closed, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hv
            rcases hv with h | ⟨h1, h2⟩
            · exact Or.inl h
            · cases hcl : s.cl1
              · exact Or.inr ⟨hcl, Or.inr rfl, h1, h2⟩
              · exact Or.inl hcl
          · simp [State.closed] at hv
          · simp [State.closed] at hv
        rcases hcase with hwas | ⟨hnot, hv01, hold, hnew⟩
        · obtain ⟨_, ⟨c0, hc0le, hc0f⟩, hconn⟩ := hs.closedTrue v hwas
          have hno_nr : ∀ j : Fin 4, f (⟨k + 1, hk1⟩, j) ≠ v.toFin := fun j hj => by
            have hnj : nr.get j = v := by rw [hnr_eq, hj, C4.ofFin_toFin]
            have hcl := h_not_cl j
            rw [hnj, hwas] at hcl; cases hcl
          refine ⟨hno_nr, ⟨c0, Nat.le_succ_of_le hc0le, hc0f⟩, fun c d hc hd hfc hfd => ?_⟩
          have hc_le : c.1.val ≤ k := by
            by_contra hgt
            have heq : c.1 = ⟨k + 1, hk1⟩ := Fin.ext (show c.1.val = k + 1 by omega)
            exact hno_nr c.2 (by rcases c with ⟨ci, cj⟩; subst heq; exact hfc)
          have hd_le : d.1.val ≤ k := by
            by_contra hgt
            have heq : d.1 = ⟨k + 1, hk1⟩ := Fin.ext (show d.1.val = k + 1 by omega)
            exact hno_nr d.2 (by rcases d with ⟨di, dj⟩; subst heq; exact hfd)
          exact Reach_mono (Nat.le_succ k) (hconn c d hc_le hd_le hfc hfd)
        · have hno_nr : ∀ j : Fin 4, f (⟨k + 1, hk1⟩, j) ≠ v.toFin := fun j hj => by
            have hnj : nr.get j = v := by rw [hnr_eq, hj, C4.ofFin_toFin]
            have hmem : inRow nr.c0 nr.c1 nr.c2 nr.c3 v = true := (inRow_iff nr v).2 ⟨j, hnj⟩
            rw [hnew] at hmem; cases hmem
          obtain ⟨j0, hj0⟩ := (inRow_state_iff s v).1 hold
          have hf_j0 : f (⟨k, hk⟩, j0) = v.toFin := by
            have := hr_eq j0; rw [hj0] at this; exact (C4.toFin_ofFin _).symm.trans (congrArg C4.toFin this.symm)
          have hsc : sameComp s v = true := by
            rcases hv01 with rfl | rfl
            · cases h : sameComp s .a0 <;> simp_all
            · cases h : sameComp s .a1 <;> simp_all
          refine ⟨hno_nr, ⟨(⟨k, hk⟩, j0), Nat.le_succ k, hf_j0⟩, fun c d hc hd hfc hfd => ?_⟩
          have hc_le : c.1.val ≤ k := by
            by_contra hgt
            have heq : c.1 = ⟨k + 1, hk1⟩ := Fin.ext (show c.1.val = k + 1 by omega)
            exact hno_nr c.2 (by rcases c with ⟨ci, cj⟩; subst heq; exact hfc)
          have hd_le : d.1.val ≤ k := by
            by_contra hgt
            have heq : d.1 = ⟨k + 1, hk1⟩ := Fin.ext (show d.1.val = k + 1 by omega)
            exact hno_nr d.2 (by rcases d with ⟨di, dj⟩; subst heq; exact hfd)
          obtain ⟨jc, hjc⟩ := hs.closedFalse v hnot c hc_le hfc
          obtain ⟨jd, hjd⟩ := hs.closedFalse v hnot d hd_le hfd
          have hsjc : s.row jc = v := by
            rw [hr_eq, ← Reach_color hjc, hfc, C4.ofFin_toFin]
          have hsjd : s.row jd = v := by
            rw [hr_eq, ← Reach_color hjd, hfd, C4.ofFin_toFin]
          have hcomp_eq : s.comp jc = s.comp jd := (sameComp_iff s v).1 hsc jc jd hsjc hsjd
          have hmid : Reach f k (⟨k, hk⟩, jc) (⟨k, hk⟩, jd) := (hs.compMatch jc jd).1 hcomp_eq
          exact Reach_mono (Nat.le_succ k) (Reach_trans hjc (Reach_trans hmid (Reach_symm hjd)))
      · -- closedFalse
        intro v hv c hc hfc
        by_cases hc_eq : c.1.val = k + 1
        · have hc1 : c.1 = ⟨k + 1, hk1⟩ := Fin.ext hc_eq
          exact ⟨c.2, by rcases c with ⟨ci, cj⟩; subst hc1; exact .refl⟩
        · have hc_le : c.1.val ≤ k := by omega
          have hs_not_cl : s.closed v = false := by
            cases v <;> simp only [State.closed, Bool.or_eq_false_iff] at hv ⊢
            · exact hv.1
            · exact hv.1
          obtain ⟨jc, hjc⟩ := hs.closedFalse v hs_not_cl c hc_le hfc
          have hsjc : s.row jc = v := by
            rw [hr_eq, ← Reach_color hjc, hfc, C4.ofFin_toFin]
          have hold : inRow s.r0 s.r1 s.r2 s.r3 v = true := (inRow_state_iff s v).2 ⟨jc, hsjc⟩
          have hnew : inRow nr.c0 nr.c1 nr.c2 nr.c3 v = true := by
            cases hn' : inRow nr.c0 nr.c1 nr.c2 nr.c3 v
            · exfalso
              cases v
              · simp only [State.closed, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
                  Bool.not_eq_false'] at hv
                rcases hv.2 with h1 | h2
                · rw [hold] at h1; cases h1
                · rw [hn'] at h2; cases h2
              · simp only [State.closed, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
                  Bool.not_eq_false'] at hv
                rcases hv.2 with h1 | h2
                · rw [hold] at h1; cases h1
                · rw [hn'] at h2; cases h2
              · simp [hold, hn'] at hd23
              · simp [hold, hn'] at hd23
            · rfl
          -- From hsurv, stepComp s nr at embLow jc matches one of c4..c7!
          have hsurv_pos :
              ((!inRow nr.c0 nr.c1 nr.c2 nr.c3 s.r0 || (stepComp s nr).c0.eqb (stepComp s nr).c4 ||
                (stepComp s nr).c0.eqb (stepComp s nr).c5 || (stepComp s nr).c0.eqb (stepComp s nr).c6 ||
                (stepComp s nr).c0.eqb (stepComp s nr).c7) &&
              (!inRow nr.c0 nr.c1 nr.c2 nr.c3 s.r1 || (stepComp s nr).c1.eqb (stepComp s nr).c4 ||
                (stepComp s nr).c1.eqb (stepComp s nr).c5 || (stepComp s nr).c1.eqb (stepComp s nr).c6 ||
                (stepComp s nr).c1.eqb (stepComp s nr).c7) &&
              (!inRow nr.c0 nr.c1 nr.c2 nr.c3 s.r2 || (stepComp s nr).c2.eqb (stepComp s nr).c4 ||
                (stepComp s nr).c2.eqb (stepComp s nr).c5 || (stepComp s nr).c2.eqb (stepComp s nr).c6 ||
                (stepComp s nr).c2.eqb (stepComp s nr).c7) &&
              (!inRow nr.c0 nr.c1 nr.c2 nr.c3 s.r3 || (stepComp s nr).c3.eqb (stepComp s nr).c4 ||
                (stepComp s nr).c3.eqb (stepComp s nr).c5 || (stepComp s nr).c3.eqb (stepComp s nr).c6 ||
                (stepComp s nr).c3.eqb (stepComp s nr).c7)) = true := by
            cases h : ((!inRow nr.c0 nr.c1 nr.c2 nr.c3 s.r0 || (stepComp s nr).c0.eqb (stepComp s nr).c4 ||
                (stepComp s nr).c0.eqb (stepComp s nr).c5 || (stepComp s nr).c0.eqb (stepComp s nr).c6 ||
                (stepComp s nr).c0.eqb (stepComp s nr).c7) &&
              (!inRow nr.c0 nr.c1 nr.c2 nr.c3 s.r1 || (stepComp s nr).c1.eqb (stepComp s nr).c4 ||
                (stepComp s nr).c1.eqb (stepComp s nr).c5 || (stepComp s nr).c1.eqb (stepComp s nr).c6 ||
                (stepComp s nr).c1.eqb (stepComp s nr).c7) &&
              (!inRow nr.c0 nr.c1 nr.c2 nr.c3 s.r2 || (stepComp s nr).c2.eqb (stepComp s nr).c4 ||
                (stepComp s nr).c2.eqb (stepComp s nr).c5 || (stepComp s nr).c2.eqb (stepComp s nr).c6 ||
                (stepComp s nr).c2.eqb (stepComp s nr).c7) &&
              (!inRow nr.c0 nr.c1 nr.c2 nr.c3 s.r3 || (stepComp s nr).c3.eqb (stepComp s nr).c4 ||
                (stepComp s nr).c3.eqb (stepComp s nr).c5 || (stepComp s nr).c3.eqb (stepComp s nr).c6 ||
                (stepComp s nr).c3.eqb (stepComp s nr).c7))
            · rw [h] at hsurv; exact absurd rfl hsurv
            · rfl
          have hsurv_jc : (stepComp s nr).get (embLow jc) = (stepComp s nr).c4 ∨
              (stepComp s nr).get (embLow jc) = (stepComp s nr).c5 ∨
              (stepComp s nr).get (embLow jc) = (stepComp s nr).c6 ∨
              (stepComp s nr).get (embLow jc) = (stepComp s nr).c7 := by
            simp only [Bool.and_eq_true] at hsurv_pos
            fin_cases jc
            · have h := hsurv_pos.1.1.1
              simp only [State.row] at hsjc; rw [hsjc, hnew] at h
              simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, C8.eqb_iff] at h
              rcases h with ((h | h) | h) | h <;> [exact Or.inl h; exact Or.inr (Or.inl h);
                exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr h))]
            · have h := hsurv_pos.1.1.2
              simp only [State.row] at hsjc; rw [hsjc, hnew] at h
              simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, C8.eqb_iff] at h
              rcases h with ((h | h) | h) | h <;> [exact Or.inl h; exact Or.inr (Or.inl h);
                exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr h))]
            · have h := hsurv_pos.1.2
              simp only [State.row] at hsjc; rw [hsjc, hnew] at h
              simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, C8.eqb_iff] at h
              rcases h with ((h | h) | h) | h <;> [exact Or.inl h; exact Or.inr (Or.inl h);
                exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr h))]
            · have h := hsurv_pos.2
              simp only [State.row] at hsjc; rw [hsjc, hnew] at h
              simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, C8.eqb_iff] at h
              rcases h with ((h | h) | h) | h <;> [exact Or.inl h; exact Or.inr (Or.inl h);
                exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr h))]
          rcases hsurv_jc with hm | hm | hm | hm
          · refine ⟨0, Reach_trans (Reach_mono (Nat.le_succ k) hjc) ?_⟩
            have := (hcomp8 (embLow jc) (embHigh 0)).1 hm
            rwa [emb_embLow, emb_embHigh] at this
          · refine ⟨1, Reach_trans (Reach_mono (Nat.le_succ k) hjc) ?_⟩
            have := (hcomp8 (embLow jc) (embHigh 1)).1 hm
            rwa [emb_embLow, emb_embHigh] at this
          · refine ⟨2, Reach_trans (Reach_mono (Nat.le_succ k) hjc) ?_⟩
            have := (hcomp8 (embLow jc) (embHigh 2)).1 hm
            rwa [emb_embLow, emb_embHigh] at this
          · refine ⟨3, Reach_trans (Reach_mono (Nat.le_succ k) hjc) ?_⟩
            have := (hcomp8 (embLow jc) (embHigh 3)).1 hm
            rwa [emb_embLow, emb_embHigh] at this

private lemma Valid_step_some {n : ℕ} (f : Cell n → Fin 4) (hvalid : Valid n f)
    {k : ℕ} (hk1 : k + 1 < n) {s : State} (hs : PrefixOk k (by omega) f s) :
    ∃ t, step s (rowOf f ⟨k + 1, hk1⟩) = some t := by
  rcases hvalid with ⟨hn, _, _, hf2, hf3, hconn, hdeg⟩
  have hk : k < n := by omega
  let nr := rowOf f ⟨k + 1, hk1⟩
  have hrow_s : rowOf f ⟨k, hk⟩ = ⟨s.r0, s.r1, s.r2, s.r3⟩ := hs.rowMatch
  have hr_eq : ∀ j : Fin 4, s.row j = C4.ofFin (f (⟨k, hk⟩, j)) := fun j => by
    have h1 := congrArg (fun r => r.get j) hrow_s
    rw [rowOf_get] at h1
    fin_cases j <;> simpa [State.row, Row.get] using h1.symm
  have hnr_eq : ∀ j : Fin 4, nr.get j = C4.ofFin (f (⟨k + 1, hk1⟩, j)) := fun j => rowOf_get f ⟨k + 1, hk1⟩ j
  -- 1. No closed color can appear in nr
  have h_not_cl : ∀ j : Fin 4, s.closed (nr.get j) = false := by
    intro j
    cases hcl : s.closed (nr.get j)
    · rfl
    · exfalso
      obtain ⟨hno_k, ⟨c0, hc0le, hc0f⟩, _⟩ := hs.closedTrue (nr.get j) hcl
      have hf_j : f (⟨k + 1, hk1⟩, j) = (nr.get j).toFin := by rw [hnr_eq, C4.toFin_ofFin]
      have hpath := hconn (nr.get j).toFin c0 (⟨k + 1, hk1⟩, j) hc0f hf_j
      obtain ⟨_, l, _, hl, _, _⟩ := border_crossing hk hpath hc0le (by dsimp; omega)
      exact hno_k l ((Reach_color hl).symm.trans hc0f)
  -- 2. Degree checks pass
  have hpd := prefixDeg_succ_eval f hk1
  have hvd := vDown_eval f hk1
  have hr1 : (rowOf f ⟨k, hk⟩).c1 = s.r1 := congrArg Row.c1 hrow_s
  have hr2 : (rowOf f ⟨k, hk⟩).c2 = s.r2 := congrArg Row.c2 hrow_s
  have hr3 : (rowOf f ⟨k, hk⟩).c3 = s.r3 := congrArg Row.c3 hrow_s
  have h_ok1 : okAdd s.d1 (s.r1.eqb nr.c0) = true := by
    rw [okAdd_iff, ← hs.deg1, ← hr1, ← hvd.2.1, ← neighborSame_eq]; exact hdeg (⟨k, hk⟩, 1)
  have h_ok2 : okAdd s.d2 (s.r2.eqb nr.c1) = true := by
    rw [okAdd_iff, ← hs.deg2, ← hr2, ← hvd.2.2.1, ← neighborSame_eq]; exact hdeg (⟨k, hk⟩, 2)
  have h_ok3 : okAdd s.d3 (s.r3.eqb nr.c2) = true := by
    rw [okAdd_iff, ← hs.deg3, ← hr3, ← hvd.2.2.2, ← neighborSame_eq]; exact hdeg (⟨k, hk⟩, 3)
  have hnd1_le : (if s.r2.eqb nr.c1 then 1 else 0) + (if nr.c0.eqb nr.c1 then 1 else 0) +
      (if nr.c1.eqb nr.c2 then 1 else 0) ≤ 2 := by
    have h1 := hdeg (⟨k + 1, hk1⟩, 1)
    rw [neighborSame_eq, hpd.2.1, hr2] at h1
    change (if s.r2.eqb nr.c1 then 1 else 0) + (if nr.c0.eqb nr.c1 then 1 else 0) +
        (if nr.c1.eqb nr.c2 then 1 else 0) + vDown f ⟨k + 1, hk1⟩ 1 ≤ 2 at h1
    omega
  have hnd2_le : (if s.r3.eqb nr.c2 then 1 else 0) + (if nr.c1.eqb nr.c2 then 1 else 0) +
      (if nr.c2.eqb nr.c3 then 1 else 0) ≤ 2 := by
    have h1 := hdeg (⟨k + 1, hk1⟩, 2)
    rw [neighborSame_eq, hpd.2.2.1, hr3] at h1
    change (if s.r3.eqb nr.c2 then 1 else 0) + (if nr.c1.eqb nr.c2 then 1 else 0) +
        (if nr.c2.eqb nr.c3 then 1 else 0) + vDown f ⟨k + 1, hk1⟩ 2 ≤ 2 at h1
    omega
  -- 3. Colors 2 and 3 cannot die
  have h_no_die_23 : ∀ v : C4, (v = .a2 ∨ v = .a3) →
      inRow s.r0 s.r1 s.r2 s.r3 v = true → inRow nr.c0 nr.c1 nr.c2 nr.c3 v = true := by
    intro v hv hold
    obtain ⟨j0, hj0⟩ := (inRow_state_iff s v).1 hold
    have hf_j0 : f (⟨k, hk⟩, j0) = v.toFin := by
      have := hr_eq j0; rw [hj0] at this; exact (C4.toFin_ofFin _).symm.trans (congrArg C4.toFin this.symm)
    have ⟨jend, hf_end⟩ : ∃ jend : Fin 4, f (⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩, jend) = v.toFin := by
      rcases hv with rfl | rfl
      · exact ⟨0, hf2⟩
      · exact ⟨3, hf3⟩
    by_cases hlast : k + 1 = n - 1
    · have heq : (⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩ : Fin n) = ⟨k + 1, hk1⟩ := Fin.ext hlast.symm
      rw [heq] at hf_end
      exact (inRow_iff nr v).2 ⟨jend, by rw [hnr_eq, hf_end, C4.ofFin_toFin]⟩
    · have hpath := hconn v.toFin (⟨k, hk⟩, j0) (⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩, jend) hf_j0 hf_end
      obtain ⟨_, _, j', hl, hadj, _⟩ := border_crossing hk hpath le_rfl (by dsimp; omega)
      have hf_j' : f (⟨k + 1, hk1⟩, j') = v.toFin := hadj.2.symm.trans ((Reach_color hl).symm.trans hf_j0)
      exact (inRow_iff nr v).2 ⟨j', by rw [hnr_eq, hf_j', C4.ofFin_toFin]⟩
  -- 4. If color v dies (in old, not in new), all its cells in row k have same comp
  have h_die_comp : ∀ v : C4,
      inRow s.r0 s.r1 s.r2 s.r3 v = true → inRow nr.c0 nr.c1 nr.c2 nr.c3 v = false →
      sameComp s v = true := by
    intro v _ hnew
    rw [sameComp_iff]
    intro i j hi hj
    rw [hs.compMatch]
    have hfi : f (⟨k, hk⟩, i) = v.toFin := by
      have := hr_eq i; rw [hi] at this; exact (C4.toFin_ofFin _).symm.trans (congrArg C4.toFin this.symm)
    have hfj : f (⟨k, hk⟩, j) = v.toFin := by
      have := hr_eq j; rw [hj] at this; exact (C4.toFin_ofFin _).symm.trans (congrArg C4.toFin this.symm)
    have hpath := hconn v.toFin (⟨k, hk⟩, i) (⟨k, hk⟩, j) hfi hfj
    rcases path_dichotomy hk le_rfl hpath with hreach | ⟨_, _, j', hl, hadj, _⟩
    · exact hreach
    · exfalso
      have hf_j' : f (⟨k + 1, hk1⟩, j') = v.toFin := hadj.2.symm.trans ((Reach_color hl).symm.trans hfi)
      have hmem : inRow nr.c0 nr.c1 nr.c2 nr.c3 v = true :=
        (inRow_iff nr v).2 ⟨j', by rw [hnr_eq, hf_j', C4.ofFin_toFin]⟩
      rw [hnew] at hmem; cases hmem
  -- 5. Surviving cells in row k must reach some cell in row k+1
  have hcomp8 := stepComp_iff_reach f hk1 s hrow_s hs.compMatch
  have h_surv : ∀ j : Fin 4,
      inRow nr.c0 nr.c1 nr.c2 nr.c3 (s.row j) = true →
      (stepComp s nr).get (embLow j) = (stepComp s nr).c4 ∨
      (stepComp s nr).get (embLow j) = (stepComp s nr).c5 ∨
      (stepComp s nr).get (embLow j) = (stepComp s nr).c6 ∨
      (stepComp s nr).get (embLow j) = (stepComp s nr).c7 := by
    intro j hnew
    obtain ⟨j', hj'⟩ := (inRow_iff nr (s.row j)).1 hnew
    have hfj : f (⟨k, hk⟩, j) = (s.row j).toFin := by
      have := hr_eq j; exact (C4.toFin_ofFin _).symm.trans (congrArg C4.toFin this.symm)
    have hfj' : f (⟨k + 1, hk1⟩, j') = (s.row j).toFin := by
      have := hnr_eq j'; rw [hj'] at this; exact (C4.toFin_ofFin _).symm.trans (congrArg C4.toFin this.symm)
    have hpath := hconn (s.row j).toFin (⟨k, hk⟩, j) (⟨k + 1, hk1⟩, j') hfj hfj'
    by_contra hnot
    push Not at hnot
    have htrap : ∀ l : Fin 4, ¬ Reach f (k + 1) (⟨k, hk⟩, j) (⟨k + 1, hk1⟩, l) := by
      intro l hl
      have heq := (hcomp8 (embLow j) (embHigh l)).2 (by rwa [emb_embLow, emb_embHigh])
      fin_cases l
      · exact hnot.1 heq
      · exact hnot.2.1 heq
      · exact hnot.2.2.1 heq
      · exact hnot.2.2.2 heq
    have hreach := trapped_reach hk1 (by dsimp; omega) htrap hpath
    exact htrap j' hreach
  -- Combine all 5 into step s nr = some _
  change ∃ t, step s nr = some t
  unfold step
  have hcl0 : (s.closed nr.c0 || !okAdd s.d1 (s.r1.eqb nr.c0)) = false := by
    have := h_not_cl 0; simp [Row.get] at this; simp [this, h_ok1]
  have hcl1 : (s.closed nr.c1 || !okAdd s.d2 (s.r2.eqb nr.c1)) = false := by
    have := h_not_cl 1; simp [Row.get] at this; simp [this, h_ok2]
  have hcl2 : (s.closed nr.c2 || !okAdd s.d3 (s.r3.eqb nr.c2)) = false := by
    have := h_not_cl 2; simp [Row.get] at this; simp [this, h_ok3]
  have hcl3 : s.closed nr.c3 = false := by have := h_not_cl 3; simpa [Row.get] using this
  simp only [hcl0, hcl1, hcl2, hcl3, Bool.false_eq_true, ite_false]
  cases hd1 : deg3 (s.r2.eqb nr.c1) (nr.c0.eqb nr.c1) (nr.c1.eqb nr.c2) with
  | none =>
    have := (deg3_none_iff _ _ _).1 hd1; omega
  | some nd1 =>
    cases hd2 : deg3 (s.r3.eqb nr.c2) (nr.c1.eqb nr.c2) (nr.c2.eqb nr.c3) with
    | none =>
      have := (deg3_none_iff _ _ _).1 hd2; omega
    | some nd2 =>
      dsimp only
      have hd2_f : (inRow s.r0 s.r1 s.r2 s.r3 .a2 && !inRow nr.c0 nr.c1 nr.c2 nr.c3 .a2) = false := by
        cases h1 : inRow s.r0 s.r1 s.r2 s.r3 .a2
        · rfl
        · simp [h_no_die_23 .a2 (Or.inl rfl) h1]
      have hd3_f : (inRow s.r0 s.r1 s.r2 s.r3 .a3 && !inRow nr.c0 nr.c1 nr.c2 nr.c3 .a3) = false := by
        cases h1 : inRow s.r0 s.r1 s.r2 s.r3 .a3
        · rfl
        · simp [h_no_die_23 .a3 (Or.inr rfl) h1]
      have hd0_ok : ((inRow s.r0 s.r1 s.r2 s.r3 .a0 && !inRow nr.c0 nr.c1 nr.c2 nr.c3 .a0) && !sameComp s .a0) = false := by
        cases h1 : inRow s.r0 s.r1 s.r2 s.r3 .a0
        · rfl
        · cases h2 : inRow nr.c0 nr.c1 nr.c2 nr.c3 .a0
          · simp [h_die_comp .a0 h1 h2]
          · rfl
      have hd1_ok : ((inRow s.r0 s.r1 s.r2 s.r3 .a1 && !inRow nr.c0 nr.c1 nr.c2 nr.c3 .a1) && !sameComp s .a1) = false := by
        cases h1 : inRow s.r0 s.r1 s.r2 s.r3 .a1
        · rfl
        · cases h2 : inRow nr.c0 nr.c1 nr.c2 nr.c3 .a1
          · simp [h_die_comp .a1 h1 h2]
          · rfl
      have hsurv_ok : ∀ j : Fin 4,
          (!inRow nr.c0 nr.c1 nr.c2 nr.c3 (s.row j) ||
            ((stepComp s nr).get (embLow j)).eqb (stepComp s nr).c4 ||
            ((stepComp s nr).get (embLow j)).eqb (stepComp s nr).c5 ||
            ((stepComp s nr).get (embLow j)).eqb (stepComp s nr).c6 ||
            ((stepComp s nr).get (embLow j)).eqb (stepComp s nr).c7) = true := by
        intro j
        cases hnew : inRow nr.c0 nr.c1 nr.c2 nr.c3 (s.row j)
        · simp
        · rcases h_surv j hnew with h | h | h | h <;>
            simp [C8.eqb_iff, h]
      have hs0 := hsurv_ok 0; have hs1 := hsurv_ok 1; have hs2 := hsurv_ok 2; have hs3 := hsurv_ok 3
      simp only [State.row, embLow, Comp8.get] at hs0 hs1 hs2 hs3
      simp only [hd2_f, hd3_f, hd0_ok, hd1_ok, Bool.or_self, Bool.false_eq_true, ite_false]
      simp only [hs0, hs1, hs2, hs3, Bool.and_self, Bool.not_true, Bool.false_eq_true, ite_false]
      exact ⟨_, rfl⟩

private lemma final_iff_Valid {n : ℕ} (f : Cell n → Fin 4) (hn : 0 < n) {s : State}
    (hs : PrefixOk (n - 1) (Nat.sub_lt hn (Nat.succ_pos 0)) f s)
    (hf0 : f (⟨0, hn⟩, 0) = 0) (hf1 : f (⟨0, hn⟩, 3) = 1) :
    isFinal s = true ↔ Valid n f := by
  have hlast : n - 1 < n := Nat.sub_lt hn (Nat.succ_pos 0)
  have hr_eq : ∀ j : Fin 4, s.row j = C4.ofFin (f (⟨n - 1, hlast⟩, j)) := fun j => by
    have h1 := congrArg (fun r => r.get j) hs.rowMatch
    rw [rowOf_get] at h1
    fin_cases j <;> simpa [State.row, Row.get] using h1.symm
  rw [isFinal_iff]
  constructor
  · rintro ⟨h2, h3, hcomp_fin⟩
    refine ⟨hn, hf0, hf1, ?_, ?_, ?_, ?_⟩
    · have := hr_eq 0; simp only [State.row] at this; rw [h2] at this
      exact (C4.toFin_ofFin _).symm.trans (congrArg C4.toFin this.symm)
    · have := hr_eq 3; simp only [State.row] at this; rw [h3] at this
      exact (C4.toFin_ofFin _).symm.trans (congrArg C4.toFin this.symm)
    · intro v c d hfc hfd
      rw [← Reach_full_iff hn]
      let cv := C4.ofFin v
      have hcv : cv.toFin = v := C4.toFin_ofFin v
      cases hcl : s.closed cv
      · obtain ⟨ic, hic⟩ := hs.closedFalse cv hcl c (by omega) (hfc.trans hcv.symm)
        obtain ⟨id_, hid⟩ := hs.closedFalse cv hcl d (by omega) (hfd.trans hcv.symm)
        have hric : s.row ic = cv := by rw [hr_eq, ← Reach_color hic, hfc]
        have hrid : s.row id_ = cv := by rw [hr_eq, ← Reach_color hid, hfd]
        have hmid : Reach f (n - 1) (⟨n - 1, hlast⟩, ic) (⟨n - 1, hlast⟩, id_) :=
          (hs.compMatch ic id_).1 (hcomp_fin ic id_ (hric.trans hrid.symm))
        exact Reach_trans hic (Reach_trans hmid (Reach_symm hid))
      · exact (hs.closedTrue cv hcl).2.2 c d (by omega) (by omega) (hfc.trans hcv.symm) (hfd.trans hcv.symm)
    · intro ⟨i, j⟩
      by_cases hi : i.val < n - 1
      · exact hs.degFull i j hi
      · rw [neighborSame_eq]
        have hvd0 : vDown f i j = 0 := by
          unfold vDown
          rw [dif_neg (by intro h; omega)]
        rw [hvd0, add_zero]
        exact hs.degPrefix i j (by omega)
  · rintro ⟨_, _, _, hf2, hf3, hconn, _⟩
    change f (⟨n - 1, hlast⟩, 0) = 2 at hf2
    change f (⟨n - 1, hlast⟩, 3) = 3 at hf3
    refine ⟨?_, ?_, ?_⟩
    · have := hr_eq 0; simp only [State.row] at this; rw [this, hf2]; rfl
    · have := hr_eq 3; simp only [State.row] at this; rw [this, hf3]; rfl
    · intro i j hij
      rw [hs.compMatch, Reach_full_iff hn]
      have hfeq : f (⟨n - 1, hlast⟩, i) = f (⟨n - 1, hlast⟩, j) := by
        have hi := hr_eq i; have hj := hr_eq j
        exact C4.ofFin_injective (hi.symm.trans (hij.trans hj))
      exact hconn (f (⟨n - 1, hlast⟩, i)) _ _ rfl hfeq.symm

/-! ### Connecting runFrom / runBoard to PrefixOk and ways -/

private lemma runFrom_PrefixOk {n : ℕ} (f : Cell n → Fin 4) (m : ℕ) :
    ∀ (k : ℕ) (hkm : k + m < n) (s : State),
      PrefixOk k (by omega) f s →
      (∀ t, runFrom m s (fun i : Fin m => rowOf f ⟨k + 1 + i.val, by omega⟩) = some t →
        PrefixOk (k + m) hkm f t) ∧
      (Valid n f → ∃ t, runFrom m s (fun i : Fin m => rowOf f ⟨k + 1 + i.val, by omega⟩) = some t) := by
  induction m with
  | zero =>
    intro k hkm s hs
    exact ⟨fun t ht => by cases ht; exact hs, fun _ => ⟨s, rfl⟩⟩
  | succ m ih =>
    intro k hkm s hs
    have hk1 : k + 1 < n := by omega
    constructor
    · intro t ht
      unfold runFrom at ht
      simp only [Fin.val_zero, add_zero] at ht
      cases hst : step s (rowOf f ⟨k + 1, hk1⟩) with
      | none => rw [hst] at ht; cases ht
      | some s1 =>
        rw [hst] at ht; dsimp only at ht
        have hs1 := step_PrefixOk f hk1 hs hst
        have hkm' : k + 1 + m < n := by omega
        have hres := (ih (k + 1) hkm' s1 hs1).1 t
        have hfun : (fun i : Fin m => rowOf f ⟨k + 1 + 1 + i.val, by omega⟩) =
            (fun i : Fin m => rowOf f ⟨k + 1 + i.succ.val, by omega⟩) := by
          funext i; congr 1; ext; dsimp; omega
        rw [hfun] at hres
        have hpok := hres ht
        simpa only [Nat.add_assoc, Nat.add_comm 1 m] using hpok
    · intro hv
      obtain ⟨s1, hs1⟩ := Valid_step_some f hv hk1 hs
      have hpok1 := step_PrefixOk f hk1 hs hs1
      have hkm' : k + 1 + m < n := by omega
      obtain ⟨t, ht⟩ := (ih (k + 1) hkm' s1 hpok1).2 hv
      refine ⟨t, ?_⟩
      unfold runFrom
      simp only [Fin.val_zero, add_zero, hs1]
      have hfun : (fun i : Fin m => rowOf f ⟨k + 1 + 1 + i.val, by omega⟩) =
          (fun i : Fin m => rowOf f ⟨k + 1 + i.succ.val, by omega⟩) := by
        funext i; congr 1; ext; dsimp; omega
      rwa [← hfun]

private lemma runBoard_iff_Valid (k : ℕ) (f : Cell (k + 1) → Fin 4) :
    Valid (k + 1) f ↔ ∃ t, runBoard k (boardEquiv (k + 1) f) = some t ∧ isFinal t = true := by
  have hn : 0 < k + 1 := Nat.succ_pos k
  constructor
  · intro hv
    have ⟨_, hf0, hf1, _, _, _, _⟩ := hv
    have hf0' : f (⟨0, hn⟩, 0) = 0 := hf0
    have hf1' : f (⟨0, hn⟩, 3) = 1 := hf1
    have hinit_some : ∃ s0, initState (rowOf f ⟨0, hn⟩) = some s0 := by
      unfold initState
      have hc0 : (rowOf f ⟨0, hn⟩).c0 = .a0 := by
        change C4.ofFin (f (⟨0, hn⟩, 0)) = .a0; rw [hf0']; rfl
      have hc3 : (rowOf f ⟨0, hn⟩).c3 = .a1 := by
        change C4.ofFin (f (⟨0, hn⟩, 3)) = .a1; rw [hf1']; rfl
      rw [hc0, hc3]
      exact ⟨_, rfl⟩
    obtain ⟨s0, hs0⟩ := hinit_some
    obtain ⟨hpok0, _, _⟩ := initState_PrefixOk f hn hs0
    have hrun := runFrom_PrefixOk f k 0 (by omega) s0 hpok0
    obtain ⟨t, ht⟩ := hrun.2 hv
    have hpokk := hrun.1 t ht
    have hfin : isFinal t = true := (final_iff_Valid f hn (by simpa using hpokk) hf0' hf1').2 hv
    refine ⟨t, ?_, hfin⟩
    unfold runBoard
    change (match initState (rowOf f ⟨0, hn⟩) with
      | none => none
      | some s => runFrom k s (fun i : Fin k => rowOf f i.succ)) = some t
    rw [hs0]
    convert ht using 2
    funext i; congr 1; ext; dsimp; omega
  · rintro ⟨t, ht, hfin⟩
    unfold runBoard at ht
    change (match initState (rowOf f ⟨0, hn⟩) with
      | none => none
      | some s => runFrom k s (fun i : Fin k => rowOf f i.succ)) = some t at ht
    cases hs0 : initState (rowOf f ⟨0, hn⟩) with
    | none => rw [hs0] at ht; cases ht
    | some s0 =>
      rw [hs0] at ht; dsimp only at ht
      obtain ⟨hpok0, hf0, hf1⟩ := initState_PrefixOk f hn hs0
      have hrun := runFrom_PrefixOk f k 0 (by omega) s0 hpok0
      have ht' : runFrom k s0 (fun i : Fin k => rowOf f ⟨0 + 1 + i.val, by omega⟩) = some t := by
        convert ht using 2
        funext i; congr 1; ext; dsimp; omega
      have hpokk := hrun.1 t ht'
      exact (final_iff_Valid f hn (by simpa using hpokk) hf0 hf1).1 hfin

private abbrev GoodFrom (k : ℕ) (s : State) :=
  {w : Fin k → Row // ∃ t, runFrom k s w = some t ∧ isFinal t = true}

private def splitGood (k : ℕ) (s : State) :
    GoodFrom (k + 1) s ≃
      (Σ r : {r : Row // (step s r).isSome}, GoodFrom k ((step s r.1).get r.2)) where
  toFun z :=
    have hsr_some : (step s (z.1 0)).isSome = true := by
      rcases z.2 with ⟨t, ht, _⟩
      unfold runFrom at ht
      cases hsr : step s (z.1 0) with
      | none => rw [hsr] at ht; cases ht
      | some _ => rfl
    ⟨⟨z.1 0, hsr_some⟩, ⟨fun i => z.1 i.succ, by
      rcases z.2 with ⟨t, ht, hfin⟩
      unfold runFrom at ht
      obtain ⟨s1, hs1⟩ := Option.isSome_iff_exists.1 hsr_some
      rw [hs1] at ht
      refine ⟨t, ?_, hfin⟩
      simpa [hs1] using ht⟩⟩
  invFun z :=
    ⟨Fin.cons z.1.1 z.2.1, by
      rcases z with ⟨⟨r, hr⟩, ⟨w, ⟨t, ht, hfin⟩⟩⟩
      obtain ⟨s1, hs1⟩ := Option.isSome_iff_exists.1 hr
      refine ⟨t, ?_, hfin⟩
      unfold runFrom
      simp only [Fin.cons_zero, Fin.cons_succ, hs1]
      simpa [hs1] using ht⟩
  left_inv z := Subtype.ext (Fin.cons_self_tail z.1)
  right_inv z := by
    rcases z with ⟨⟨r, hr⟩, ⟨w, hw⟩⟩
    rfl

private lemma card_GoodFrom (k : ℕ) (s : State) :
    Fintype.card (GoodFrom k s) = ways k s := by
  induction k generalizing s with
  | zero =>
    unfold ways
    by_cases hf : isFinal s = true
    · simp only [hf, ite_true]
      have : Unique (GoodFrom 0 s) :=
        { default := ⟨Fin.elim0, ⟨s, rfl, hf⟩⟩
          uniq := fun z => Subtype.ext (funext fun i => i.elim0) }
      exact Fintype.card_unique
    · simp only [hf]
      have : IsEmpty (GoodFrom 0 s) := ⟨fun z => by
        rcases z.2 with ⟨t, ht, hfin⟩
        cases ht; exact hf hfin⟩
      exact Fintype.card_eq_zero
  | succ k ih =>
    unfold ways
    rw [Fintype.card_congr (splitGood k s), Fintype.card_sigma]
    have hcongr :
        (∑ r : {r : Row // (step s r).isSome}, Fintype.card (GoodFrom k ((step s r.1).get r.2))) =
        (∑ r : {r : Row // (step s r).isSome},
          match step s r.1 with | none => 0 | some t => Fintype.card (GoodFrom k t)) := by
      apply Finset.sum_congr rfl
      intro ⟨r, hr⟩ _
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hr
      simp [ht]
    rw [hcongr]
    have hsum :
        (∑ r : {r : Row // (step s r).isSome},
          match step s r.1 with | none => 0 | some t => Fintype.card (GoodFrom k t)) =
        ∑ r : Row, match step s r with | none => 0 | some t => Fintype.card (GoodFrom k t) := by
      have h1 := Finset.sum_subtype (p := fun r : Row => (step s r).isSome = true)
        (F := inferInstance)
        (Finset.univ.filter fun r : Row => (step s r).isSome = true)
        (by intro r; simp) (fun r => match step s r with | none => 0 | some t => Fintype.card (GoodFrom k t))
      rw [← h1, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r _
      cases hsr : step s r <;> simp
    rw [hsum]
    apply Finset.sum_congr rfl
    intro r _
    cases hsr : step s r
    · rfl
    · exact ih _

private lemma card_Valid_eq_ways (k : ℕ) :
    Nat.card {f : Cell (k + 1) → Fin 4 // Valid (k + 1) f} =
      ∑ r : Row, match initState r with | none => 0 | some s => ways k s := by
  classical
  rw [Nat.card_eq_fintype_card]
  let e1 : {f : Cell (k + 1) → Fin 4 // Valid (k + 1) f} ≃
      {w : Fin (k + 1) → Row // ∃ t, runBoard k w = some t ∧ isFinal t = true} :=
    { toFun := fun z => ⟨boardEquiv (k + 1) z.1, (runBoard_iff_Valid k z.1).1 z.2⟩
      invFun := fun z => ⟨(boardEquiv (k + 1)).symm z.1,
        (runBoard_iff_Valid k _).2 (by simpa using z.2)⟩
      left_inv := fun z => Subtype.ext ((boardEquiv (k + 1)).left_inv z.1)
      right_inv := fun z => Subtype.ext ((boardEquiv (k + 1)).right_inv z.1) }
  let e2 : {w : Fin (k + 1) → Row // ∃ t, runBoard k w = some t ∧ isFinal t = true} ≃
      (Σ r : {r : Row // (initState r).isSome}, GoodFrom k ((initState r.1).get r.2)) :=
    { toFun := fun z =>
        have hr_some : (initState (z.1 0)).isSome = true := by
          rcases z.2 with ⟨t, ht, _⟩
          unfold runBoard at ht
          cases hr : initState (z.1 0) with
          | none => rw [hr] at ht; cases ht
          | some _ => rfl
        ⟨⟨z.1 0, hr_some⟩, ⟨fun i => z.1 i.succ, by
          rcases z.2 with ⟨t, ht, hfin⟩
          unfold runBoard at ht
          obtain ⟨s0, hs0⟩ := Option.isSome_iff_exists.1 hr_some
          rw [hs0] at ht
          exact ⟨t, by simpa [hs0] using ht, hfin⟩⟩⟩
      invFun := fun z =>
        ⟨Fin.cons z.1.1 z.2.1, by
          rcases z with ⟨⟨r, hr⟩, ⟨w, ⟨t, ht, hfin⟩⟩⟩
          obtain ⟨s0, hs0⟩ := Option.isSome_iff_exists.1 hr
          refine ⟨t, ?_, hfin⟩
          unfold runBoard
          simp only [Fin.cons_zero, Fin.cons_succ, hs0]
          simpa [hs0] using ht⟩
      left_inv := fun z => Subtype.ext (Fin.cons_self_tail z.1)
      right_inv := fun z => by rcases z with ⟨⟨r, hr⟩, ⟨w, hw⟩⟩; rfl }
  rw [Fintype.card_congr (e1.trans e2), Fintype.card_sigma]
  have hcongr :
      (∑ r : {r : Row // (initState r).isSome}, Fintype.card (GoodFrom k ((initState r.1).get r.2))) =
      (∑ r : {r : Row // (initState r).isSome},
        match initState r.1 with | none => 0 | some s => Fintype.card (GoodFrom k s)) := by
    apply Finset.sum_congr rfl
    intro ⟨r, hr⟩ _
    obtain ⟨s0, hs0⟩ := Option.isSome_iff_exists.1 hr
    simp [hs0]
  rw [hcongr]
  have hsum :
      (∑ r : {r : Row // (initState r).isSome},
        match initState r.1 with | none => 0 | some s => Fintype.card (GoodFrom k s)) =
      ∑ r : Row, match initState r with | none => 0 | some s => Fintype.card (GoodFrom k s) := by
    have h1 := Finset.sum_subtype (p := fun r : Row => (initState r).isSome = true)
      (F := inferInstance)
      (Finset.univ.filter fun r : Row => (initState r).isSome = true)
      (by intro r; simp) (fun r => match initState r with | none => 0 | some s => Fintype.card (GoodFrom k s))
    rw [← h1, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    cases hir : initState r <;> simp
  rw [hsum]
  apply Finset.sum_congr rfl
  intro r _
  cases hir : initState r
  · rfl
  · exact card_GoodFrom k _


/-! ### Part 4: Reachable automaton table and polynomial transfer proof -/

private structure StateData where
  st : State
  es : List (Row × Fin 390)
  w0 : ℕ
  w1 : ℕ
  w2 : ℕ
  a0 : ℕ
  a1 : ℕ
  a2 : ℕ

private def dataOf (i : Fin 390) : StateData :=
  (if i.val < 195 then (if i.val < 97 then (if i.val < 48 then (if i.val < 24 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then ⟨⟨.a0,.a0,.a0,.a1,.d2,.d1,.d0,.a0,.a0,.a0,.a1,false,false⟩,[(⟨.a1,.a0,.a1,.a0⟩,16),(⟨.a1,.a0,.a1,.a1⟩,17),(⟨.a1,.a0,.a1,.a2⟩,18),(⟨.a1,.a0,.a1,.a3⟩,19),(⟨.a1,.a1,.a1,.a2⟩,20),(⟨.a1,.a1,.a1,.a3⟩,21),(⟨.a1,.a2,.a1,.a1⟩,22),(⟨.a1,.a2,.a1,.a2⟩,23),(⟨.a1,.a2,.a1,.a3⟩,24),(⟨.a1,.a3,.a1,.a1⟩,25),(⟨.a1,.a3,.a1,.a2⟩,26),(⟨.a1,.a3,.a1,.a3⟩,27),(⟨.a2,.a0,.a0,.a0⟩,28),(⟨.a2,.a0,.a0,.a2⟩,29),(⟨.a2,.a0,.a0,.a3⟩,30),(⟨.a2,.a0,.a1,.a0⟩,31),(⟨.a2,.a0,.a1,.a1⟩,32),(⟨.a2,.a0,.a1,.a2⟩,33),(⟨.a2,.a0,.a1,.a3⟩,34),(⟨.a2,.a0,.a2,.a0⟩,35),(⟨.a2,.a0,.a2,.a2⟩,36),(⟨.a2,.a0,.a2,.a3⟩,37),(⟨.a2,.a0,.a3,.a0⟩,38),(⟨.a2,.a0,.a3,.a2⟩,39),(⟨.a2,.a0,.a3,.a3⟩,40),(⟨.a2,.a1,.a1,.a2⟩,41),(⟨.a2,.a1,.a1,.a3⟩,42),(⟨.a2,.a2,.a1,.a1⟩,43),(⟨.a2,.a2,.a1,.a2⟩,44),(⟨.a2,.a2,.a1,.a3⟩,45),(⟨.a2,.a2,.a2,.a2⟩,46),(⟨.a2,.a2,.a2,.a3⟩,47),(⟨.a2,.a2,.a3,.a2⟩,48),(⟨.a2,.a2,.a3,.a3⟩,49),(⟨.a2,.a3,.a1,.a1⟩,50),(⟨.a2,.a3,.a1,.a2⟩,51),(⟨.a2,.a3,.a1,.a3⟩,52),(⟨.a2,.a3,.a2,.a2⟩,53),(⟨.a2,.a3,.a2,.a3⟩,54),(⟨.a2,.a3,.a3,.a2⟩,55),(⟨.a2,.a3,.a3,.a3⟩,56),(⟨.a3,.a0,.a0,.a0⟩,57),(⟨.a3,.a0,.a0,.a2⟩,58),(⟨.a3,.a0,.a0,.a3⟩,59),(⟨.a3,.a0,.a1,.a0⟩,60),(⟨.a3,.a0,.a1,.a1⟩,61),(⟨.a3,.a0,.a1,.a2⟩,62),(⟨.a3,.a0,.a1,.a3⟩,63),(⟨.a3,.a0,.a2,.a0⟩,64),(⟨.a3,.a0,.a2,.a2⟩,65),(⟨.a3,.a0,.a2,.a3⟩,66),(⟨.a3,.a0,.a3,.a0⟩,67),(⟨.a3,.a0,.a3,.a2⟩,68),(⟨.a3,.a0,.a3,.a3⟩,69),(⟨.a3,.a1,.a1,.a2⟩,70),(⟨.a3,.a1,.a1,.a3⟩,71),(⟨.a3,.a2,.a1,.a1⟩,72),(⟨.a3,.a2,.a1,.a2⟩,73),(⟨.a3,.a2,.a1,.a3⟩,74),(⟨.a3,.a2,.a2,.a2⟩,75),(⟨.a3,.a2,.a2,.a3⟩,76),(⟨.a3,.a2,.a3,.a2⟩,77),(⟨.a3,.a2,.a3,.a3⟩,78),(⟨.a3,.a3,.a1,.a1⟩,79),(⟨.a3,.a3,.a1,.a2⟩,80),(⟨.a3,.a3,.a1,.a3⟩,81),(⟨.a3,.a3,.a2,.a2⟩,82),(⟨.a3,.a3,.a2,.a3⟩,83),(⟨.a3,.a3,.a3,.a2⟩,84),(⟨.a3,.a3,.a3,.a3⟩,85)],0,8,11,13,3,0⟩ else (if i.val < 2 then ⟨⟨.a0,.a0,.a1,.a1,.d1,.d1,.d1,.a0,.a0,.a1,.a1,false,false⟩,[(⟨.a0,.a0,.a0,.a0⟩,86),(⟨.a0,.a0,.a0,.a2⟩,87),(⟨.a0,.a0,.a0,.a3⟩,88),(⟨.a0,.a0,.a1,.a0⟩,89),(⟨.a0,.a0,.a1,.a1⟩,90),(⟨.a0,.a0,.a1,.a2⟩,91),(⟨.a0,.a0,.a1,.a3⟩,92),(⟨.a0,.a0,.a2,.a0⟩,93),(⟨.a0,.a0,.a2,.a2⟩,94),(⟨.a0,.a0,.a2,.a3⟩,95),(⟨.a0,.a0,.a3,.a0⟩,96),(⟨.a0,.a0,.a3,.a2⟩,97),(⟨.a0,.a0,.a3,.a3⟩,98),(⟨.a0,.a1,.a0,.a0⟩,99),(⟨.a0,.a1,.a0,.a1⟩,100),(⟨.a0,.a1,.a0,.a2⟩,101),(⟨.a0,.a1,.a0,.a3⟩,102),(⟨.a0,.a1,.a1,.a0⟩,103),(⟨.a0,.a1,.a1,.a2⟩,104),(⟨.a0,.a1,.a1,.a3⟩,105),(⟨.a0,.a1,.a2,.a0⟩,106),(⟨.a0,.a1,.a2,.a1⟩,107),(⟨.a0,.a1,.a2,.a2⟩,108),(⟨.a0,.a1,.a2,.a3⟩,109),(⟨.a0,.a1,.a3,.a0⟩,110),(⟨.a0,.a1,.a3,.a1⟩,111),(⟨.a0,.a1,.a3,.a2⟩,112),(⟨.a0,.a1,.a3,.a3⟩,113),(⟨.a0,.a2,.a0,.a0⟩,114),(⟨.a0,.a2,.a0,.a2⟩,115),(⟨.a0,.a2,.a0,.a3⟩,116),(⟨.a0,.a2,.a1,.a0⟩,117),(⟨.a0,.a2,.a1,.a1⟩,118),(⟨.a0,.a2,.a1,.a2⟩,119),(⟨.a0,.a2,.a1,.a3⟩,120),(⟨.a0,.a2,.a2,.a0⟩,121),(⟨.a0,.a2,.a2,.a2⟩,122),(⟨.a0,.a2,.a2,.a3⟩,123),(⟨.a0,.a2,.a3,.a0⟩,124),(⟨.a0,.a2,.a3,.a2⟩,125),(⟨.a0,.a2,.a3,.a3⟩,126),(⟨.a0,.a3,.a0,.a0⟩,127),(⟨.a0,.a3,.a0,.a2⟩,128),(⟨.a0,.a3,.a0,.a3⟩,129),(⟨.a0,.a3,.a1,.a0⟩,130),(⟨.a0,.a3,.a1,.a1⟩,131),(⟨.a0,.a3,.a1,.a2⟩,132),(⟨.a0,.a3,.a1,.a3⟩,133),(⟨.a0,.a3,.a2,.a0⟩,134),(⟨.a0,.a3,.a2,.a2⟩,135),(⟨.a0,.a3,.a2,.a3⟩,136),(⟨.a0,.a3,.a3,.a0⟩,137),(⟨.a0,.a3,.a3,.a2⟩,138),(⟨.a0,.a3,.a3,.a3⟩,139),(⟨.a1,.a1,.a2,.a1⟩,140),(⟨.a1,.a1,.a2,.a2⟩,141),(⟨.a1,.a1,.a2,.a3⟩,142),(⟨.a1,.a1,.a3,.a1⟩,143),(⟨.a1,.a1,.a3,.a2⟩,144),(⟨.a1,.a1,.a3,.a3⟩,145),(⟨.a1,.a2,.a1,.a1⟩,22),(⟨.a1,.a2,.a1,.a2⟩,23),(⟨.a1,.a2,.a1,.a3⟩,24),(⟨.a1,.a3,.a1,.a1⟩,25),(⟨.a1,.a3,.a1,.a2⟩,26),(⟨.a1,.a3,.a1,.a3⟩,27),(⟨.a2,.a1,.a1,.a2⟩,146),(⟨.a2,.a1,.a1,.a3⟩,147),(⟨.a2,.a1,.a2,.a1⟩,148),(⟨.a2,.a1,.a2,.a2⟩,149),(⟨.a2,.a1,.a2,.a3⟩,150),(⟨.a2,.a1,.a3,.a1⟩,151),(⟨.a2,.a1,.a3,.a2⟩,152),(⟨.a2,.a1,.a3,.a3⟩,153),(⟨.a2,.a2,.a1,.a1⟩,43),(⟨.a2,.a2,.a1,.a2⟩,44),(⟨.a2,.a2,.a1,.a3⟩,45),(⟨.a2,.a2,.a2,.a2⟩,46),(⟨.a2,.a2,.a2,.a3⟩,47),(⟨.a2,.a2,.a3,.a2⟩,48),(⟨.a2,.a2,.a3,.a3⟩,49),(⟨.a2,.a3,.a1,.a1⟩,50),(⟨.a2,.a3,.a1,.a2⟩,51),(⟨.a2,.a3,.a1,.a3⟩,52),(⟨.a2,.a3,.a2,.a2⟩,53),(⟨.a2,.a3,.a2,.a3⟩,54),(⟨.a2,.a3,.a3,.a2⟩,55),(⟨.a2,.a3,.a3,.a3⟩,56),(⟨.a3,.a1,.a1,.a2⟩,154),(⟨.a3,.a1,.a1,.a3⟩,155),(⟨.a3,.a1,.a2,.a1⟩,156),(⟨.a3,.a1,.a2,.a2⟩,157),(⟨.a3,.a1,.a2,.a3⟩,158),(⟨.a3,.a1,.a3,.a1⟩,159),(⟨.a3,.a1,.a3,.a2⟩,160),(⟨.a3,.a1,.a3,.a3⟩,161),(⟨.a3,.a2,.a1,.a1⟩,72),(⟨.a3,.a2,.a1,.a2⟩,73),(⟨.a3,.a2,.a1,.a3⟩,74),(⟨.a3,.a2,.a2,.a2⟩,75),(⟨.a3,.a2,.a2,.a3⟩,76),(⟨.a3,.a2,.a3,.a2⟩,77),(⟨.a3,.a2,.a3,.a3⟩,78),(⟨.a3,.a3,.a1,.a1⟩,79),(⟨.a3,.a3,.a1,.a2⟩,80),(⟨.a3,.a3,.a1,.a3⟩,81),(⟨.a3,.a3,.a2,.a2⟩,82),(⟨.a3,.a3,.a2,.a3⟩,83),(⟨.a3,.a3,.a3,.a2⟩,84),(⟨.a3,.a3,.a3,.a3⟩,85)],0,6,45,96,61,9⟩ else ⟨⟨.a0,.a0,.a2,.a1,.d1,.d0,.d0,.a0,.a0,.a1,.a2,false,false⟩,[(⟨.a0,.a2,.a0,.a0⟩,162),(⟨.a0,.a2,.a0,.a2⟩,163),(⟨.a0,.a2,.a0,.a3⟩,164),(⟨.a0,.a2,.a1,.a0⟩,165),(⟨.a0,.a2,.a1,.a1⟩,166),(⟨.a0,.a2,.a1,.a2⟩,167),(⟨.a0,.a2,.a1,.a3⟩,168),(⟨.a0,.a2,.a2,.a0⟩,169),(⟨.a0,.a2,.a2,.a2⟩,170),(⟨.a0,.a2,.a2,.a3⟩,171),(⟨.a0,.a2,.a3,.a0⟩,172),(⟨.a0,.a2,.a3,.a2⟩,173),(⟨.a0,.a2,.a3,.a3⟩,174),(⟨.a1,.a2,.a1,.a1⟩,175),(⟨.a1,.a2,.a1,.a2⟩,176),(⟨.a1,.a2,.a1,.a3⟩,177),(⟨.a2,.a2,.a1,.a1⟩,178),(⟨.a2,.a2,.a1,.a2⟩,179),(⟨.a2,.a2,.a1,.a3⟩,180),(⟨.a2,.a2,.a3,.a2⟩,181),(⟨.a2,.a2,.a3,.a3⟩,182),(⟨.a3,.a2,.a1,.a1⟩,183),(⟨.a3,.a2,.a1,.a2⟩,184),(⟨.a3,.a2,.a1,.a3⟩,185),(⟨.a3,.a2,.a2,.a2⟩,186),(⟨.a3,.a2,.a2,.a3⟩,187),(⟨.a3,.a2,.a3,.a2⟩,188),(⟨.a3,.a2,.a3,.a3⟩,189)],0,2,8,10,2,0⟩)) else (if i.val < 4 then ⟨⟨.a0,.a0,.a3,.a1,.d1,.d0,.d0,.a0,.a0,.a1,.a2,false,false⟩,[(⟨.a0,.a3,.a0,.a0⟩,190),(⟨.a0,.a3,.a0,.a2⟩,191),(⟨.a0,.a3,.a0,.a3⟩,192),(⟨.a0,.a3,.a1,.a0⟩,193),(⟨.a0,.a3,.a1,.a1⟩,194),(⟨.a0,.a3,.a1,.a2⟩,195),(⟨.a0,.a3,.a1,.a3⟩,196),(⟨.a0,.a3,.a2,.a0⟩,197),(⟨.a0,.a3,.a2,.a2⟩,198),(⟨.a0,.a3,.a2,.a3⟩,199),(⟨.a0,.a3,.a3,.a0⟩,200),(⟨.a0,.a3,.a3,.a2⟩,201),(⟨.a0,.a3,.a3,.a3⟩,202),(⟨.a1,.a3,.a1,.a1⟩,203),(⟨.a1,.a3,.a1,.a2⟩,204),(⟨.a1,.a3,.a1,.a3⟩,205),(⟨.a2,.a3,.a1,.a1⟩,206),(⟨.a2,.a3,.a1,.a2⟩,207),(⟨.a2,.a3,.a1,.a3⟩,208),(⟨.a2,.a3,.a2,.a2⟩,209),(⟨.a2,.a3,.a2,.a3⟩,210),(⟨.a2,.a3,.a3,.a2⟩,211),(⟨.a2,.a3,.a3,.a3⟩,212),(⟨.a3,.a3,.a1,.a1⟩,213),(⟨.a3,.a3,.a1,.a2⟩,214),(⟨.a3,.a3,.a1,.a3⟩,215),(⟨.a3,.a3,.a2,.a2⟩,216),(⟨.a3,.a3,.a2,.a3⟩,217)],0,1,1,2,1,0⟩ else (if i.val < 5 then ⟨⟨.a0,.a1,.a0,.a1,.d0,.d0,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a1,.a1,.a1,.d1,.d2,.d1,.a0,.a1,.a1,.a1,false,false⟩,[(⟨.a1,.a2,.a1,.a1⟩,218),(⟨.a1,.a2,.a1,.a2⟩,219),(⟨.a1,.a2,.a1,.a3⟩,220),(⟨.a1,.a2,.a2,.a1⟩,221),(⟨.a1,.a2,.a2,.a2⟩,222),(⟨.a1,.a2,.a2,.a3⟩,223),(⟨.a1,.a2,.a3,.a1⟩,224),(⟨.a1,.a2,.a3,.a2⟩,225),(⟨.a1,.a2,.a3,.a3⟩,226),(⟨.a1,.a3,.a1,.a1⟩,227),(⟨.a1,.a3,.a1,.a2⟩,228),(⟨.a1,.a3,.a1,.a3⟩,229),(⟨.a1,.a3,.a2,.a1⟩,230),(⟨.a1,.a3,.a2,.a2⟩,231),(⟨.a1,.a3,.a2,.a3⟩,232),(⟨.a1,.a3,.a3,.a1⟩,233),(⟨.a1,.a3,.a3,.a2⟩,234),(⟨.a1,.a3,.a3,.a3⟩,235),(⟨.a2,.a2,.a1,.a1⟩,43),(⟨.a2,.a2,.a1,.a2⟩,44),(⟨.a2,.a2,.a1,.a3⟩,45),(⟨.a2,.a2,.a2,.a2⟩,46),(⟨.a2,.a2,.a2,.a3⟩,47),(⟨.a2,.a2,.a3,.a2⟩,48),(⟨.a2,.a2,.a3,.a3⟩,49),(⟨.a2,.a3,.a1,.a1⟩,50),(⟨.a2,.a3,.a1,.a2⟩,51),(⟨.a2,.a3,.a1,.a3⟩,52),(⟨.a2,.a3,.a2,.a2⟩,53),(⟨.a2,.a3,.a2,.a3⟩,54),(⟨.a2,.a3,.a3,.a2⟩,55),(⟨.a2,.a3,.a3,.a3⟩,56),(⟨.a3,.a2,.a1,.a1⟩,72),(⟨.a3,.a2,.a1,.a2⟩,73),(⟨.a3,.a2,.a1,.a3⟩,74),(⟨.a3,.a2,.a2,.a2⟩,75),(⟨.a3,.a2,.a2,.a3⟩,76),(⟨.a3,.a2,.a3,.a2⟩,77),(⟨.a3,.a2,.a3,.a3⟩,78),(⟨.a3,.a3,.a1,.a1⟩,79),(⟨.a3,.a3,.a1,.a2⟩,80),(⟨.a3,.a3,.a1,.a3⟩,81),(⟨.a3,.a3,.a2,.a2⟩,82),(⟨.a3,.a3,.a2,.a3⟩,83),(⟨.a3,.a3,.a3,.a2⟩,84),(⟨.a3,.a3,.a3,.a3⟩,85)],0,4,20,25,6,0⟩))) else (if i.val < 9 then (if i.val < 7 then ⟨⟨.a0,.a1,.a2,.a1,.d0,.d0,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a1,.a2,.a1,.a1⟩,175),(⟨.a1,.a2,.a1,.a2⟩,176),(⟨.a1,.a2,.a1,.a3⟩,177)],0,0,0,0,0,0⟩ else (if i.val < 8 then ⟨⟨.a0,.a1,.a3,.a1,.d0,.d0,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a1,.a3,.a1,.a1⟩,203),(⟨.a1,.a3,.a1,.a2⟩,204),(⟨.a1,.a3,.a1,.a3⟩,205)],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a2,.a0,.a1,.d0,.d0,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 10 then ⟨⟨.a0,.a2,.a1,.a1,.d0,.d1,.d1,.a0,.a1,.a2,.a2,false,false⟩,[(⟨.a2,.a1,.a1,.a2⟩,146),(⟨.a2,.a1,.a1,.a3⟩,147),(⟨.a2,.a1,.a2,.a1⟩,148),(⟨.a2,.a1,.a2,.a2⟩,149),(⟨.a2,.a1,.a2,.a3⟩,150),(⟨.a2,.a1,.a3,.a1⟩,151),(⟨.a2,.a1,.a3,.a2⟩,152),(⟨.a2,.a1,.a3,.a3⟩,153),(⟨.a2,.a2,.a1,.a1⟩,43),(⟨.a2,.a2,.a1,.a2⟩,44),(⟨.a2,.a2,.a1,.a3⟩,45),(⟨.a2,.a2,.a2,.a2⟩,46),(⟨.a2,.a2,.a2,.a3⟩,47),(⟨.a2,.a2,.a3,.a2⟩,48),(⟨.a2,.a2,.a3,.a3⟩,49),(⟨.a2,.a3,.a1,.a1⟩,50),(⟨.a2,.a3,.a1,.a2⟩,51),(⟨.a2,.a3,.a1,.a3⟩,52),(⟨.a2,.a3,.a2,.a2⟩,53),(⟨.a2,.a3,.a2,.a3⟩,54),(⟨.a2,.a3,.a3,.a2⟩,55),(⟨.a2,.a3,.a3,.a3⟩,56)],0,6,8,10,2,0⟩ else (if i.val < 11 then ⟨⟨.a0,.a2,.a2,.a1,.d1,.d1,.d0,.a0,.a1,.a1,.a2,false,false⟩,[(⟨.a1,.a2,.a1,.a1⟩,175),(⟨.a1,.a2,.a1,.a2⟩,176),(⟨.a1,.a2,.a1,.a3⟩,177),(⟨.a2,.a1,.a1,.a2⟩,41),(⟨.a2,.a1,.a1,.a3⟩,42),(⟨.a2,.a2,.a1,.a1⟩,178),(⟨.a2,.a2,.a1,.a2⟩,179),(⟨.a2,.a2,.a1,.a3⟩,180),(⟨.a2,.a2,.a3,.a2⟩,181),(⟨.a2,.a2,.a3,.a3⟩,182),(⟨.a2,.a3,.a1,.a1⟩,50),(⟨.a2,.a3,.a1,.a2⟩,51),(⟨.a2,.a3,.a1,.a3⟩,52),(⟨.a2,.a3,.a2,.a2⟩,53),(⟨.a2,.a3,.a2,.a3⟩,54),(⟨.a2,.a3,.a3,.a2⟩,55),(⟨.a2,.a3,.a3,.a3⟩,56),(⟨.a3,.a2,.a1,.a1⟩,183),(⟨.a3,.a2,.a1,.a2⟩,184),(⟨.a3,.a2,.a1,.a3⟩,185),(⟨.a3,.a2,.a2,.a2⟩,186),(⟨.a3,.a2,.a2,.a3⟩,187),(⟨.a3,.a2,.a3,.a2⟩,188),(⟨.a3,.a2,.a3,.a3⟩,189)],0,4,0,0,0,0⟩ else ⟨⟨.a0,.a2,.a3,.a1,.d0,.d0,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a2,.a3,.a1,.a1⟩,206),(⟨.a2,.a3,.a1,.a2⟩,207),(⟨.a2,.a3,.a1,.a3⟩,208),(⟨.a2,.a3,.a2,.a2⟩,209),(⟨.a2,.a3,.a2,.a3⟩,210),(⟨.a2,.a3,.a3,.a2⟩,211),(⟨.a2,.a3,.a3,.a3⟩,212)],0,1,0,0,0,0⟩)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then ⟨⟨.a0,.a3,.a0,.a1,.d0,.d0,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 14 then ⟨⟨.a0,.a3,.a1,.a1,.d0,.d1,.d1,.a0,.a1,.a2,.a2,false,false⟩,[(⟨.a3,.a1,.a1,.a2⟩,154),(⟨.a3,.a1,.a1,.a3⟩,155),(⟨.a3,.a1,.a2,.a1⟩,156),(⟨.a3,.a1,.a2,.a2⟩,157),(⟨.a3,.a1,.a2,.a3⟩,158),(⟨.a3,.a1,.a3,.a1⟩,159),(⟨.a3,.a1,.a3,.a2⟩,160),(⟨.a3,.a1,.a3,.a3⟩,161),(⟨.a3,.a2,.a1,.a1⟩,72),(⟨.a3,.a2,.a1,.a2⟩,73),(⟨.a3,.a2,.a1,.a3⟩,74),(⟨.a3,.a2,.a2,.a2⟩,75),(⟨.a3,.a2,.a2,.a3⟩,76),(⟨.a3,.a2,.a3,.a2⟩,77),(⟨.a3,.a2,.a3,.a3⟩,78),(⟨.a3,.a3,.a1,.a1⟩,79),(⟨.a3,.a3,.a1,.a2⟩,80),(⟨.a3,.a3,.a1,.a3⟩,81),(⟨.a3,.a3,.a2,.a2⟩,82),(⟨.a3,.a3,.a2,.a3⟩,83),(⟨.a3,.a3,.a3,.a2⟩,84),(⟨.a3,.a3,.a3,.a3⟩,85)],0,0,1,2,1,0⟩ else ⟨⟨.a0,.a3,.a2,.a1,.d0,.d0,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a3,.a2,.a1,.a1⟩,183),(⟨.a3,.a2,.a1,.a2⟩,184),(⟨.a3,.a2,.a1,.a3⟩,185),(⟨.a3,.a2,.a2,.a2⟩,186),(⟨.a3,.a2,.a2,.a3⟩,187),(⟨.a3,.a2,.a3,.a2⟩,188),(⟨.a3,.a2,.a3,.a3⟩,189)],0,0,0,0,0,0⟩)) else (if i.val < 16 then ⟨⟨.a0,.a3,.a3,.a1,.d1,.d1,.d0,.a0,.a1,.a1,.a2,false,false⟩,[(⟨.a1,.a3,.a1,.a1⟩,203),(⟨.a1,.a3,.a1,.a2⟩,204),(⟨.a1,.a3,.a1,.a3⟩,205),(⟨.a2,.a3,.a1,.a1⟩,206),(⟨.a2,.a3,.a1,.a2⟩,207),(⟨.a2,.a3,.a1,.a3⟩,208),(⟨.a2,.a3,.a2,.a2⟩,209),(⟨.a2,.a3,.a2,.a3⟩,210),(⟨.a2,.a3,.a3,.a2⟩,211),(⟨.a2,.a3,.a3,.a3⟩,212),(⟨.a3,.a1,.a1,.a2⟩,70),(⟨.a3,.a1,.a1,.a3⟩,71),(⟨.a3,.a2,.a1,.a1⟩,72),(⟨.a3,.a2,.a1,.a2⟩,73),(⟨.a3,.a2,.a1,.a3⟩,74),(⟨.a3,.a2,.a2,.a2⟩,75),(⟨.a3,.a2,.a2,.a3⟩,76),(⟨.a3,.a2,.a3,.a2⟩,77),(⟨.a3,.a2,.a3,.a3⟩,78),(⟨.a3,.a3,.a1,.a1⟩,213),(⟨.a3,.a3,.a1,.a2⟩,214),(⟨.a3,.a3,.a1,.a3⟩,215),(⟨.a3,.a3,.a2,.a2⟩,216),(⟨.a3,.a3,.a2,.a3⟩,217)],0,1,0,0,0,0⟩ else (if i.val < 17 then ⟨⟨.a1,.a0,.a1,.a0,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a0,.a1,.a1,.d1,.d2,.d1,.a0,.a1,.a2,.a2,false,false⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 21 then (if i.val < 19 then ⟨⟨.a1,.a0,.a1,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 20 then ⟨⟨.a1,.a0,.a1,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a1,.a1,.a2,.d2,.d2,.d0,.a0,.a0,.a0,.a1,true,false⟩,[(⟨.a2,.a2,.a2,.a3⟩,236),(⟨.a2,.a3,.a2,.a2⟩,237),(⟨.a2,.a3,.a2,.a3⟩,238),(⟨.a3,.a2,.a2,.a3⟩,239),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,1,0,0,0,0⟩)) else (if i.val < 22 then ⟨⟨.a1,.a1,.a1,.a3,.d2,.d2,.d0,.a0,.a0,.a0,.a1,true,false⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a3,.a2⟩,244),(⟨.a3,.a2,.a3,.a2⟩,245),(⟨.a3,.a2,.a3,.a3⟩,246),(⟨.a3,.a3,.a3,.a2⟩,247)],0,1,1,1,0,0⟩ else (if i.val < 23 then ⟨⟨.a1,.a2,.a1,.a1,.d0,.d2,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a2,.a1,.a2,.d0,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩))))) else (if i.val < 36 then (if i.val < 30 then (if i.val < 27 then (if i.val < 25 then ⟨⟨.a1,.a2,.a1,.a3,.d0,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 26 then ⟨⟨.a1,.a3,.a1,.a1,.d0,.d2,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a3,.a1,.a2,.d0,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 28 then ⟨⟨.a1,.a3,.a1,.a3,.d0,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 29 then ⟨⟨.a2,.a0,.a0,.a0,.d2,.d2,.d1,.a0,.a1,.a1,.a1,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a0,.a0,.a2,.d2,.d1,.d0,.a0,.a1,.a1,.a2,false,true⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 33 then (if i.val < 31 then ⟨⟨.a2,.a0,.a0,.a3,.d2,.d1,.d0,.a0,.a1,.a1,.a2,false,true⟩,[],1,0,0,0,0,0⟩ else (if i.val < 32 then ⟨⟨.a2,.a0,.a1,.a0,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a0,.a1,.a1,.d1,.d2,.d1,.a0,.a1,.a2,.a2,false,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 34 then ⟨⟨.a2,.a0,.a1,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 35 then ⟨⟨.a2,.a0,.a1,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],1,0,0,0,0,0⟩ else ⟨⟨.a2,.a0,.a2,.a0,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩)))) else (if i.val < 42 then (if i.val < 39 then (if i.val < 37 then ⟨⟨.a2,.a0,.a2,.a2,.d1,.d1,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 38 then ⟨⟨.a2,.a0,.a2,.a3,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a0,.a3,.a0,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 40 then ⟨⟨.a2,.a0,.a3,.a2,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 41 then ⟨⟨.a2,.a0,.a3,.a3,.d1,.d1,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],1,0,0,0,0,0⟩ else ⟨⟨.a2,.a1,.a1,.a2,.d1,.d2,.d0,.a0,.a1,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 45 then (if i.val < 43 then ⟨⟨.a2,.a1,.a1,.a3,.d1,.d2,.d0,.a0,.a1,.a1,.a2,true,false⟩,[],1,0,0,0,0,0⟩ else (if i.val < 44 then ⟨⟨.a2,.a2,.a1,.a1,.d1,.d2,.d1,.a0,.a0,.a1,.a1,true,false⟩,[(⟨.a2,.a2,.a1,.a1⟩,43),(⟨.a2,.a2,.a1,.a2⟩,44),(⟨.a2,.a2,.a1,.a3⟩,45),(⟨.a2,.a2,.a2,.a2⟩,46),(⟨.a2,.a2,.a2,.a3⟩,47),(⟨.a2,.a2,.a3,.a2⟩,48),(⟨.a2,.a2,.a3,.a3⟩,49),(⟨.a2,.a3,.a1,.a1⟩,50),(⟨.a2,.a3,.a1,.a2⟩,51),(⟨.a2,.a3,.a1,.a3⟩,52),(⟨.a2,.a3,.a2,.a2⟩,53),(⟨.a2,.a3,.a2,.a3⟩,54),(⟨.a2,.a3,.a3,.a2⟩,55),(⟨.a2,.a3,.a3,.a3⟩,56)],0,4,8,10,2,0⟩ else ⟨⟨.a2,.a2,.a1,.a2,.d1,.d1,.d0,.a0,.a0,.a1,.a2,true,false⟩,[(⟨.a2,.a1,.a2,.a1⟩,248),(⟨.a2,.a1,.a2,.a2⟩,249),(⟨.a2,.a1,.a2,.a3⟩,250),(⟨.a2,.a2,.a2,.a3⟩,236),(⟨.a2,.a3,.a2,.a2⟩,237),(⟨.a2,.a3,.a2,.a3⟩,238)],0,1,0,0,0,0⟩)) else (if i.val < 46 then ⟨⟨.a2,.a2,.a1,.a3,.d1,.d1,.d0,.a0,.a0,.a1,.a2,true,false⟩,[(⟨.a2,.a1,.a3,.a1⟩,251),(⟨.a2,.a1,.a3,.a2⟩,252),(⟨.a2,.a1,.a3,.a3⟩,253),(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a3,.a2⟩,244)],1,2,1,1,0,0⟩ else (if i.val < 47 then ⟨⟨.a2,.a2,.a2,.a2,.d2,.d2,.d1,.a0,.a0,.a0,.a0,true,true⟩,[(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a2,.a2,.a3,.d2,.d1,.d0,.a0,.a0,.a0,.a1,true,true⟩,[(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],1,0,0,0,0,0⟩)))))) else (if i.val < 72 then (if i.val < 60 then (if i.val < 54 then (if i.val < 51 then (if i.val < 49 then ⟨⟨.a2,.a2,.a3,.a2,.d1,.d0,.d0,.a0,.a0,.a1,.a2,true,true⟩,[(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257)],0,0,0,0,0,0⟩ else (if i.val < 50 then ⟨⟨.a2,.a2,.a3,.a3,.d1,.d1,.d1,.a0,.a0,.a1,.a1,true,true⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a2,.a2⟩,209),(⟨.a2,.a3,.a2,.a3⟩,210),(⟨.a2,.a3,.a3,.a2⟩,258)],1,1,1,1,0,0⟩ else ⟨⟨.a2,.a3,.a1,.a1,.d0,.d2,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 52 then ⟨⟨.a2,.a3,.a1,.a2,.d0,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 53 then ⟨⟨.a2,.a3,.a1,.a3,.d0,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a3,.a2,.a2,.d0,.d1,.d1,.a0,.a1,.a2,.a2,true,true⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 57 then (if i.val < 55 then ⟨⟨.a2,.a3,.a2,.a3,.d0,.d0,.d0,.a0,.a1,.a2,.a3,true,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 56 then ⟨⟨.a2,.a3,.a3,.a2,.d1,.d1,.d0,.a0,.a1,.a1,.a2,true,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a3,.a3,.a3,.d1,.d2,.d1,.a0,.a1,.a1,.a1,true,true⟩,[],1,0,0,0,0,0⟩)) else (if i.val < 58 then ⟨⟨.a3,.a0,.a0,.a0,.d2,.d2,.d1,.a0,.a1,.a1,.a1,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 59 then ⟨⟨.a3,.a0,.a0,.a2,.d2,.d1,.d0,.a0,.a1,.a1,.a2,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a0,.a0,.a3,.d2,.d1,.d0,.a0,.a1,.a1,.a2,false,true⟩,[],0,0,0,0,0,0⟩)))) else (if i.val < 66 then (if i.val < 63 then (if i.val < 61 then ⟨⟨.a3,.a0,.a1,.a0,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 62 then ⟨⟨.a3,.a0,.a1,.a1,.d1,.d2,.d1,.a0,.a1,.a2,.a2,false,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a0,.a1,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 64 then ⟨⟨.a3,.a0,.a1,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 65 then ⟨⟨.a3,.a0,.a2,.a0,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a0,.a2,.a2,.d1,.d1,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 69 then (if i.val < 67 then ⟨⟨.a3,.a0,.a2,.a3,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 68 then ⟨⟨.a3,.a0,.a3,.a0,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a0,.a3,.a2,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 70 then ⟨⟨.a3,.a0,.a3,.a3,.d1,.d1,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 71 then ⟨⟨.a3,.a1,.a1,.a2,.d1,.d2,.d0,.a0,.a1,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a1,.a1,.a3,.d1,.d2,.d0,.a0,.a1,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩))))) else (if i.val < 84 then (if i.val < 78 then (if i.val < 75 then (if i.val < 73 then ⟨⟨.a3,.a2,.a1,.a1,.d0,.d2,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 74 then ⟨⟨.a3,.a2,.a1,.a2,.d0,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a2,.a1,.a3,.d0,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 76 then ⟨⟨.a3,.a2,.a2,.a2,.d1,.d2,.d1,.a0,.a1,.a1,.a1,true,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 77 then ⟨⟨.a3,.a2,.a2,.a3,.d1,.d1,.d0,.a0,.a1,.a1,.a2,true,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a2,.a3,.a2,.d0,.d0,.d0,.a0,.a1,.a2,.a3,true,true⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 81 then (if i.val < 79 then ⟨⟨.a3,.a2,.a3,.a3,.d0,.d1,.d1,.a0,.a1,.a2,.a2,true,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 80 then ⟨⟨.a3,.a3,.a1,.a1,.d1,.d2,.d1,.a0,.a0,.a1,.a1,true,false⟩,[(⟨.a3,.a2,.a1,.a1⟩,72),(⟨.a3,.a2,.a1,.a2⟩,73),(⟨.a3,.a2,.a1,.a3⟩,74),(⟨.a3,.a2,.a2,.a2⟩,75),(⟨.a3,.a2,.a2,.a3⟩,76),(⟨.a3,.a2,.a3,.a2⟩,77),(⟨.a3,.a2,.a3,.a3⟩,78),(⟨.a3,.a3,.a1,.a1⟩,79),(⟨.a3,.a3,.a1,.a2⟩,80),(⟨.a3,.a3,.a1,.a3⟩,81),(⟨.a3,.a3,.a2,.a2⟩,82),(⟨.a3,.a3,.a2,.a3⟩,83),(⟨.a3,.a3,.a3,.a2⟩,84),(⟨.a3,.a3,.a3,.a3⟩,85)],0,0,1,2,1,0⟩ else ⟨⟨.a3,.a3,.a1,.a2,.d1,.d1,.d0,.a0,.a0,.a1,.a2,true,false⟩,[(⟨.a3,.a1,.a2,.a1⟩,259),(⟨.a3,.a1,.a2,.a2⟩,260),(⟨.a3,.a1,.a2,.a3⟩,261),(⟨.a3,.a2,.a2,.a3⟩,239),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩)) else (if i.val < 82 then ⟨⟨.a3,.a3,.a1,.a3,.d1,.d1,.d0,.a0,.a0,.a1,.a2,true,false⟩,[(⟨.a3,.a1,.a3,.a1⟩,262),(⟨.a3,.a1,.a3,.a2⟩,263),(⟨.a3,.a1,.a3,.a3⟩,264),(⟨.a3,.a2,.a3,.a2⟩,245),(⟨.a3,.a2,.a3,.a3⟩,246),(⟨.a3,.a3,.a3,.a2⟩,247)],0,0,0,0,0,0⟩ else (if i.val < 83 then ⟨⟨.a3,.a3,.a2,.a2,.d1,.d1,.d1,.a0,.a0,.a1,.a1,true,true⟩,[(⟨.a3,.a2,.a2,.a3⟩,265),(⟨.a3,.a2,.a3,.a2⟩,188),(⟨.a3,.a2,.a3,.a3⟩,189),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a3,.a2,.a3,.d1,.d0,.d0,.a0,.a0,.a1,.a2,true,true⟩,[(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,0,0,0,0,0⟩)))) else (if i.val < 90 then (if i.val < 87 then (if i.val < 85 then ⟨⟨.a3,.a3,.a3,.a2,.d2,.d1,.d0,.a0,.a0,.a0,.a1,true,true⟩,[(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257)],0,0,0,0,0,0⟩ else (if i.val < 86 then ⟨⟨.a3,.a3,.a3,.a3,.d2,.d2,.d1,.a0,.a0,.a0,.a0,true,true⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243)],0,1,1,1,0,0⟩ else ⟨⟨.a0,.a0,.a0,.a0,.d2,.d2,.d1,.a0,.a0,.a0,.a0,false,true⟩,[(⟨.a2,.a2,.a0,.a0⟩,266),(⟨.a2,.a2,.a0,.a2⟩,267),(⟨.a2,.a2,.a0,.a3⟩,268),(⟨.a2,.a2,.a2,.a2⟩,46),(⟨.a2,.a2,.a2,.a3⟩,47),(⟨.a2,.a2,.a3,.a2⟩,48),(⟨.a2,.a2,.a3,.a3⟩,49),(⟨.a2,.a3,.a0,.a0⟩,269),(⟨.a2,.a3,.a0,.a2⟩,270),(⟨.a2,.a3,.a0,.a3⟩,271),(⟨.a2,.a3,.a2,.a2⟩,53),(⟨.a2,.a3,.a2,.a3⟩,54),(⟨.a2,.a3,.a3,.a2⟩,55),(⟨.a2,.a3,.a3,.a3⟩,56),(⟨.a3,.a2,.a0,.a0⟩,272),(⟨.a3,.a2,.a0,.a2⟩,273),(⟨.a3,.a2,.a0,.a3⟩,274),(⟨.a3,.a2,.a2,.a2⟩,75),(⟨.a3,.a2,.a2,.a3⟩,76),(⟨.a3,.a2,.a3,.a2⟩,77),(⟨.a3,.a2,.a3,.a3⟩,78),(⟨.a3,.a3,.a0,.a0⟩,275),(⟨.a3,.a3,.a0,.a2⟩,276),(⟨.a3,.a3,.a0,.a3⟩,277),(⟨.a3,.a3,.a2,.a2⟩,82),(⟨.a3,.a3,.a2,.a3⟩,83),(⟨.a3,.a3,.a3,.a2⟩,84),(⟨.a3,.a3,.a3,.a3⟩,85)],0,4,9,12,3,0⟩)) else (if i.val < 88 then ⟨⟨.a0,.a0,.a0,.a2,.d2,.d1,.d0,.a0,.a0,.a0,.a1,false,true⟩,[(⟨.a2,.a0,.a2,.a0⟩,278),(⟨.a2,.a0,.a2,.a2⟩,279),(⟨.a2,.a0,.a2,.a3⟩,280),(⟨.a2,.a2,.a2,.a3⟩,236),(⟨.a2,.a3,.a2,.a2⟩,237),(⟨.a2,.a3,.a2,.a3⟩,238),(⟨.a3,.a0,.a2,.a0⟩,281),(⟨.a3,.a0,.a2,.a2⟩,282),(⟨.a3,.a0,.a2,.a3⟩,283),(⟨.a3,.a2,.a2,.a3⟩,239),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,1,0,0,0,0⟩ else (if i.val < 89 then ⟨⟨.a0,.a0,.a0,.a3,.d2,.d1,.d0,.a0,.a0,.a0,.a1,false,true⟩,[(⟨.a2,.a0,.a3,.a0⟩,284),(⟨.a2,.a0,.a3,.a2⟩,285),(⟨.a2,.a0,.a3,.a3⟩,286),(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a3,.a2⟩,244),(⟨.a3,.a0,.a3,.a0⟩,287),(⟨.a3,.a0,.a3,.a2⟩,288),(⟨.a3,.a0,.a3,.a3⟩,289),(⟨.a3,.a2,.a3,.a2⟩,245),(⟨.a3,.a2,.a3,.a3⟩,246),(⟨.a3,.a3,.a3,.a2⟩,247)],0,2,1,1,0,0⟩ else ⟨⟨.a0,.a0,.a1,.a0,.d1,.d1,.d0,.a0,.a0,.a1,.a2,false,false⟩,[(⟨.a0,.a0,.a0,.a2⟩,290),(⟨.a0,.a0,.a0,.a3⟩,291),(⟨.a0,.a1,.a0,.a0⟩,292),(⟨.a0,.a1,.a0,.a1⟩,293),(⟨.a0,.a1,.a0,.a2⟩,294),(⟨.a0,.a1,.a0,.a3⟩,295),(⟨.a0,.a2,.a0,.a0⟩,296),(⟨.a0,.a2,.a0,.a2⟩,297),(⟨.a0,.a2,.a0,.a3⟩,298),(⟨.a0,.a3,.a0,.a0⟩,299),(⟨.a0,.a3,.a0,.a2⟩,300),(⟨.a0,.a3,.a0,.a3⟩,301)],0,0,2,1,0,0⟩))) else (if i.val < 93 then (if i.val < 91 then ⟨⟨.a0,.a0,.a1,.a1,.d1,.d2,.d1,.a0,.a0,.a1,.a1,false,false⟩,[(⟨.a0,.a0,.a0,.a0⟩,86),(⟨.a0,.a0,.a0,.a2⟩,87),(⟨.a0,.a0,.a0,.a3⟩,88),(⟨.a0,.a0,.a1,.a0⟩,89),(⟨.a0,.a0,.a1,.a1⟩,90),(⟨.a0,.a0,.a1,.a2⟩,91),(⟨.a0,.a0,.a1,.a3⟩,92),(⟨.a0,.a0,.a2,.a0⟩,93),(⟨.a0,.a0,.a2,.a2⟩,94),(⟨.a0,.a0,.a2,.a3⟩,95),(⟨.a0,.a0,.a3,.a0⟩,96),(⟨.a0,.a0,.a3,.a2⟩,97),(⟨.a0,.a0,.a3,.a3⟩,98),(⟨.a0,.a2,.a0,.a0⟩,114),(⟨.a0,.a2,.a0,.a2⟩,115),(⟨.a0,.a2,.a0,.a3⟩,116),(⟨.a0,.a2,.a1,.a0⟩,117),(⟨.a0,.a2,.a1,.a1⟩,118),(⟨.a0,.a2,.a1,.a2⟩,119),(⟨.a0,.a2,.a1,.a3⟩,120),(⟨.a0,.a2,.a2,.a0⟩,121),(⟨.a0,.a2,.a2,.a2⟩,122),(⟨.a0,.a2,.a2,.a3⟩,123),(⟨.a0,.a2,.a3,.a0⟩,124),(⟨.a0,.a2,.a3,.a2⟩,125),(⟨.a0,.a2,.a3,.a3⟩,126),(⟨.a0,.a3,.a0,.a0⟩,127),(⟨.a0,.a3,.a0,.a2⟩,128),(⟨.a0,.a3,.a0,.a3⟩,129),(⟨.a0,.a3,.a1,.a0⟩,130),(⟨.a0,.a3,.a1,.a1⟩,131),(⟨.a0,.a3,.a1,.a2⟩,132),(⟨.a0,.a3,.a1,.a3⟩,133),(⟨.a0,.a3,.a2,.a0⟩,134),(⟨.a0,.a3,.a2,.a2⟩,135),(⟨.a0,.a3,.a2,.a3⟩,136),(⟨.a0,.a3,.a3,.a0⟩,137),(⟨.a0,.a3,.a3,.a2⟩,138),(⟨.a0,.a3,.a3,.a3⟩,139),(⟨.a1,.a2,.a1,.a1⟩,22),(⟨.a1,.a2,.a1,.a2⟩,23),(⟨.a1,.a2,.a1,.a3⟩,24),(⟨.a1,.a3,.a1,.a1⟩,25),(⟨.a1,.a3,.a1,.a2⟩,26),(⟨.a1,.a3,.a1,.a3⟩,27),(⟨.a2,.a2,.a1,.a1⟩,43),(⟨.a2,.a2,.a1,.a2⟩,44),(⟨.a2,.a2,.a1,.a3⟩,45),(⟨.a2,.a2,.a2,.a2⟩,46),(⟨.a2,.a2,.a2,.a3⟩,47),(⟨.a2,.a2,.a3,.a2⟩,48),(⟨.a2,.a2,.a3,.a3⟩,49),(⟨.a2,.a3,.a1,.a1⟩,50),(⟨.a2,.a3,.a1,.a2⟩,51),(⟨.a2,.a3,.a1,.a3⟩,52),(⟨.a2,.a3,.a2,.a2⟩,53),(⟨.a2,.a3,.a2,.a3⟩,54),(⟨.a2,.a3,.a3,.a2⟩,55),(⟨.a2,.a3,.a3,.a3⟩,56),(⟨.a3,.a2,.a1,.a1⟩,72),(⟨.a3,.a2,.a1,.a2⟩,73),(⟨.a3,.a2,.a1,.a3⟩,74),(⟨.a3,.a2,.a2,.a2⟩,75),(⟨.a3,.a2,.a2,.a3⟩,76),(⟨.a3,.a2,.a3,.a2⟩,77),(⟨.a3,.a2,.a3,.a3⟩,78),(⟨.a3,.a3,.a1,.a1⟩,79),(⟨.a3,.a3,.a1,.a2⟩,80),(⟨.a3,.a3,.a1,.a3⟩,81),(⟨.a3,.a3,.a2,.a2⟩,82),(⟨.a3,.a3,.a2,.a3⟩,83),(⟨.a3,.a3,.a3,.a2⟩,84),(⟨.a3,.a3,.a3,.a3⟩,85)],0,4,37,88,58,9⟩ else (if i.val < 92 then ⟨⟨.a0,.a0,.a1,.a2,.d1,.d1,.d0,.a0,.a0,.a1,.a2,false,false⟩,[(⟨.a0,.a0,.a2,.a0⟩,302),(⟨.a0,.a0,.a2,.a2⟩,303),(⟨.a0,.a0,.a2,.a3⟩,304),(⟨.a0,.a1,.a2,.a0⟩,305),(⟨.a0,.a1,.a2,.a1⟩,306),(⟨.a0,.a1,.a2,.a2⟩,307),(⟨.a0,.a1,.a2,.a3⟩,308),(⟨.a0,.a2,.a2,.a0⟩,309),(⟨.a0,.a2,.a2,.a3⟩,310),(⟨.a0,.a3,.a2,.a0⟩,311),(⟨.a0,.a3,.a2,.a2⟩,312),(⟨.a0,.a3,.a2,.a3⟩,313),(⟨.a1,.a1,.a2,.a1⟩,314),(⟨.a1,.a1,.a2,.a2⟩,315),(⟨.a1,.a1,.a2,.a3⟩,316),(⟨.a2,.a1,.a2,.a1⟩,248),(⟨.a2,.a1,.a2,.a2⟩,249),(⟨.a2,.a1,.a2,.a3⟩,250),(⟨.a2,.a2,.a2,.a3⟩,236),(⟨.a2,.a3,.a2,.a2⟩,237),(⟨.a2,.a3,.a2,.a3⟩,238),(⟨.a3,.a1,.a2,.a1⟩,259),(⟨.a3,.a1,.a2,.a2⟩,260),(⟨.a3,.a1,.a2,.a3⟩,261),(⟨.a3,.a2,.a2,.a3⟩,239),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,1,3,4,2,0⟩ else ⟨⟨.a0,.a0,.a1,.a3,.d1,.d1,.d0,.a0,.a0,.a1,.a2,false,false⟩,[(⟨.a0,.a0,.a3,.a0⟩,317),(⟨.a0,.a0,.a3,.a2⟩,318),(⟨.a0,.a0,.a3,.a3⟩,319),(⟨.a0,.a1,.a3,.a0⟩,320),(⟨.a0,.a1,.a3,.a1⟩,321),(⟨.a0,.a1,.a3,.a2⟩,322),(⟨.a0,.a1,.a3,.a3⟩,323),(⟨.a0,.a2,.a3,.a0⟩,324),(⟨.a0,.a2,.a3,.a2⟩,325),(⟨.a0,.a2,.a3,.a3⟩,326),(⟨.a0,.a3,.a3,.a0⟩,327),(⟨.a0,.a3,.a3,.a2⟩,328),(⟨.a1,.a1,.a3,.a1⟩,329),(⟨.a1,.a1,.a3,.a2⟩,330),(⟨.a1,.a1,.a3,.a3⟩,331),(⟨.a2,.a1,.a3,.a1⟩,251),(⟨.a2,.a1,.a3,.a2⟩,252),(⟨.a2,.a1,.a3,.a3⟩,253),(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a3,.a2⟩,244),(⟨.a3,.a1,.a3,.a1⟩,262),(⟨.a3,.a1,.a3,.a2⟩,263),(⟨.a3,.a1,.a3,.a3⟩,264),(⟨.a3,.a2,.a3,.a2⟩,245),(⟨.a3,.a2,.a3,.a3⟩,246),(⟨.a3,.a3,.a3,.a2⟩,247)],0,2,5,9,4,0⟩)) else (if i.val < 95 then (if i.val < 94 then ⟨⟨.a0,.a0,.a2,.a0,.d1,.d0,.d0,.a0,.a0,.a1,.a2,false,true⟩,[(⟨.a0,.a2,.a0,.a0⟩,332),(⟨.a0,.a2,.a0,.a2⟩,333),(⟨.a0,.a2,.a0,.a3⟩,334)],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a0,.a2,.a2,.d1,.d1,.d1,.a0,.a0,.a1,.a1,false,true⟩,[(⟨.a0,.a0,.a2,.a0⟩,302),(⟨.a0,.a0,.a2,.a2⟩,303),(⟨.a0,.a0,.a2,.a3⟩,304),(⟨.a0,.a2,.a0,.a0⟩,162),(⟨.a0,.a2,.a0,.a2⟩,163),(⟨.a0,.a2,.a0,.a3⟩,164),(⟨.a0,.a2,.a2,.a0⟩,335),(⟨.a0,.a2,.a2,.a3⟩,336),(⟨.a0,.a2,.a3,.a0⟩,172),(⟨.a0,.a2,.a3,.a2⟩,173),(⟨.a0,.a2,.a3,.a3⟩,174),(⟨.a0,.a3,.a2,.a0⟩,311),(⟨.a0,.a3,.a2,.a2⟩,312),(⟨.a0,.a3,.a2,.a3⟩,313),(⟨.a2,.a2,.a3,.a2⟩,181),(⟨.a2,.a2,.a3,.a3⟩,182),(⟨.a2,.a3,.a2,.a2⟩,237),(⟨.a2,.a3,.a2,.a3⟩,238),(⟨.a3,.a2,.a2,.a3⟩,265),(⟨.a3,.a2,.a3,.a2⟩,188),(⟨.a3,.a2,.a3,.a3⟩,189),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,1,2,3,1,0⟩) else (if i.val < 96 then ⟨⟨.a0,.a0,.a2,.a3,.d1,.d0,.d0,.a0,.a0,.a1,.a2,false,true⟩,[(⟨.a0,.a2,.a3,.a0⟩,337),(⟨.a0,.a2,.a3,.a2⟩,338),(⟨.a0,.a2,.a3,.a3⟩,339),(⟨.a2,.a2,.a3,.a2⟩,340),(⟨.a2,.a2,.a3,.a3⟩,341),(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,1,1,1,0,0⟩ else ⟨⟨.a0,.a0,.a3,.a0,.d1,.d0,.d0,.a0,.a0,.a1,.a2,false,true⟩,[(⟨.a0,.a3,.a0,.a0⟩,342),(⟨.a0,.a3,.a0,.a2⟩,343),(⟨.a0,.a3,.a0,.a3⟩,344)],0,0,0,0,0,0⟩))))))) else (if i.val < 146 then (if i.val < 121 then (if i.val < 109 then (if i.val < 103 then (if i.val < 100 then (if i.val < 98 then ⟨⟨.a0,.a0,.a3,.a2,.d1,.d0,.d0,.a0,.a0,.a1,.a2,false,true⟩,[(⟨.a0,.a3,.a2,.a0⟩,345),(⟨.a0,.a3,.a2,.a2⟩,346),(⟨.a0,.a3,.a2,.a3⟩,347),(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257),(⟨.a3,.a3,.a2,.a2⟩,348),(⟨.a3,.a3,.a2,.a3⟩,349)],0,0,0,0,0,0⟩ else (if i.val < 99 then ⟨⟨.a0,.a0,.a3,.a3,.d1,.d1,.d1,.a0,.a0,.a1,.a1,false,true⟩,[(⟨.a0,.a0,.a3,.a0⟩,317),(⟨.a0,.a0,.a3,.a2⟩,318),(⟨.a0,.a0,.a3,.a3⟩,319),(⟨.a0,.a2,.a3,.a0⟩,324),(⟨.a0,.a2,.a3,.a2⟩,325),(⟨.a0,.a2,.a3,.a3⟩,326),(⟨.a0,.a3,.a0,.a0⟩,190),(⟨.a0,.a3,.a0,.a2⟩,191),(⟨.a0,.a3,.a0,.a3⟩,192),(⟨.a0,.a3,.a2,.a0⟩,197),(⟨.a0,.a3,.a2,.a2⟩,198),(⟨.a0,.a3,.a2,.a3⟩,199),(⟨.a0,.a3,.a3,.a0⟩,350),(⟨.a0,.a3,.a3,.a2⟩,351),(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a2,.a2⟩,209),(⟨.a2,.a3,.a2,.a3⟩,210),(⟨.a2,.a3,.a3,.a2⟩,258),(⟨.a3,.a2,.a3,.a2⟩,245),(⟨.a3,.a2,.a3,.a3⟩,246),(⟨.a3,.a3,.a2,.a2⟩,216),(⟨.a3,.a3,.a2,.a3⟩,217)],0,1,3,5,2,0⟩ else ⟨⟨.a0,.a1,.a0,.a0,.d1,.d1,.d1,.a0,.a1,.a2,.a2,false,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 101 then ⟨⟨.a0,.a1,.a0,.a1,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 102 then ⟨⟨.a0,.a1,.a0,.a2,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a1,.a0,.a3,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 106 then (if i.val < 104 then ⟨⟨.a0,.a1,.a1,.a0,.d2,.d2,.d0,.a0,.a1,.a1,.a2,false,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 105 then ⟨⟨.a0,.a1,.a1,.a2,.d2,.d2,.d0,.a0,.a1,.a1,.a2,false,false⟩,[(⟨.a2,.a2,.a2,.a3⟩,236),(⟨.a2,.a3,.a2,.a2⟩,237),(⟨.a2,.a3,.a2,.a3⟩,238),(⟨.a3,.a2,.a2,.a3⟩,239),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,1,0,0,0,0⟩ else ⟨⟨.a0,.a1,.a1,.a3,.d2,.d2,.d0,.a0,.a1,.a1,.a2,false,false⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a3,.a2⟩,244),(⟨.a3,.a2,.a3,.a2⟩,245),(⟨.a3,.a2,.a3,.a3⟩,246),(⟨.a3,.a3,.a3,.a2⟩,247)],0,1,1,1,0,0⟩)) else (if i.val < 107 then ⟨⟨.a0,.a1,.a2,.a0,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 108 then ⟨⟨.a0,.a1,.a2,.a1,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a1,.a2,.a1,.a1⟩,175),(⟨.a1,.a2,.a1,.a2⟩,176),(⟨.a1,.a2,.a1,.a3⟩,177)],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a1,.a2,.a2,.d1,.d1,.d1,.a0,.a1,.a2,.a2,false,false⟩,[(⟨.a1,.a1,.a2,.a1⟩,352),(⟨.a1,.a1,.a2,.a2⟩,353),(⟨.a1,.a1,.a2,.a3⟩,354),(⟨.a1,.a2,.a1,.a1⟩,355),(⟨.a1,.a2,.a1,.a2⟩,356),(⟨.a1,.a2,.a1,.a3⟩,357),(⟨.a1,.a2,.a2,.a1⟩,358),(⟨.a1,.a2,.a2,.a3⟩,359),(⟨.a1,.a2,.a3,.a1⟩,360),(⟨.a1,.a2,.a3,.a2⟩,361),(⟨.a1,.a2,.a3,.a3⟩,362),(⟨.a1,.a3,.a2,.a1⟩,363),(⟨.a1,.a3,.a2,.a2⟩,364),(⟨.a1,.a3,.a2,.a3⟩,365),(⟨.a2,.a2,.a3,.a2⟩,181),(⟨.a2,.a2,.a3,.a3⟩,182),(⟨.a2,.a3,.a2,.a2⟩,237),(⟨.a2,.a3,.a2,.a3⟩,238),(⟨.a3,.a2,.a2,.a3⟩,265),(⟨.a3,.a2,.a3,.a2⟩,188),(⟨.a3,.a2,.a3,.a3⟩,189),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,1,2,3,1,0⟩)))) else (if i.val < 115 then (if i.val < 112 then (if i.val < 110 then ⟨⟨.a0,.a1,.a2,.a3,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a1,.a2,.a3,.a1⟩,366),(⟨.a1,.a2,.a3,.a2⟩,367),(⟨.a1,.a2,.a3,.a3⟩,368),(⟨.a2,.a2,.a3,.a2⟩,340),(⟨.a2,.a2,.a3,.a3⟩,341),(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,1,1,1,0,0⟩ else (if i.val < 111 then ⟨⟨.a0,.a1,.a3,.a0,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a1,.a3,.a1,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a1,.a3,.a1,.a1⟩,203),(⟨.a1,.a3,.a1,.a2⟩,204),(⟨.a1,.a3,.a1,.a3⟩,205)],0,0,0,0,0,0⟩)) else (if i.val < 113 then ⟨⟨.a0,.a1,.a3,.a2,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a1,.a3,.a2,.a1⟩,369),(⟨.a1,.a3,.a2,.a2⟩,370),(⟨.a1,.a3,.a2,.a3⟩,371),(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257),(⟨.a3,.a3,.a2,.a2⟩,348),(⟨.a3,.a3,.a2,.a3⟩,349)],0,0,0,0,0,0⟩ else (if i.val < 114 then ⟨⟨.a0,.a1,.a3,.a3,.d1,.d1,.d1,.a0,.a1,.a2,.a2,false,false⟩,[(⟨.a1,.a1,.a3,.a1⟩,372),(⟨.a1,.a1,.a3,.a2⟩,373),(⟨.a1,.a1,.a3,.a3⟩,374),(⟨.a1,.a2,.a3,.a1⟩,375),(⟨.a1,.a2,.a3,.a2⟩,376),(⟨.a1,.a2,.a3,.a3⟩,377),(⟨.a1,.a3,.a1,.a1⟩,378),(⟨.a1,.a3,.a1,.a2⟩,379),(⟨.a1,.a3,.a1,.a3⟩,380),(⟨.a1,.a3,.a2,.a1⟩,381),(⟨.a1,.a3,.a2,.a2⟩,382),(⟨.a1,.a3,.a2,.a3⟩,383),(⟨.a1,.a3,.a3,.a1⟩,384),(⟨.a1,.a3,.a3,.a2⟩,385),(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a2,.a2⟩,209),(⟨.a2,.a3,.a2,.a3⟩,210),(⟨.a2,.a3,.a3,.a2⟩,258),(⟨.a3,.a2,.a3,.a2⟩,245),(⟨.a3,.a2,.a3,.a3⟩,246),(⟨.a3,.a3,.a2,.a2⟩,216),(⟨.a3,.a3,.a2,.a3⟩,217)],0,1,3,5,2,0⟩ else ⟨⟨.a0,.a2,.a0,.a0,.d0,.d1,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 118 then (if i.val < 116 then ⟨⟨.a0,.a2,.a0,.a2,.d0,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 117 then ⟨⟨.a0,.a2,.a0,.a3,.d0,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a2,.a1,.a0,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 119 then ⟨⟨.a0,.a2,.a1,.a1,.d0,.d2,.d1,.a0,.a1,.a2,.a2,false,false⟩,[(⟨.a2,.a2,.a1,.a1⟩,43),(⟨.a2,.a2,.a1,.a2⟩,44),(⟨.a2,.a2,.a1,.a3⟩,45),(⟨.a2,.a2,.a2,.a2⟩,46),(⟨.a2,.a2,.a2,.a3⟩,47),(⟨.a2,.a2,.a3,.a2⟩,48),(⟨.a2,.a2,.a3,.a3⟩,49),(⟨.a2,.a3,.a1,.a1⟩,50),(⟨.a2,.a3,.a1,.a2⟩,51),(⟨.a2,.a3,.a1,.a3⟩,52),(⟨.a2,.a3,.a2,.a2⟩,53),(⟨.a2,.a3,.a2,.a3⟩,54),(⟨.a2,.a3,.a3,.a2⟩,55),(⟨.a2,.a3,.a3,.a3⟩,56)],0,4,8,10,2,0⟩ else (if i.val < 120 then ⟨⟨.a0,.a2,.a1,.a2,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a2,.a1,.a2,.a1⟩,248),(⟨.a2,.a1,.a2,.a2⟩,249),(⟨.a2,.a1,.a2,.a3⟩,250),(⟨.a2,.a2,.a2,.a3⟩,236),(⟨.a2,.a3,.a2,.a2⟩,237),(⟨.a2,.a3,.a2,.a3⟩,238)],0,1,0,0,0,0⟩ else ⟨⟨.a0,.a2,.a1,.a3,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a2,.a1,.a3,.a1⟩,251),(⟨.a2,.a1,.a3,.a2⟩,252),(⟨.a2,.a1,.a3,.a3⟩,253),(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a3,.a2⟩,244)],0,2,1,1,0,0⟩))))) else (if i.val < 133 then (if i.val < 127 then (if i.val < 124 then (if i.val < 122 then ⟨⟨.a0,.a2,.a2,.a0,.d1,.d1,.d0,.a0,.a1,.a1,.a2,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 123 then ⟨⟨.a0,.a2,.a2,.a2,.d1,.d2,.d1,.a0,.a1,.a1,.a1,false,true⟩,[(⟨.a2,.a3,.a2,.a2⟩,386),(⟨.a2,.a3,.a2,.a3⟩,387),(⟨.a2,.a3,.a3,.a2⟩,55),(⟨.a2,.a3,.a3,.a3⟩,56),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,1,0,0,0,0⟩ else ⟨⟨.a0,.a2,.a2,.a3,.d1,.d1,.d0,.a0,.a1,.a1,.a2,false,true⟩,[(⟨.a2,.a2,.a3,.a2⟩,340),(⟨.a2,.a2,.a3,.a3⟩,341),(⟨.a2,.a3,.a3,.a2⟩,244),(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,1,0,0,0,0⟩)) else (if i.val < 125 then ⟨⟨.a0,.a2,.a3,.a0,.d0,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 126 then ⟨⟨.a0,.a2,.a3,.a2,.d0,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257)],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a2,.a3,.a3,.d0,.d1,.d1,.a0,.a1,.a2,.a2,false,true⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a2,.a2⟩,209),(⟨.a2,.a3,.a2,.a3⟩,210),(⟨.a2,.a3,.a3,.a2⟩,258)],0,1,1,1,0,0⟩))) else (if i.val < 130 then (if i.val < 128 then ⟨⟨.a0,.a3,.a0,.a0,.d0,.d1,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 129 then ⟨⟨.a0,.a3,.a0,.a2,.d0,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a3,.a0,.a3,.d0,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 131 then ⟨⟨.a0,.a3,.a1,.a0,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 132 then ⟨⟨.a0,.a3,.a1,.a1,.d0,.d2,.d1,.a0,.a1,.a2,.a2,false,false⟩,[(⟨.a3,.a2,.a1,.a1⟩,72),(⟨.a3,.a2,.a1,.a2⟩,73),(⟨.a3,.a2,.a1,.a3⟩,74),(⟨.a3,.a2,.a2,.a2⟩,75),(⟨.a3,.a2,.a2,.a3⟩,76),(⟨.a3,.a2,.a3,.a2⟩,77),(⟨.a3,.a2,.a3,.a3⟩,78),(⟨.a3,.a3,.a1,.a1⟩,79),(⟨.a3,.a3,.a1,.a2⟩,80),(⟨.a3,.a3,.a1,.a3⟩,81),(⟨.a3,.a3,.a2,.a2⟩,82),(⟨.a3,.a3,.a2,.a3⟩,83),(⟨.a3,.a3,.a3,.a2⟩,84),(⟨.a3,.a3,.a3,.a3⟩,85)],0,0,1,2,1,0⟩ else ⟨⟨.a0,.a3,.a1,.a2,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a3,.a1,.a2,.a1⟩,259),(⟨.a3,.a1,.a2,.a2⟩,260),(⟨.a3,.a1,.a2,.a3⟩,261),(⟨.a3,.a2,.a2,.a3⟩,239),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩)))) else (if i.val < 139 then (if i.val < 136 then (if i.val < 134 then ⟨⟨.a0,.a3,.a1,.a3,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a3,.a1,.a3,.a1⟩,262),(⟨.a3,.a1,.a3,.a2⟩,263),(⟨.a3,.a1,.a3,.a3⟩,264),(⟨.a3,.a2,.a3,.a2⟩,245),(⟨.a3,.a2,.a3,.a3⟩,246),(⟨.a3,.a3,.a3,.a2⟩,247)],0,0,0,0,0,0⟩ else (if i.val < 135 then ⟨⟨.a0,.a3,.a2,.a0,.d0,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a3,.a2,.a2,.d0,.d1,.d1,.a0,.a1,.a2,.a2,false,true⟩,[(⟨.a3,.a2,.a2,.a3⟩,265),(⟨.a3,.a2,.a3,.a2⟩,188),(⟨.a3,.a2,.a3,.a3⟩,189),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩)) else (if i.val < 137 then ⟨⟨.a0,.a3,.a2,.a3,.d0,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,0,0,0,0,0⟩ else (if i.val < 138 then ⟨⟨.a0,.a3,.a3,.a0,.d1,.d1,.d0,.a0,.a1,.a1,.a2,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a3,.a3,.a2,.d1,.d1,.d0,.a0,.a1,.a1,.a2,false,true⟩,[(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257),(⟨.a3,.a2,.a2,.a3⟩,239),(⟨.a3,.a3,.a2,.a2⟩,348),(⟨.a3,.a3,.a2,.a3⟩,349)],0,0,0,0,0,0⟩))) else (if i.val < 142 then (if i.val < 140 then ⟨⟨.a0,.a3,.a3,.a3,.d1,.d2,.d1,.a0,.a1,.a1,.a1,false,true⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a3,.a2,.a2,.a2⟩,75),(⟨.a3,.a2,.a2,.a3⟩,76),(⟨.a3,.a2,.a3,.a2⟩,388),(⟨.a3,.a2,.a3,.a3⟩,389)],0,1,2,2,0,0⟩ else (if i.val < 141 then ⟨⟨.a1,.a1,.a2,.a1,.d2,.d0,.d0,.a0,.a0,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a1,.a2,.a2,.d2,.d1,.d1,.a0,.a0,.a1,.a1,true,false⟩,[(⟨.a2,.a2,.a3,.a2⟩,181),(⟨.a2,.a2,.a3,.a3⟩,182),(⟨.a2,.a3,.a2,.a2⟩,237),(⟨.a2,.a3,.a2,.a3⟩,238),(⟨.a3,.a2,.a2,.a3⟩,265),(⟨.a3,.a2,.a3,.a2⟩,188),(⟨.a3,.a2,.a3,.a3⟩,189),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,1,0,0,0,0⟩)) else (if i.val < 144 then (if i.val < 143 then ⟨⟨.a1,.a1,.a2,.a3,.d2,.d0,.d0,.a0,.a0,.a1,.a2,true,false⟩,[(⟨.a2,.a2,.a3,.a2⟩,340),(⟨.a2,.a2,.a3,.a3⟩,341),(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,1,0,0,0,0⟩ else ⟨⟨.a1,.a1,.a3,.a1,.d2,.d0,.d0,.a0,.a0,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩) else (if i.val < 145 then ⟨⟨.a1,.a1,.a3,.a2,.d2,.d0,.d0,.a0,.a0,.a1,.a2,true,false⟩,[(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257),(⟨.a3,.a3,.a2,.a2⟩,348),(⟨.a3,.a3,.a2,.a3⟩,349)],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a1,.a3,.a3,.d2,.d1,.d1,.a0,.a0,.a1,.a1,true,false⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a2,.a2⟩,209),(⟨.a2,.a3,.a2,.a3⟩,210),(⟨.a2,.a3,.a3,.a2⟩,258),(⟨.a3,.a2,.a3,.a2⟩,245),(⟨.a3,.a2,.a3,.a3⟩,246),(⟨.a3,.a3,.a2,.a2⟩,216),(⟨.a3,.a3,.a2,.a3⟩,217)],0,1,1,1,0,0⟩)))))) else (if i.val < 170 then (if i.val < 158 then (if i.val < 152 then (if i.val < 149 then (if i.val < 147 then ⟨⟨.a2,.a1,.a1,.a2,.d2,.d2,.d0,.a0,.a1,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 148 then ⟨⟨.a2,.a1,.a1,.a3,.d2,.d2,.d0,.a0,.a1,.a1,.a2,true,false⟩,[],1,0,0,0,0,0⟩ else ⟨⟨.a2,.a1,.a2,.a1,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 150 then ⟨⟨.a2,.a1,.a2,.a2,.d1,.d1,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 151 then ⟨⟨.a2,.a1,.a2,.a3,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a1,.a3,.a1,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 155 then (if i.val < 153 then ⟨⟨.a2,.a1,.a3,.a2,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 154 then ⟨⟨.a2,.a1,.a3,.a3,.d1,.d1,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],1,0,0,0,0,0⟩ else ⟨⟨.a3,.a1,.a1,.a2,.d2,.d2,.d0,.a0,.a1,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 156 then ⟨⟨.a3,.a1,.a1,.a3,.d2,.d2,.d0,.a0,.a1,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 157 then ⟨⟨.a3,.a1,.a2,.a1,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a1,.a2,.a2,.d1,.d1,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],0,0,0,0,0,0⟩)))) else (if i.val < 164 then (if i.val < 161 then (if i.val < 159 then ⟨⟨.a3,.a1,.a2,.a3,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 160 then ⟨⟨.a3,.a1,.a3,.a1,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a1,.a3,.a2,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 162 then ⟨⟨.a3,.a1,.a3,.a3,.d1,.d1,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 163 then ⟨⟨.a0,.a2,.a0,.a0,.d1,.d1,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a2,.a0,.a2,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 167 then (if i.val < 165 then ⟨⟨.a0,.a2,.a0,.a3,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 166 then ⟨⟨.a0,.a2,.a1,.a0,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a2,.a1,.a1,.d1,.d2,.d1,.a0,.a1,.a2,.a2,false,false⟩,[(⟨.a2,.a2,.a1,.a1⟩,43),(⟨.a2,.a2,.a1,.a2⟩,44),(⟨.a2,.a2,.a1,.a3⟩,45),(⟨.a2,.a2,.a2,.a2⟩,46),(⟨.a2,.a2,.a2,.a3⟩,47),(⟨.a2,.a2,.a3,.a2⟩,48),(⟨.a2,.a2,.a3,.a3⟩,49),(⟨.a2,.a3,.a1,.a1⟩,50),(⟨.a2,.a3,.a1,.a2⟩,51),(⟨.a2,.a3,.a1,.a3⟩,52),(⟨.a2,.a3,.a2,.a2⟩,53),(⟨.a2,.a3,.a2,.a3⟩,54),(⟨.a2,.a3,.a3,.a2⟩,55),(⟨.a2,.a3,.a3,.a3⟩,56)],0,4,8,10,2,0⟩)) else (if i.val < 168 then ⟨⟨.a0,.a2,.a1,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a2,.a1,.a2,.a1⟩,248),(⟨.a2,.a1,.a2,.a2⟩,249),(⟨.a2,.a1,.a2,.a3⟩,250),(⟨.a2,.a2,.a2,.a3⟩,236),(⟨.a2,.a3,.a2,.a2⟩,237),(⟨.a2,.a3,.a2,.a3⟩,238)],0,1,0,0,0,0⟩ else (if i.val < 169 then ⟨⟨.a0,.a2,.a1,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a2,.a1,.a3,.a1⟩,251),(⟨.a2,.a1,.a3,.a2⟩,252),(⟨.a2,.a1,.a3,.a3⟩,253),(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a3,.a2⟩,244)],0,2,1,1,0,0⟩ else ⟨⟨.a0,.a2,.a2,.a0,.d2,.d1,.d0,.a0,.a1,.a1,.a2,false,true⟩,[],0,0,0,0,0,0⟩))))) else (if i.val < 182 then (if i.val < 176 then (if i.val < 173 then (if i.val < 171 then ⟨⟨.a0,.a2,.a2,.a2,.d2,.d2,.d1,.a0,.a1,.a1,.a1,false,true⟩,[(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩ else (if i.val < 172 then ⟨⟨.a0,.a2,.a2,.a3,.d2,.d1,.d0,.a0,.a1,.a1,.a2,false,true⟩,[(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a2,.a3,.a0,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 174 then ⟨⟨.a0,.a2,.a3,.a2,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257)],0,0,0,0,0,0⟩ else (if i.val < 175 then ⟨⟨.a0,.a2,.a3,.a3,.d1,.d1,.d1,.a0,.a1,.a2,.a2,false,true⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a2,.a2⟩,209),(⟨.a2,.a3,.a2,.a3⟩,210),(⟨.a2,.a3,.a3,.a2⟩,258)],0,1,1,1,0,0⟩ else ⟨⟨.a1,.a2,.a1,.a1,.d1,.d2,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 179 then (if i.val < 177 then ⟨⟨.a1,.a2,.a1,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 178 then ⟨⟨.a1,.a2,.a1,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a2,.a1,.a1,.d2,.d2,.d1,.a0,.a0,.a1,.a1,true,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 180 then ⟨⟨.a2,.a2,.a1,.a2,.d2,.d1,.d0,.a0,.a0,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 181 then ⟨⟨.a2,.a2,.a1,.a3,.d2,.d1,.d0,.a0,.a0,.a1,.a2,true,false⟩,[],1,0,0,0,0,0⟩ else ⟨⟨.a2,.a2,.a3,.a2,.d2,.d0,.d0,.a0,.a0,.a1,.a2,true,true⟩,[],0,0,0,0,0,0⟩)))) else (if i.val < 188 then (if i.val < 185 then (if i.val < 183 then ⟨⟨.a2,.a2,.a3,.a3,.d2,.d1,.d1,.a0,.a0,.a1,.a1,true,true⟩,[],1,0,0,0,0,0⟩ else (if i.val < 184 then ⟨⟨.a3,.a2,.a1,.a1,.d1,.d2,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a2,.a1,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 186 then ⟨⟨.a3,.a2,.a1,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 187 then ⟨⟨.a3,.a2,.a2,.a2,.d2,.d2,.d1,.a0,.a1,.a1,.a1,true,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a2,.a2,.a3,.d2,.d1,.d0,.a0,.a1,.a1,.a2,true,true⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 191 then (if i.val < 189 then ⟨⟨.a3,.a2,.a3,.a2,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 190 then ⟨⟨.a3,.a2,.a3,.a3,.d1,.d1,.d1,.a0,.a1,.a2,.a2,true,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a3,.a0,.a0,.d1,.d1,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 193 then (if i.val < 192 then ⟨⟨.a0,.a3,.a0,.a2,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a3,.a0,.a3,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩) else (if i.val < 194 then ⟨⟨.a0,.a3,.a1,.a0,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a3,.a1,.a1,.d1,.d2,.d1,.a0,.a1,.a2,.a2,false,false⟩,[(⟨.a3,.a2,.a1,.a1⟩,72),(⟨.a3,.a2,.a1,.a2⟩,73),(⟨.a3,.a2,.a1,.a3⟩,74),(⟨.a3,.a2,.a2,.a2⟩,75),(⟨.a3,.a2,.a2,.a3⟩,76),(⟨.a3,.a2,.a3,.a2⟩,77),(⟨.a3,.a2,.a3,.a3⟩,78),(⟨.a3,.a3,.a1,.a1⟩,79),(⟨.a3,.a3,.a1,.a2⟩,80),(⟨.a3,.a3,.a1,.a3⟩,81),(⟨.a3,.a3,.a2,.a2⟩,82),(⟨.a3,.a3,.a2,.a3⟩,83),(⟨.a3,.a3,.a3,.a2⟩,84),(⟨.a3,.a3,.a3,.a3⟩,85)],0,0,1,2,1,0⟩)))))))) else (if i.val < 292 then (if i.val < 243 then (if i.val < 219 then (if i.val < 207 then (if i.val < 201 then (if i.val < 198 then (if i.val < 196 then ⟨⟨.a0,.a3,.a1,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a3,.a1,.a2,.a1⟩,259),(⟨.a3,.a1,.a2,.a2⟩,260),(⟨.a3,.a1,.a2,.a3⟩,261),(⟨.a3,.a2,.a2,.a3⟩,239),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩ else (if i.val < 197 then ⟨⟨.a0,.a3,.a1,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a3,.a1,.a3,.a1⟩,262),(⟨.a3,.a1,.a3,.a2⟩,263),(⟨.a3,.a1,.a3,.a3⟩,264),(⟨.a3,.a2,.a3,.a2⟩,245),(⟨.a3,.a2,.a3,.a3⟩,246),(⟨.a3,.a3,.a3,.a2⟩,247)],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a3,.a2,.a0,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 199 then ⟨⟨.a0,.a3,.a2,.a2,.d1,.d1,.d1,.a0,.a1,.a2,.a2,false,true⟩,[(⟨.a3,.a2,.a2,.a3⟩,265),(⟨.a3,.a2,.a3,.a2⟩,188),(⟨.a3,.a2,.a3,.a3⟩,189),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩ else (if i.val < 200 then ⟨⟨.a0,.a3,.a2,.a3,.d1,.d0,.d0,.a0,.a1,.a2,.a3,false,true⟩,[(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a3,.a3,.a0,.d2,.d1,.d0,.a0,.a1,.a1,.a2,false,true⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 204 then (if i.val < 202 then ⟨⟨.a0,.a3,.a3,.a2,.d2,.d1,.d0,.a0,.a1,.a1,.a2,false,true⟩,[(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257)],0,0,0,0,0,0⟩ else (if i.val < 203 then ⟨⟨.a0,.a3,.a3,.a3,.d2,.d2,.d1,.a0,.a1,.a1,.a1,false,true⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243)],0,1,1,1,0,0⟩ else ⟨⟨.a1,.a3,.a1,.a1,.d1,.d2,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 205 then ⟨⟨.a1,.a3,.a1,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 206 then ⟨⟨.a1,.a3,.a1,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a3,.a1,.a1,.d1,.d2,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],0,0,0,0,0,0⟩)))) else (if i.val < 213 then (if i.val < 210 then (if i.val < 208 then ⟨⟨.a2,.a3,.a1,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 209 then ⟨⟨.a2,.a3,.a1,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a3,.a2,.a2,.d1,.d1,.d1,.a0,.a1,.a2,.a2,true,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 211 then ⟨⟨.a2,.a3,.a2,.a3,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 212 then ⟨⟨.a2,.a3,.a3,.a2,.d2,.d1,.d0,.a0,.a1,.a1,.a2,true,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a3,.a3,.a3,.d2,.d2,.d1,.a0,.a1,.a1,.a1,true,true⟩,[],1,0,0,0,0,0⟩))) else (if i.val < 216 then (if i.val < 214 then ⟨⟨.a3,.a3,.a1,.a1,.d2,.d2,.d1,.a0,.a0,.a1,.a1,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 215 then ⟨⟨.a3,.a3,.a1,.a2,.d2,.d1,.d0,.a0,.a0,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a3,.a1,.a3,.d2,.d1,.d0,.a0,.a0,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 217 then ⟨⟨.a3,.a3,.a2,.a2,.d2,.d1,.d1,.a0,.a0,.a1,.a1,true,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 218 then ⟨⟨.a3,.a3,.a2,.a3,.d2,.d0,.d0,.a0,.a0,.a1,.a2,true,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a2,.a1,.a1,.d0,.d2,.d1,.a0,.a1,.a0,.a0,true,false⟩,[(⟨.a2,.a2,.a1,.a1⟩,43),(⟨.a2,.a2,.a1,.a2⟩,44),(⟨.a2,.a2,.a1,.a3⟩,45),(⟨.a2,.a2,.a2,.a2⟩,46),(⟨.a2,.a2,.a2,.a3⟩,47),(⟨.a2,.a2,.a3,.a2⟩,48),(⟨.a2,.a2,.a3,.a3⟩,49),(⟨.a2,.a3,.a1,.a1⟩,50),(⟨.a2,.a3,.a1,.a2⟩,51),(⟨.a2,.a3,.a1,.a3⟩,52),(⟨.a2,.a3,.a2,.a2⟩,53),(⟨.a2,.a3,.a2,.a3⟩,54),(⟨.a2,.a3,.a3,.a2⟩,55),(⟨.a2,.a3,.a3,.a3⟩,56)],0,4,8,10,2,0⟩))))) else (if i.val < 231 then (if i.val < 225 then (if i.val < 222 then (if i.val < 220 then ⟨⟨.a1,.a2,.a1,.a2,.d0,.d1,.d0,.a0,.a1,.a0,.a2,true,false⟩,[(⟨.a2,.a1,.a2,.a1⟩,248),(⟨.a2,.a1,.a2,.a2⟩,249),(⟨.a2,.a1,.a2,.a3⟩,250),(⟨.a2,.a2,.a2,.a3⟩,236),(⟨.a2,.a3,.a2,.a2⟩,237),(⟨.a2,.a3,.a2,.a3⟩,238)],0,1,0,0,0,0⟩ else (if i.val < 221 then ⟨⟨.a1,.a2,.a1,.a3,.d0,.d1,.d0,.a0,.a1,.a0,.a2,true,false⟩,[(⟨.a2,.a1,.a3,.a1⟩,251),(⟨.a2,.a1,.a3,.a2⟩,252),(⟨.a2,.a1,.a3,.a3⟩,253),(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a3,.a2⟩,244)],0,2,1,1,0,0⟩ else ⟨⟨.a1,.a2,.a2,.a1,.d1,.d1,.d0,.a0,.a1,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 223 then ⟨⟨.a1,.a2,.a2,.a2,.d1,.d2,.d1,.a0,.a1,.a1,.a1,true,false⟩,[(⟨.a2,.a3,.a2,.a2⟩,386),(⟨.a2,.a3,.a2,.a3⟩,387),(⟨.a2,.a3,.a3,.a2⟩,55),(⟨.a2,.a3,.a3,.a3⟩,56),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,1,0,0,0,0⟩ else (if i.val < 224 then ⟨⟨.a1,.a2,.a2,.a3,.d1,.d1,.d0,.a0,.a1,.a1,.a2,true,false⟩,[(⟨.a2,.a2,.a3,.a2⟩,340),(⟨.a2,.a2,.a3,.a3⟩,341),(⟨.a2,.a3,.a3,.a2⟩,244),(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,1,0,0,0,0⟩ else ⟨⟨.a1,.a2,.a3,.a1,.d0,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 228 then (if i.val < 226 then ⟨⟨.a1,.a2,.a3,.a2,.d0,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257)],0,0,0,0,0,0⟩ else (if i.val < 227 then ⟨⟨.a1,.a2,.a3,.a3,.d0,.d1,.d1,.a0,.a1,.a2,.a2,true,false⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a2,.a2⟩,209),(⟨.a2,.a3,.a2,.a3⟩,210),(⟨.a2,.a3,.a3,.a2⟩,258)],0,1,1,1,0,0⟩ else ⟨⟨.a1,.a3,.a1,.a1,.d0,.d2,.d1,.a0,.a1,.a0,.a0,true,false⟩,[(⟨.a3,.a2,.a1,.a1⟩,72),(⟨.a3,.a2,.a1,.a2⟩,73),(⟨.a3,.a2,.a1,.a3⟩,74),(⟨.a3,.a2,.a2,.a2⟩,75),(⟨.a3,.a2,.a2,.a3⟩,76),(⟨.a3,.a2,.a3,.a2⟩,77),(⟨.a3,.a2,.a3,.a3⟩,78),(⟨.a3,.a3,.a1,.a1⟩,79),(⟨.a3,.a3,.a1,.a2⟩,80),(⟨.a3,.a3,.a1,.a3⟩,81),(⟨.a3,.a3,.a2,.a2⟩,82),(⟨.a3,.a3,.a2,.a3⟩,83),(⟨.a3,.a3,.a3,.a2⟩,84),(⟨.a3,.a3,.a3,.a3⟩,85)],0,0,1,2,1,0⟩)) else (if i.val < 229 then ⟨⟨.a1,.a3,.a1,.a2,.d0,.d1,.d0,.a0,.a1,.a0,.a2,true,false⟩,[(⟨.a3,.a1,.a2,.a1⟩,259),(⟨.a3,.a1,.a2,.a2⟩,260),(⟨.a3,.a1,.a2,.a3⟩,261),(⟨.a3,.a2,.a2,.a3⟩,239),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩ else (if i.val < 230 then ⟨⟨.a1,.a3,.a1,.a3,.d0,.d1,.d0,.a0,.a1,.a0,.a2,true,false⟩,[(⟨.a3,.a1,.a3,.a1⟩,262),(⟨.a3,.a1,.a3,.a2⟩,263),(⟨.a3,.a1,.a3,.a3⟩,264),(⟨.a3,.a2,.a3,.a2⟩,245),(⟨.a3,.a2,.a3,.a3⟩,246),(⟨.a3,.a3,.a3,.a2⟩,247)],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a3,.a2,.a1,.d0,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩)))) else (if i.val < 237 then (if i.val < 234 then (if i.val < 232 then ⟨⟨.a1,.a3,.a2,.a2,.d0,.d1,.d1,.a0,.a1,.a2,.a2,true,false⟩,[(⟨.a3,.a2,.a2,.a3⟩,265),(⟨.a3,.a2,.a3,.a2⟩,188),(⟨.a3,.a2,.a3,.a3⟩,189),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩ else (if i.val < 233 then ⟨⟨.a1,.a3,.a2,.a3,.d0,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a3,.a3,.a1,.d1,.d1,.d0,.a0,.a1,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 235 then ⟨⟨.a1,.a3,.a3,.a2,.d1,.d1,.d0,.a0,.a1,.a1,.a2,true,false⟩,[(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257),(⟨.a3,.a2,.a2,.a3⟩,239),(⟨.a3,.a3,.a2,.a2⟩,348),(⟨.a3,.a3,.a2,.a3⟩,349)],0,0,0,0,0,0⟩ else (if i.val < 236 then ⟨⟨.a1,.a3,.a3,.a3,.d1,.d2,.d1,.a0,.a1,.a1,.a1,true,false⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a3,.a2,.a2,.a2⟩,75),(⟨.a3,.a2,.a2,.a3⟩,76),(⟨.a3,.a2,.a3,.a2⟩,388),(⟨.a3,.a2,.a3,.a3⟩,389)],0,1,2,2,0,0⟩ else ⟨⟨.a2,.a2,.a2,.a3,.d2,.d2,.d0,.a0,.a0,.a0,.a1,true,true⟩,[],1,0,0,0,0,0⟩))) else (if i.val < 240 then (if i.val < 238 then ⟨⟨.a2,.a3,.a2,.a2,.d0,.d2,.d1,.a0,.a1,.a2,.a2,true,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 239 then ⟨⟨.a2,.a3,.a2,.a3,.d0,.d1,.d0,.a0,.a1,.a2,.a3,true,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a2,.a2,.a3,.d1,.d2,.d0,.a0,.a1,.a1,.a2,true,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 241 then ⟨⟨.a3,.a3,.a2,.a2,.d1,.d2,.d1,.a0,.a0,.a1,.a1,true,true⟩,[(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩ else (if i.val < 242 then ⟨⟨.a3,.a3,.a2,.a3,.d1,.d1,.d0,.a0,.a0,.a1,.a2,true,true⟩,[(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a2,.a3,.a2,.d1,.d1,.d0,.a0,.a0,.a1,.a2,true,true⟩,[(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257)],0,0,0,0,0,0⟩)))))) else (if i.val < 267 then (if i.val < 255 then (if i.val < 249 then (if i.val < 246 then (if i.val < 244 then ⟨⟨.a2,.a2,.a3,.a3,.d1,.d2,.d1,.a0,.a0,.a1,.a1,true,true⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243)],1,1,1,1,0,0⟩ else (if i.val < 245 then ⟨⟨.a2,.a3,.a3,.a2,.d1,.d2,.d0,.a0,.a1,.a1,.a2,true,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a2,.a3,.a2,.d0,.d1,.d0,.a0,.a1,.a2,.a3,true,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 247 then ⟨⟨.a3,.a2,.a3,.a3,.d0,.d2,.d1,.a0,.a1,.a2,.a2,true,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 248 then ⟨⟨.a3,.a3,.a3,.a2,.d2,.d2,.d0,.a0,.a0,.a0,.a1,true,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a1,.a2,.a1,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 252 then (if i.val < 250 then ⟨⟨.a2,.a1,.a2,.a2,.d1,.d2,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 251 then ⟨⟨.a2,.a1,.a2,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a1,.a3,.a1,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 253 then ⟨⟨.a2,.a1,.a3,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 254 then ⟨⟨.a2,.a1,.a3,.a3,.d1,.d2,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],1,0,0,0,0,0⟩ else ⟨⟨.a3,.a2,.a3,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,true⟩,[],0,0,0,0,0,0⟩)))) else (if i.val < 261 then (if i.val < 258 then (if i.val < 256 then ⟨⟨.a3,.a2,.a3,.a3,.d1,.d2,.d1,.a0,.a1,.a2,.a2,true,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 257 then ⟨⟨.a2,.a3,.a2,.a2,.d1,.d2,.d1,.a0,.a1,.a2,.a2,true,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a3,.a2,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 259 then ⟨⟨.a2,.a3,.a3,.a2,.d2,.d2,.d0,.a0,.a1,.a1,.a2,true,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 260 then ⟨⟨.a3,.a1,.a2,.a1,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a1,.a2,.a2,.d1,.d2,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 264 then (if i.val < 262 then ⟨⟨.a3,.a1,.a2,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 263 then ⟨⟨.a3,.a1,.a3,.a1,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a1,.a3,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 265 then ⟨⟨.a3,.a1,.a3,.a3,.d1,.d2,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 266 then ⟨⟨.a3,.a2,.a2,.a3,.d2,.d2,.d0,.a0,.a1,.a1,.a2,true,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a2,.a0,.a0,.d1,.d2,.d1,.a0,.a0,.a1,.a1,false,true⟩,[(⟨.a2,.a2,.a0,.a0⟩,266),(⟨.a2,.a2,.a0,.a2⟩,267),(⟨.a2,.a2,.a0,.a3⟩,268),(⟨.a2,.a2,.a2,.a2⟩,46),(⟨.a2,.a2,.a2,.a3⟩,47),(⟨.a2,.a2,.a3,.a2⟩,48),(⟨.a2,.a2,.a3,.a3⟩,49),(⟨.a2,.a3,.a0,.a0⟩,269),(⟨.a2,.a3,.a0,.a2⟩,270),(⟨.a2,.a3,.a0,.a3⟩,271),(⟨.a2,.a3,.a2,.a2⟩,53),(⟨.a2,.a3,.a2,.a3⟩,54),(⟨.a2,.a3,.a3,.a2⟩,55),(⟨.a2,.a3,.a3,.a3⟩,56)],0,4,8,10,2,0⟩))))) else (if i.val < 279 then (if i.val < 273 then (if i.val < 270 then (if i.val < 268 then ⟨⟨.a2,.a2,.a0,.a2,.d1,.d1,.d0,.a0,.a0,.a1,.a2,false,true⟩,[(⟨.a2,.a0,.a2,.a0⟩,278),(⟨.a2,.a0,.a2,.a2⟩,279),(⟨.a2,.a0,.a2,.a3⟩,280),(⟨.a2,.a2,.a2,.a3⟩,236),(⟨.a2,.a3,.a2,.a2⟩,237),(⟨.a2,.a3,.a2,.a3⟩,238)],0,1,0,0,0,0⟩ else (if i.val < 269 then ⟨⟨.a2,.a2,.a0,.a3,.d1,.d1,.d0,.a0,.a0,.a1,.a2,false,true⟩,[(⟨.a2,.a0,.a3,.a0⟩,284),(⟨.a2,.a0,.a3,.a2⟩,285),(⟨.a2,.a0,.a3,.a3⟩,286),(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a3,.a2⟩,244)],1,2,1,1,0,0⟩ else ⟨⟨.a2,.a3,.a0,.a0,.d0,.d2,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 271 then ⟨⟨.a2,.a3,.a0,.a2,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 272 then ⟨⟨.a2,.a3,.a0,.a3,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a2,.a0,.a0,.d0,.d2,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 276 then (if i.val < 274 then ⟨⟨.a3,.a2,.a0,.a2,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 275 then ⟨⟨.a3,.a2,.a0,.a3,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a3,.a0,.a0,.d1,.d2,.d1,.a0,.a0,.a1,.a1,false,true⟩,[(⟨.a3,.a2,.a0,.a0⟩,272),(⟨.a3,.a2,.a0,.a2⟩,273),(⟨.a3,.a2,.a0,.a3⟩,274),(⟨.a3,.a2,.a2,.a2⟩,75),(⟨.a3,.a2,.a2,.a3⟩,76),(⟨.a3,.a2,.a3,.a2⟩,77),(⟨.a3,.a2,.a3,.a3⟩,78),(⟨.a3,.a3,.a0,.a0⟩,275),(⟨.a3,.a3,.a0,.a2⟩,276),(⟨.a3,.a3,.a0,.a3⟩,277),(⟨.a3,.a3,.a2,.a2⟩,82),(⟨.a3,.a3,.a2,.a3⟩,83),(⟨.a3,.a3,.a3,.a2⟩,84),(⟨.a3,.a3,.a3,.a3⟩,85)],0,0,1,2,1,0⟩)) else (if i.val < 277 then ⟨⟨.a3,.a3,.a0,.a2,.d1,.d1,.d0,.a0,.a0,.a1,.a2,false,true⟩,[(⟨.a3,.a0,.a2,.a0⟩,281),(⟨.a3,.a0,.a2,.a2⟩,282),(⟨.a3,.a0,.a2,.a3⟩,283),(⟨.a3,.a2,.a2,.a3⟩,239),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩ else (if i.val < 278 then ⟨⟨.a3,.a3,.a0,.a3,.d1,.d1,.d0,.a0,.a0,.a1,.a2,false,true⟩,[(⟨.a3,.a0,.a3,.a0⟩,287),(⟨.a3,.a0,.a3,.a2⟩,288),(⟨.a3,.a0,.a3,.a3⟩,289),(⟨.a3,.a2,.a3,.a2⟩,245),(⟨.a3,.a2,.a3,.a3⟩,246),(⟨.a3,.a3,.a3,.a2⟩,247)],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a0,.a2,.a0,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩)))) else (if i.val < 285 then (if i.val < 282 then (if i.val < 280 then ⟨⟨.a2,.a0,.a2,.a2,.d1,.d2,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 281 then ⟨⟨.a2,.a0,.a2,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a0,.a2,.a0,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 283 then ⟨⟨.a3,.a0,.a2,.a2,.d1,.d2,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 284 then ⟨⟨.a3,.a0,.a2,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a0,.a3,.a0,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 288 then (if i.val < 286 then ⟨⟨.a2,.a0,.a3,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 287 then ⟨⟨.a2,.a0,.a3,.a3,.d1,.d2,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],1,0,0,0,0,0⟩ else ⟨⟨.a3,.a0,.a3,.a0,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 290 then (if i.val < 289 then ⟨⟨.a3,.a0,.a3,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a0,.a3,.a3,.d1,.d2,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],0,0,0,0,0,0⟩) else (if i.val < 291 then ⟨⟨.a0,.a0,.a0,.a2,.d2,.d2,.d0,.a0,.a0,.a0,.a1,false,true⟩,[(⟨.a2,.a2,.a2,.a3⟩,236),(⟨.a2,.a3,.a2,.a2⟩,237),(⟨.a2,.a3,.a2,.a3⟩,238),(⟨.a3,.a2,.a2,.a3⟩,239),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,1,0,0,0,0⟩ else ⟨⟨.a0,.a0,.a0,.a3,.d2,.d2,.d0,.a0,.a0,.a0,.a1,false,true⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a3,.a2⟩,244),(⟨.a3,.a2,.a3,.a2⟩,245),(⟨.a3,.a2,.a3,.a3⟩,246),(⟨.a3,.a3,.a3,.a2⟩,247)],0,1,1,1,0,0⟩))))))) else (if i.val < 341 then (if i.val < 316 then (if i.val < 304 then (if i.val < 298 then (if i.val < 295 then (if i.val < 293 then ⟨⟨.a0,.a1,.a0,.a0,.d1,.d2,.d1,.a0,.a1,.a2,.a2,false,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 294 then ⟨⟨.a0,.a1,.a0,.a1,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a1,.a0,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 296 then ⟨⟨.a0,.a1,.a0,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 297 then ⟨⟨.a0,.a2,.a0,.a0,.d0,.d2,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a2,.a0,.a2,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 301 then (if i.val < 299 then ⟨⟨.a0,.a2,.a0,.a3,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 300 then ⟨⟨.a0,.a3,.a0,.a0,.d0,.d2,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a3,.a0,.a2,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 302 then ⟨⟨.a0,.a3,.a0,.a3,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 303 then ⟨⟨.a0,.a0,.a2,.a0,.d1,.d1,.d0,.a0,.a0,.a1,.a2,false,true⟩,[(⟨.a0,.a2,.a0,.a0⟩,332),(⟨.a0,.a2,.a0,.a2⟩,333),(⟨.a0,.a2,.a0,.a3⟩,334)],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a0,.a2,.a2,.d1,.d2,.d1,.a0,.a0,.a1,.a1,false,true⟩,[(⟨.a0,.a0,.a2,.a0⟩,302),(⟨.a0,.a0,.a2,.a2⟩,303),(⟨.a0,.a0,.a2,.a3⟩,304),(⟨.a0,.a3,.a2,.a0⟩,311),(⟨.a0,.a3,.a2,.a2⟩,312),(⟨.a0,.a3,.a2,.a3⟩,313),(⟨.a2,.a3,.a2,.a2⟩,237),(⟨.a2,.a3,.a2,.a3⟩,238),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,1,2,1,0⟩)))) else (if i.val < 310 then (if i.val < 307 then (if i.val < 305 then ⟨⟨.a0,.a0,.a2,.a3,.d1,.d1,.d0,.a0,.a0,.a1,.a2,false,true⟩,[(⟨.a0,.a2,.a3,.a0⟩,337),(⟨.a0,.a2,.a3,.a2⟩,338),(⟨.a0,.a2,.a3,.a3⟩,339),(⟨.a2,.a2,.a3,.a2⟩,340),(⟨.a2,.a2,.a3,.a3⟩,341),(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,1,1,1,0,0⟩ else (if i.val < 306 then ⟨⟨.a0,.a1,.a2,.a0,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a1,.a2,.a1,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a1,.a2,.a1,.a1⟩,175),(⟨.a1,.a2,.a1,.a2⟩,176),(⟨.a1,.a2,.a1,.a3⟩,177)],0,0,0,0,0,0⟩)) else (if i.val < 308 then ⟨⟨.a0,.a1,.a2,.a2,.d1,.d2,.d1,.a0,.a1,.a2,.a2,false,false⟩,[(⟨.a1,.a1,.a2,.a1⟩,352),(⟨.a1,.a1,.a2,.a2⟩,353),(⟨.a1,.a1,.a2,.a3⟩,354),(⟨.a1,.a3,.a2,.a1⟩,363),(⟨.a1,.a3,.a2,.a2⟩,364),(⟨.a1,.a3,.a2,.a3⟩,365),(⟨.a2,.a3,.a2,.a2⟩,237),(⟨.a2,.a3,.a2,.a3⟩,238),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,1,2,1,0⟩ else (if i.val < 309 then ⟨⟨.a0,.a1,.a2,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a1,.a2,.a3,.a1⟩,366),(⟨.a1,.a2,.a3,.a2⟩,367),(⟨.a1,.a2,.a3,.a3⟩,368),(⟨.a2,.a2,.a3,.a2⟩,340),(⟨.a2,.a2,.a3,.a3⟩,341),(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,1,1,1,0,0⟩ else ⟨⟨.a0,.a2,.a2,.a0,.d1,.d2,.d0,.a0,.a1,.a1,.a2,false,true⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 313 then (if i.val < 311 then ⟨⟨.a0,.a2,.a2,.a3,.d1,.d2,.d0,.a0,.a1,.a1,.a2,false,true⟩,[(⟨.a2,.a3,.a3,.a2⟩,244)],0,0,0,0,0,0⟩ else (if i.val < 312 then ⟨⟨.a0,.a3,.a2,.a0,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a3,.a2,.a2,.d0,.d2,.d1,.a0,.a1,.a2,.a2,false,true⟩,[(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩)) else (if i.val < 314 then ⟨⟨.a0,.a3,.a2,.a3,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,0,0,0,0,0⟩ else (if i.val < 315 then ⟨⟨.a1,.a1,.a2,.a1,.d2,.d1,.d0,.a0,.a0,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a1,.a2,.a2,.d2,.d2,.d1,.a0,.a0,.a1,.a1,true,false⟩,[(⟨.a2,.a3,.a2,.a2⟩,237),(⟨.a2,.a3,.a2,.a3⟩,238),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩))))) else (if i.val < 328 then (if i.val < 322 then (if i.val < 319 then (if i.val < 317 then ⟨⟨.a1,.a1,.a2,.a3,.d2,.d1,.d0,.a0,.a0,.a1,.a2,true,false⟩,[(⟨.a2,.a2,.a3,.a2⟩,340),(⟨.a2,.a2,.a3,.a3⟩,341),(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,1,0,0,0,0⟩ else (if i.val < 318 then ⟨⟨.a0,.a0,.a3,.a0,.d1,.d1,.d0,.a0,.a0,.a1,.a2,false,true⟩,[(⟨.a0,.a3,.a0,.a0⟩,342),(⟨.a0,.a3,.a0,.a2⟩,343),(⟨.a0,.a3,.a0,.a3⟩,344)],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a0,.a3,.a2,.d1,.d1,.d0,.a0,.a0,.a1,.a2,false,true⟩,[(⟨.a0,.a3,.a2,.a0⟩,345),(⟨.a0,.a3,.a2,.a2⟩,346),(⟨.a0,.a3,.a2,.a3⟩,347),(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257),(⟨.a3,.a3,.a2,.a2⟩,348),(⟨.a3,.a3,.a2,.a3⟩,349)],0,0,0,0,0,0⟩)) else (if i.val < 320 then ⟨⟨.a0,.a0,.a3,.a3,.d1,.d2,.d1,.a0,.a0,.a1,.a1,false,true⟩,[(⟨.a0,.a0,.a3,.a0⟩,317),(⟨.a0,.a0,.a3,.a2⟩,318),(⟨.a0,.a0,.a3,.a3⟩,319),(⟨.a0,.a2,.a3,.a0⟩,324),(⟨.a0,.a2,.a3,.a2⟩,325),(⟨.a0,.a2,.a3,.a3⟩,326),(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a3,.a2,.a3,.a2⟩,245),(⟨.a3,.a2,.a3,.a3⟩,246)],0,1,3,5,2,0⟩ else (if i.val < 321 then ⟨⟨.a0,.a1,.a3,.a0,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a1,.a3,.a1,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a1,.a3,.a1,.a1⟩,203),(⟨.a1,.a3,.a1,.a2⟩,204),(⟨.a1,.a3,.a1,.a3⟩,205)],0,0,0,0,0,0⟩))) else (if i.val < 325 then (if i.val < 323 then ⟨⟨.a0,.a1,.a3,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,false⟩,[(⟨.a1,.a3,.a2,.a1⟩,369),(⟨.a1,.a3,.a2,.a2⟩,370),(⟨.a1,.a3,.a2,.a3⟩,371),(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257),(⟨.a3,.a3,.a2,.a2⟩,348),(⟨.a3,.a3,.a2,.a3⟩,349)],0,0,0,0,0,0⟩ else (if i.val < 324 then ⟨⟨.a0,.a1,.a3,.a3,.d1,.d2,.d1,.a0,.a1,.a2,.a2,false,false⟩,[(⟨.a1,.a1,.a3,.a1⟩,372),(⟨.a1,.a1,.a3,.a2⟩,373),(⟨.a1,.a1,.a3,.a3⟩,374),(⟨.a1,.a2,.a3,.a1⟩,375),(⟨.a1,.a2,.a3,.a2⟩,376),(⟨.a1,.a2,.a3,.a3⟩,377),(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a3,.a2,.a3,.a2⟩,245),(⟨.a3,.a2,.a3,.a3⟩,246)],0,1,3,5,2,0⟩ else ⟨⟨.a0,.a2,.a3,.a0,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 326 then ⟨⟨.a0,.a2,.a3,.a2,.d0,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257)],0,0,0,0,0,0⟩ else (if i.val < 327 then ⟨⟨.a0,.a2,.a3,.a3,.d0,.d2,.d1,.a0,.a1,.a2,.a2,false,true⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243)],0,1,1,1,0,0⟩ else ⟨⟨.a0,.a3,.a3,.a0,.d1,.d2,.d0,.a0,.a1,.a1,.a2,false,true⟩,[],0,0,0,0,0,0⟩)))) else (if i.val < 334 then (if i.val < 331 then (if i.val < 329 then ⟨⟨.a0,.a3,.a3,.a2,.d1,.d2,.d0,.a0,.a1,.a1,.a2,false,true⟩,[(⟨.a3,.a2,.a2,.a3⟩,239)],0,0,0,0,0,0⟩ else (if i.val < 330 then ⟨⟨.a1,.a1,.a3,.a1,.d2,.d1,.d0,.a0,.a0,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a1,.a3,.a2,.d2,.d1,.d0,.a0,.a0,.a1,.a2,true,false⟩,[(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257),(⟨.a3,.a3,.a2,.a2⟩,348),(⟨.a3,.a3,.a2,.a3⟩,349)],0,0,0,0,0,0⟩)) else (if i.val < 332 then ⟨⟨.a1,.a1,.a3,.a3,.d2,.d2,.d1,.a0,.a0,.a1,.a1,true,false⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a3,.a2,.a3,.a2⟩,245),(⟨.a3,.a2,.a3,.a3⟩,246)],0,1,1,1,0,0⟩ else (if i.val < 333 then ⟨⟨.a0,.a2,.a0,.a0,.d1,.d2,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a2,.a0,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 337 then (if i.val < 335 then ⟨⟨.a0,.a2,.a0,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 336 then ⟨⟨.a0,.a2,.a2,.a0,.d2,.d2,.d0,.a0,.a1,.a1,.a2,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a2,.a2,.a3,.d2,.d2,.d0,.a0,.a1,.a1,.a2,false,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 339 then (if i.val < 338 then ⟨⟨.a0,.a2,.a3,.a0,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a2,.a3,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257)],0,0,0,0,0,0⟩) else (if i.val < 340 then ⟨⟨.a0,.a2,.a3,.a3,.d1,.d2,.d1,.a0,.a1,.a2,.a2,false,true⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243)],0,1,1,1,0,0⟩ else ⟨⟨.a2,.a2,.a3,.a2,.d2,.d1,.d0,.a0,.a0,.a1,.a2,true,true⟩,[],0,0,0,0,0,0⟩)))))) else (if i.val < 365 then (if i.val < 353 then (if i.val < 347 then (if i.val < 344 then (if i.val < 342 then ⟨⟨.a2,.a2,.a3,.a3,.d2,.d2,.d1,.a0,.a0,.a1,.a1,true,true⟩,[],1,0,0,0,0,0⟩ else (if i.val < 343 then ⟨⟨.a0,.a3,.a0,.a0,.d1,.d2,.d1,.a0,.a1,.a2,.a2,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a3,.a0,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 345 then ⟨⟨.a0,.a3,.a0,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 346 then ⟨⟨.a0,.a3,.a2,.a0,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a0,.a3,.a2,.a2,.d1,.d2,.d1,.a0,.a1,.a2,.a2,false,true⟩,[(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩))) else (if i.val < 350 then (if i.val < 348 then ⟨⟨.a0,.a3,.a2,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,false,true⟩,[(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,0,0,0,0,0⟩ else (if i.val < 349 then ⟨⟨.a3,.a3,.a2,.a2,.d2,.d2,.d1,.a0,.a0,.a1,.a1,true,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a3,.a2,.a3,.d2,.d1,.d0,.a0,.a0,.a1,.a2,true,true⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 351 then ⟨⟨.a0,.a3,.a3,.a0,.d2,.d2,.d0,.a0,.a1,.a1,.a2,false,true⟩,[],0,0,0,0,0,0⟩ else (if i.val < 352 then ⟨⟨.a0,.a3,.a3,.a2,.d2,.d2,.d0,.a0,.a1,.a1,.a2,false,true⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a1,.a2,.a1,.d1,.d1,.d0,.a0,.a0,.a1,.a2,true,false⟩,[(⟨.a1,.a2,.a1,.a1⟩,175),(⟨.a1,.a2,.a1,.a2⟩,176),(⟨.a1,.a2,.a1,.a3⟩,177)],0,0,0,0,0,0⟩)))) else (if i.val < 359 then (if i.val < 356 then (if i.val < 354 then ⟨⟨.a1,.a1,.a2,.a2,.d1,.d2,.d1,.a0,.a0,.a1,.a1,true,false⟩,[(⟨.a1,.a1,.a2,.a1⟩,352),(⟨.a1,.a1,.a2,.a2⟩,353),(⟨.a1,.a1,.a2,.a3⟩,354),(⟨.a1,.a3,.a2,.a1⟩,363),(⟨.a1,.a3,.a2,.a2⟩,364),(⟨.a1,.a3,.a2,.a3⟩,365),(⟨.a2,.a3,.a2,.a2⟩,237),(⟨.a2,.a3,.a2,.a3⟩,238),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,1,2,1,0⟩ else (if i.val < 355 then ⟨⟨.a1,.a1,.a2,.a3,.d1,.d1,.d0,.a0,.a0,.a1,.a2,true,false⟩,[(⟨.a1,.a2,.a3,.a1⟩,366),(⟨.a1,.a2,.a3,.a2⟩,367),(⟨.a1,.a2,.a3,.a3⟩,368),(⟨.a2,.a2,.a3,.a2⟩,340),(⟨.a2,.a2,.a3,.a3⟩,341),(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,1,1,1,0,0⟩ else ⟨⟨.a1,.a2,.a1,.a1,.d1,.d1,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 357 then ⟨⟨.a1,.a2,.a1,.a2,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 358 then ⟨⟨.a1,.a2,.a1,.a3,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a2,.a2,.a1,.d2,.d2,.d0,.a0,.a1,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩))) else (if i.val < 362 then (if i.val < 360 then ⟨⟨.a1,.a2,.a2,.a3,.d2,.d2,.d0,.a0,.a1,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 361 then ⟨⟨.a1,.a2,.a3,.a1,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a2,.a3,.a2,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257)],0,0,0,0,0,0⟩)) else (if i.val < 363 then ⟨⟨.a1,.a2,.a3,.a3,.d1,.d1,.d1,.a0,.a1,.a2,.a2,true,false⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a2,.a3,.a2,.a2⟩,209),(⟨.a2,.a3,.a2,.a3⟩,210),(⟨.a2,.a3,.a3,.a2⟩,258)],0,1,1,1,0,0⟩ else (if i.val < 364 then ⟨⟨.a1,.a3,.a2,.a1,.d0,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a3,.a2,.a2,.d0,.d2,.d1,.a0,.a1,.a2,.a2,true,false⟩,[(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩))))) else (if i.val < 377 then (if i.val < 371 then (if i.val < 368 then (if i.val < 366 then ⟨⟨.a1,.a3,.a2,.a3,.d0,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,0,0,0,0,0⟩ else (if i.val < 367 then ⟨⟨.a1,.a2,.a3,.a1,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a2,.a3,.a2,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257)],0,0,0,0,0,0⟩)) else (if i.val < 369 then ⟨⟨.a1,.a2,.a3,.a3,.d1,.d2,.d1,.a0,.a1,.a2,.a2,true,false⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243)],0,1,1,1,0,0⟩ else (if i.val < 370 then ⟨⟨.a1,.a3,.a2,.a1,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a3,.a2,.a2,.d1,.d2,.d1,.a0,.a1,.a2,.a2,true,false⟩,[(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩))) else (if i.val < 374 then (if i.val < 372 then ⟨⟨.a1,.a3,.a2,.a3,.d1,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,0,0,0,0,0⟩ else (if i.val < 373 then ⟨⟨.a1,.a1,.a3,.a1,.d1,.d1,.d0,.a0,.a0,.a1,.a2,true,false⟩,[(⟨.a1,.a3,.a1,.a1⟩,203),(⟨.a1,.a3,.a1,.a2⟩,204),(⟨.a1,.a3,.a1,.a3⟩,205)],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a1,.a3,.a2,.d1,.d1,.d0,.a0,.a0,.a1,.a2,true,false⟩,[(⟨.a1,.a3,.a2,.a1⟩,369),(⟨.a1,.a3,.a2,.a2⟩,370),(⟨.a1,.a3,.a2,.a3⟩,371),(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257),(⟨.a3,.a3,.a2,.a2⟩,348),(⟨.a3,.a3,.a2,.a3⟩,349)],0,0,0,0,0,0⟩)) else (if i.val < 375 then ⟨⟨.a1,.a1,.a3,.a3,.d1,.d2,.d1,.a0,.a0,.a1,.a1,true,false⟩,[(⟨.a1,.a1,.a3,.a1⟩,372),(⟨.a1,.a1,.a3,.a2⟩,373),(⟨.a1,.a1,.a3,.a3⟩,374),(⟨.a1,.a2,.a3,.a1⟩,375),(⟨.a1,.a2,.a3,.a2⟩,376),(⟨.a1,.a2,.a3,.a3⟩,377),(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243),(⟨.a3,.a2,.a3,.a2⟩,245),(⟨.a3,.a2,.a3,.a3⟩,246)],0,1,3,5,2,0⟩ else (if i.val < 376 then ⟨⟨.a1,.a2,.a3,.a1,.d0,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a2,.a3,.a2,.d0,.d1,.d0,.a0,.a1,.a2,.a3,true,false⟩,[(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257)],0,0,0,0,0,0⟩)))) else (if i.val < 383 then (if i.val < 380 then (if i.val < 378 then ⟨⟨.a1,.a2,.a3,.a3,.d0,.d2,.d1,.a0,.a1,.a2,.a2,true,false⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243)],0,1,1,1,0,0⟩ else (if i.val < 379 then ⟨⟨.a1,.a3,.a1,.a1,.d1,.d1,.d1,.a0,.a1,.a2,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a3,.a1,.a2,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 381 then ⟨⟨.a1,.a3,.a1,.a3,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else (if i.val < 382 then ⟨⟨.a1,.a3,.a2,.a1,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a3,.a2,.a2,.d1,.d1,.d1,.a0,.a1,.a2,.a2,true,false⟩,[(⟨.a3,.a2,.a2,.a3⟩,265),(⟨.a3,.a2,.a3,.a2⟩,188),(⟨.a3,.a2,.a3,.a3⟩,189),(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩))) else (if i.val < 386 then (if i.val < 384 then ⟨⟨.a1,.a3,.a2,.a3,.d1,.d0,.d0,.a0,.a1,.a2,.a3,true,false⟩,[(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,0,0,0,0,0⟩ else (if i.val < 385 then ⟨⟨.a1,.a3,.a3,.a1,.d2,.d2,.d0,.a0,.a1,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩ else ⟨⟨.a1,.a3,.a3,.a2,.d2,.d2,.d0,.a0,.a1,.a1,.a2,true,false⟩,[],0,0,0,0,0,0⟩)) else (if i.val < 388 then (if i.val < 387 then ⟨⟨.a2,.a3,.a2,.a2,.d0,.d2,.d1,.a0,.a1,.a0,.a0,true,true⟩,[(⟨.a3,.a3,.a2,.a2⟩,240),(⟨.a3,.a3,.a2,.a3⟩,241)],0,0,0,0,0,0⟩ else ⟨⟨.a2,.a3,.a2,.a3,.d0,.d1,.d0,.a0,.a1,.a0,.a2,true,true⟩,[(⟨.a3,.a2,.a3,.a2⟩,254),(⟨.a3,.a2,.a3,.a3⟩,255)],0,0,0,0,0,0⟩) else (if i.val < 389 then ⟨⟨.a3,.a2,.a3,.a2,.d0,.d1,.d0,.a0,.a1,.a0,.a2,true,true⟩,[(⟨.a2,.a3,.a2,.a2⟩,256),(⟨.a2,.a3,.a2,.a3⟩,257)],0,0,0,0,0,0⟩ else ⟨⟨.a3,.a2,.a3,.a3,.d0,.d2,.d1,.a0,.a1,.a0,.a0,true,true⟩,[(⟨.a2,.a2,.a3,.a2⟩,242),(⟨.a2,.a2,.a3,.a3⟩,243)],0,1,1,1,0,0⟩)))))))))

private def stateOf (i : Fin 390) : State := (dataOf i).st
private def edgesOf (i : Fin 390) : List (Row × Fin 390) := (dataOf i).es
private def w0Vec (i : Fin 390) : ℕ := (dataOf i).w0
private def w1Vec (i : Fin 390) : ℕ := (dataOf i).w1
private def w2Vec (i : Fin 390) : ℕ := (dataOf i).w2
private def a0Vec (i : Fin 390) : ℕ := (dataOf i).a0
private def a1Vec (i : Fin 390) : ℕ := (dataOf i).a1
private def a2Vec (i : Fin 390) : ℕ := (dataOf i).a2

private def initEdges : List (Row × Fin 390) :=
  [(⟨.a0,.a0,.a0,.a1⟩,0),(⟨.a0,.a0,.a1,.a1⟩,1),(⟨.a0,.a0,.a2,.a1⟩,2),(⟨.a0,.a0,.a3,.a1⟩,3),(⟨.a0,.a1,.a0,.a1⟩,4),(⟨.a0,.a1,.a1,.a1⟩,5),(⟨.a0,.a1,.a2,.a1⟩,6),(⟨.a0,.a1,.a3,.a1⟩,7),(⟨.a0,.a2,.a0,.a1⟩,8),(⟨.a0,.a2,.a1,.a1⟩,9),(⟨.a0,.a2,.a2,.a1⟩,10),(⟨.a0,.a2,.a3,.a1⟩,11),(⟨.a0,.a3,.a0,.a1⟩,12),(⟨.a0,.a3,.a1,.a1⟩,13),(⟨.a0,.a3,.a2,.a1⟩,14),(⟨.a0,.a3,.a3,.a1⟩,15)]

private def all4 (p : C4 → Bool) : Bool := p .a0 && p .a1 && p .a2 && p .a3

private lemma all4_iff (p : C4 → Bool) : all4 p = true ↔ ∀ c : C4, p c = true := by
  simp only [all4, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ c
    cases c <;> assumption
  · intro h
    exact ⟨⟨⟨h .a0, h .a1⟩, h .a2⟩, h .a3⟩

private def lookupRow : List (Row × Fin 390) → Row → Option (Fin 390)
  | [], _ => none
  | (r, j) :: tl, r' => if r.eqb r' then some j else lookupRow tl r'

private def memRow (r : Row) : List (Row × Fin 390) → Bool
  | [] => false
  | (r', _) :: tl => r.eqb r' || memRow r tl

private def nodupRows : List (Row × Fin 390) → Bool
  | [] => true
  | (r, _) :: tl => !memRow r tl && nodupRows tl

private lemma lookupRow_none_of_not_mem (es : List (Row × Fin 390)) (r : Row)
    (h : memRow r es = false) : lookupRow es r = none := by
  induction es with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨r0, j0⟩
    simp only [memRow, Bool.or_eq_false_iff] at h
    have hneq : r0.eqb r = false := by
      cases he : r0.eqb r
      · rfl
      · have h1 := (Row.eqb_iff r0 r).1 he
        have h2 := (Row.eqb_iff r r0).2 h1.symm
        rw [h2] at h; cases h.1
    simp only [lookupRow, hneq, Bool.false_eq_true, ite_false]
    exact ih h.2

private lemma sum_lookupRow (es : List (Row × Fin 390)) (hnd : nodupRows es = true)
    (f : Fin 390 → ℕ) :
    (∑ r : Row, match lookupRow es r with | none => 0 | some j => f j) =
      (es.map fun e => f e.2).sum := by
  induction es with
  | nil => simp [lookupRow]
  | cons hd tl ih =>
    rcases hd with ⟨r0, j0⟩
    simp only [nodupRows, Bool.and_eq_true, Bool.not_eq_true'] at hnd
    have htl := ih hnd.2
    have h1 : (∑ r : Row, match lookupRow ((r0, j0) :: tl) r with | none => 0 | some j => f j) =
        f j0 + ∑ r ∈ Finset.univ.erase r0,
          match lookupRow ((r0, j0) :: tl) r with | none => 0 | some j => f j := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ r0)]
      have hself : r0.eqb r0 = true := (Row.eqb_iff r0 r0).2 rfl
      simp [lookupRow, hself]
    have h2 : (∑ r ∈ Finset.univ.erase r0,
        match lookupRow ((r0, j0) :: tl) r with | none => 0 | some j => f j) =
        ∑ r ∈ Finset.univ.erase r0,
          match lookupRow tl r with | none => 0 | some j => f j := by
      apply Finset.sum_congr rfl
      intro r hr
      have hne : r0 ≠ r := (Finset.mem_erase.1 hr).1.symm
      have heq : r0.eqb r = false := by
        cases h : r0.eqb r
        · rfl
        · exact absurd ((Row.eqb_iff r0 r).1 h) hne
      simp [lookupRow, heq]
    have h3 : (∑ r : Row, match lookupRow tl r with | none => 0 | some j => f j) =
        ∑ r ∈ Finset.univ.erase r0,
          match lookupRow tl r with | none => 0 | some j => f j := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ r0)]
      rw [lookupRow_none_of_not_mem tl r0 hnd.1]
      simp
    rw [h1, h2, ← h3, htl]
    rfl

private def optEqb : Option State → Option (Fin 390) → Bool
  | none, none => true
  | some s, some j => s.eqb (stateOf j)
  | _, _ => false

private lemma optEqb_iff (o1 : Option State) (o2 : Option (Fin 390)) :
    optEqb o1 o2 = true ↔ o1 = Option.map stateOf o2 := by
  cases o1 <;> cases o2 <;> simp [optEqb, State.eqb_iff]

private lemma lookupRow_none_of_all (es : List (Row × Fin 390)) (r : Row)
    (p : Row → Bool) (hp : p r = true) (hall : es.all (fun e => !p e.1) = true) :
    lookupRow es r = none := by
  induction es with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨r0, j0⟩
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hall
    have hne : r0.eqb r = false := by
      cases h : r0.eqb r
      · rfl
      · have heq := (Row.eqb_iff r0 r).1 h
        subst heq
        rw [hp] at hall
        cases hall.1
    simp only [lookupRow, hne, Bool.false_eq_true, ite_false]
    exact ih hall.2

private def checkOne (i : Fin 390) : Bool :=
  let s := stateOf i
  let es := edgesOf i
  all4 fun c0 =>
    if s.closed c0 || !okAdd s.d1 (s.r1.eqb c0) then
      es.all fun e => !e.1.c0.eqb c0
    else
    all4 fun c1 =>
      if s.closed c1 || !okAdd s.d2 (s.r2.eqb c1) then
        es.all fun e => !(e.1.c0.eqb c0 && e.1.c1.eqb c1)
      else
      all4 fun c2 =>
        if s.closed c2 || !okAdd s.d3 (s.r3.eqb c2) || (s.r2.eqb c1 && c0.eqb c1 && c1.eqb c2) then
          es.all fun e => !(e.1.c0.eqb c0 && e.1.c1.eqb c1 && e.1.c2.eqb c2)
        else
        all4 fun c3 =>
          optEqb (step s ⟨c0, c1, c2, c3⟩) (lookupRow es ⟨c0, c1, c2, c3⟩)

private lemma checkOne_sound (i : Fin 390) (hc : checkOne i = true) (r : Row) :
    step (stateOf i) r = Option.map stateOf (lookupRow (edgesOf i) r) := by
  rcases r with ⟨c0, c1, c2, c3⟩
  let s := stateOf i
  let es := edgesOf i
  change step s ⟨c0, c1, c2, c3⟩ = Option.map stateOf (lookupRow es ⟨c0, c1, c2, c3⟩)
  unfold checkOne at hc
  have h0 := (all4_iff _).1 hc c0
  by_cases b0 : (s.closed c0 || !okAdd s.d1 (s.r1.eqb c0)) = true
  · rw [if_pos b0] at h0
    have hl : lookupRow es ⟨c0, c1, c2, c3⟩ = none :=
      lookupRow_none_of_all es ⟨c0, c1, c2, c3⟩ (fun r => r.c0.eqb c0)
        ((C4.eqb_iff c0 c0).2 rfl) h0
    rw [hl]; unfold step; rw [if_pos b0]; rfl
  · rw [if_neg b0] at h0
    have h1 := (all4_iff _).1 h0 c1
    by_cases b1 : (s.closed c1 || !okAdd s.d2 (s.r2.eqb c1)) = true
    · rw [if_pos b1] at h1
      have hl : lookupRow es ⟨c0, c1, c2, c3⟩ = none :=
        lookupRow_none_of_all es ⟨c0, c1, c2, c3⟩ (fun r => r.c0.eqb c0 && r.c1.eqb c1)
          (by simp [C4.eqb_iff]) h1
      rw [hl]; unfold step; rw [if_neg b0, if_pos b1]; rfl
    · rw [if_neg b1] at h1
      have h2 := (all4_iff _).1 h1 c2
      by_cases b2 : (s.closed c2 || !okAdd s.d3 (s.r3.eqb c2) ||
          (s.r2.eqb c1 && c0.eqb c1 && c1.eqb c2)) = true
      · rw [if_pos b2] at h2
        have hl : lookupRow es ⟨c0, c1, c2, c3⟩ = none :=
          lookupRow_none_of_all es ⟨c0, c1, c2, c3⟩
            (fun r => r.c0.eqb c0 && r.c1.eqb c1 && r.c2.eqb c2)
            (by simp [C4.eqb_iff]) h2
        rw [hl]; unfold step; rw [if_neg b0, if_neg b1]
        by_cases b2a : (s.closed c2 || !okAdd s.d3 (s.r3.eqb c2)) = true
        · rw [if_pos b2a]; rfl
        · rw [if_neg b2a]
          simp only [b2a, Bool.false_or, Bool.and_eq_true] at b2
          rcases b2 with ⟨⟨hv1, hh0⟩, hh1⟩
          simp [hv1, hh0, hh1, deg3]
      · rw [if_neg b2] at h2
        exact (optEqb_iff _ _).1 ((all4_iff _).1 h2 c3)

private def checkRange (lo hi : ℕ) : Bool :=
  (List.range (hi - lo)).all fun d =>
    if h : lo + d < 390 then checkOne ⟨lo + d, h⟩ else true

private lemma checkRange_sound {lo hi : ℕ} (h : checkRange lo hi = true)
    (i : Fin 390) (hlo : lo ≤ i.val) (hhi : i.val < hi) : checkOne i = true := by
  unfold checkRange at h
  have hmem : i.val - lo ∈ List.range (hi - lo) := List.mem_range.2 (by omega)
  have h1 := List.all_eq_true.1 h (i.val - lo) hmem
  have hlt : lo + (i.val - lo) < 390 := by omega
  rw [dif_pos hlt] at h1
  have heq : (⟨lo + (i.val - lo), hlt⟩ : Fin 390) = i := Fin.ext (show lo + (i.val - lo) = i.val by omega)
  rwa [heq] at h1

private def checkAll (p : Fin 390 → Bool) : Bool :=
  (List.range 390).all fun k => if h : k < 390 then p ⟨k, h⟩ else true

private lemma checkAll_sound {p : Fin 390 → Bool} (h : checkAll p = true) (i : Fin 390) :
    p i = true := by
  unfold checkAll at h
  have h1 := List.all_eq_true.1 h i.val (List.mem_range.2 i.isLt)
  rw [dif_pos i.isLt] at h1
  exact h1

private def T (v : Fin 390 → ℕ) (i : Fin 390) : ℕ :=
  ((edgesOf i).map fun e => v e.2).sum

private theorem h_step_0 : checkRange 0 130 = true := by decide +kernel
private theorem h_step_1 : checkRange 130 260 = true := by decide +kernel
private theorem h_step_2 : checkRange 260 390 = true := by decide +kernel

private theorem h_nodup : checkAll (fun i => nodupRows (edgesOf i)) = true := by decide +kernel
private theorem h_w0 : checkAll (fun i => (if isFinal (stateOf i) then 1 else 0) == w0Vec i) = true := by decide +kernel
private theorem h_w1 : checkAll (fun i => T w0Vec i == w1Vec i) = true := by decide +kernel
private theorem h_w2 : checkAll (fun i => T w1Vec i == w2Vec i) = true := by decide +kernel
private theorem h_a0_base : checkAll (fun i => T w2Vec i == a0Vec i) = true := by decide +kernel
private theorem h_T_a0 : checkAll (fun i => T a0Vec i == a0Vec i + a1Vec i + a2Vec i) = true := by decide +kernel
private theorem h_T_a1 : checkAll (fun i => T a1Vec i == a1Vec i + 2 * a2Vec i) = true := by decide +kernel
private theorem h_T_a2 : checkAll (fun i => T a2Vec i == a2Vec i) = true := by decide +kernel

private theorem h_init :
    (all4 fun c0 => all4 fun c1 => all4 fun c2 => all4 fun c3 =>
      optEqb (initState ⟨c0, c1, c2, c3⟩) (lookupRow initEdges ⟨c0, c1, c2, c3⟩)) = true := by
  decide +kernel

private theorem h_init_nodup : nodupRows initEdges = true := by decide +kernel
private theorem h_init_a0 : (initEdges.map fun e => a0Vec e.2).sum = 158 := by decide +kernel
private theorem h_init_a1 : (initEdges.map fun e => a1Vec e.2).sum = 76 := by decide +kernel
private theorem h_init_a2 : (initEdges.map fun e => a2Vec e.2).sum = 9 := by decide +kernel

private lemma step_eq (i : Fin 390) (r : Row) :
    step (stateOf i) r = Option.map stateOf (lookupRow (edgesOf i) r) := by
  apply checkOne_sound
  by_cases h1 : i.val < 130
  · exact checkRange_sound h_step_0 i (Nat.zero_le _) h1
  · by_cases h2 : i.val < 260
    · exact checkRange_sound h_step_1 i (by omega) h2
    · exact checkRange_sound h_step_2 i (by omega) i.isLt

private lemma ways_succ_eq_T (k : ℕ) (i : Fin 390) :
    ways (k + 1) (stateOf i) = T (fun j => ways k (stateOf j)) i := by
  change (∑ r : Row, match step (stateOf i) r with | none => 0 | some t => ways k t) =
      ((edgesOf i).map fun e => ways k (stateOf e.2)).sum
  have hcongr :
      (∑ r : Row, match step (stateOf i) r with | none => 0 | some t => ways k t) =
      (∑ r : Row, match lookupRow (edgesOf i) r with | none => 0 | some j => ways k (stateOf j)) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [step_eq i r]
    cases lookupRow (edgesOf i) r <;> rfl
  rw [hcongr]
  exact sum_lookupRow (edgesOf i) (checkAll_sound h_nodup i) (fun j => ways k (stateOf j))

private lemma list_sum_map_add {α : Type*} (l : List α) (f g : α → ℕ) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [ih]; omega

private lemma list_sum_map_mul {α : Type*} (l : List α) (f : α → ℕ) (c : ℕ) :
    (l.map fun x => f x * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp [ih, Nat.add_mul]

private lemma T_add (u v : Fin 390 → ℕ) (i : Fin 390) :
    T (fun j => u j + v j) i = T u i + T v i :=
  list_sum_map_add (edgesOf i) (fun e => u e.2) (fun e => v e.2)

private lemma T_mul (u : Fin 390 → ℕ) (c : ℕ) (i : Fin 390) :
    T (fun j => u j * c) i = T u i * c :=
  list_sum_map_mul (edgesOf i) (fun e => u e.2) c

private lemma ways_zero_eq (i : Fin 390) : ways 0 (stateOf i) = w0Vec i := by
  unfold ways
  exact beq_iff_eq.1 (checkAll_sound h_w0 i)

private lemma ways_one_eq (i : Fin 390) : ways 1 (stateOf i) = w1Vec i := by
  rw [ways_succ_eq_T 0 i]
  have hfn : (fun j => ways 0 (stateOf j)) = w0Vec := funext ways_zero_eq
  rw [hfn]
  exact beq_iff_eq.1 (checkAll_sound h_w1 i)

private lemma ways_two_eq (i : Fin 390) : ways 2 (stateOf i) = w2Vec i := by
  rw [ways_succ_eq_T 1 i]
  have hfn : (fun j => ways 1 (stateOf j)) = w1Vec := funext ways_one_eq
  rw [hfn]
  exact beq_iff_eq.1 (checkAll_sound h_w2 i)

private lemma ways_three_eq (i : Fin 390) : ways 3 (stateOf i) = a0Vec i := by
  rw [ways_succ_eq_T 2 i]
  have hfn : (fun j => ways 2 (stateOf j)) = w2Vec := funext ways_two_eq
  rw [hfn]
  exact beq_iff_eq.1 (checkAll_sound h_a0_base i)

private lemma ways_poly (m : ℕ) (i : Fin 390) :
    ways (m + 3) (stateOf i) = a0Vec i + a1Vec i * m + a2Vec i * m ^ 2 := by
  induction m generalizing i with
  | zero =>
    simp [ways_three_eq]
  | succ m ih =>
    have hsucc : m + 1 + 3 = (m + 3) + 1 := by omega
    rw [hsucc, ways_succ_eq_T (m + 3) i]
    have hfn : (fun j => ways (m + 3) (stateOf j)) =
        (fun j => (a0Vec j + a1Vec j * m) + a2Vec j * m ^ 2) := funext ih
    rw [hfn, T_add, T_add, T_mul, T_mul]
    have h0 : T a0Vec i = a0Vec i + a1Vec i + a2Vec i := beq_iff_eq.1 (checkAll_sound h_T_a0 i)
    have h1 : T a1Vec i = a1Vec i + 2 * a2Vec i := beq_iff_eq.1 (checkAll_sound h_T_a1 i)
    have h2 : T a2Vec i = a2Vec i := beq_iff_eq.1 (checkAll_sound h_T_a2 i)
    rw [h0, h1, h2]
    ring

private lemma init_eq (r : Row) :
    initState r = Option.map stateOf (lookupRow initEdges r) := by
  rcases r with ⟨c0, c1, c2, c3⟩
  have h0 := (all4_iff _).1 h_init c0
  have h1 := (all4_iff _).1 h0 c1
  have h2 := (all4_iff _).1 h1 c2
  have h3 := (all4_iff _).1 h2 c3
  exact (optEqb_iff _ _).1 h3

private lemma total_poly (m : ℕ) :
    (∑ r : Row, match initState r with | none => 0 | some s => ways (m + 3) s) =
      158 + 76 * m + 9 * m ^ 2 := by
  have hcongr :
      (∑ r : Row, match initState r with | none => 0 | some s => ways (m + 3) s) =
      (∑ r : Row, match lookupRow initEdges r with | none => 0 | some j => ways (m + 3) (stateOf j)) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [init_eq r]
    cases lookupRow initEdges r <;> rfl
  rw [hcongr, sum_lookupRow initEdges h_init_nodup]
  have hmap : (initEdges.map fun e => ways (m + 3) (stateOf e.2)).sum =
      (initEdges.map fun e => (a0Vec e.2 + a1Vec e.2 * m) + a2Vec e.2 * m ^ 2).sum :=
    congrArg List.sum (List.map_congr_left fun e _ => ways_poly m e.2)
  rw [hmap, list_sum_map_add, list_sum_map_add, list_sum_map_mul, list_sum_map_mul,
    h_init_a0, h_init_a1, h_init_a2]

theorem result : type_of% @OMA.S_oeis_a165378.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have hcard := card_Valid_eq_ways (m + 3)
  rw [hcard, total_poly m]
  have hring : 9 * (m + 4) ^ 2 + 4 * (m + 4) = (158 + 76 * m + 9 * m ^ 2) + 2 := by ring
  omega

end OMA.Allow165378

theorem OMA.solution : type_of% @OMA.S_oeis_a165378.main := OMA.Allow165378.result
