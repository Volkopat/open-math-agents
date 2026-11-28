import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1_H1_R1_H1_R1

/-!
Write-1 residual H1 (a=0 left into state 0): FAR/TNF certificates from
@hyprspacecoyote `BusyBeaver.BB_4.R2.H2.R1.H1` (`tv_b1`).
-/
-- Credit: @pageman

namespace OMA.BB4H2

open Turing Turing.BusyBeaver

abbrev Symbol := Fin 2
abbrev State := Fin 4
abbrev Key := State × Symbol
abbrev Machine4 := Machine Symbol State

structure Move where
  state : State
  write : Symbol
  left : Bool
  deriving DecidableEq

structure Table where
  t00 : Option Move
  t01 : Option Move
  t10 : Option Move
  t11 : Option Move
  t20 : Option Move
  t21 : Option Move
  t30 : Option Move
  t31 : Option Move
  deriving DecidableEq

def Table.empty : Table := ⟨none, none, none, none, none, none, none, none⟩

def Table.get (tb : Table) (q : State) (a : Symbol) : Option Move :=
  match q.val, a.val with
  | 0, 0 => tb.t00
  | 0, _ => tb.t01
  | 1, 0 => tb.t10
  | 1, _ => tb.t11
  | 2, 0 => tb.t20
  | 2, _ => tb.t21
  | _, 0 => tb.t30
  | _, _ => tb.t31

def Table.set (tb : Table) (q : State) (a : Symbol) (m : Move) : Table :=
  match q.val, a.val with
  | 0, 0 => { tb with t00 := some m }
  | 0, _ => { tb with t01 := some m }
  | 1, 0 => { tb with t10 := some m }
  | 1, _ => { tb with t11 := some m }
  | 2, 0 => { tb with t20 := some m }
  | 2, _ => { tb with t21 := some m }
  | _, 0 => { tb with t30 := some m }
  | _, _ => { tb with t31 := some m }

def Move.flip (m : Move) : Move := { m with left := !m.left }

def Table.flip (tb : Table) : Table :=
  ⟨tb.t00.map Move.flip, tb.t01.map Move.flip,
   tb.t10.map Move.flip, tb.t11.map Move.flip,
   tb.t20.map Move.flip, tb.t21.map Move.flip,
   tb.t30.map Move.flip, tb.t31.map Move.flip⟩

theorem Table.get_set_self (tb : Table) (q : State) (a : Symbol) (m : Move) :
    (tb.set q a m).get q a = some m := by
  fin_cases q <;> fin_cases a <;> rfl

theorem Table.get_set_ne (tb : Table) {q q' : State} {a a' : Symbol} (m : Move)
    (h : (q', a') ≠ (q, a)) : (tb.set q a m).get q' a' = tb.get q' a' := by
  fin_cases q <;> fin_cases a <;> fin_cases q' <;> fin_cases a' <;>
    first | rfl | exact absurd rfl h

theorem Table.get_flip (tb : Table) (q : State) (a : Symbol) :
    tb.flip.get q a = (tb.get q a).map Move.flip := by
  fin_cases q <;> fin_cases a <;> rfl

structure Position where
  state : State
  ls : List Symbol
  head : Symbol
  rs : List Symbol
  deriving DecidableEq

def startPos : Position := ⟨0, [], 0, []⟩

def push (a : Symbol) (xs : List Symbol) : List Symbol :=
  match a.val, xs with
  | 0, [] => []
  | _, xs => a :: xs

def symHead : List Symbol → Symbol
  | [] => 0
  | x :: _ => x

theorem symHead_eq_headI (xs : List Symbol) : symHead xs = xs.headI := by
  cases xs <;> rfl

def listEq : List Symbol → List Symbol → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x.val y.val && listEq xs ys
  | _, _ => false

theorem listEq_eq_true {xs ys : List Symbol} (h : listEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => simp [listEq] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp [listEq] at h
    | cons y ys =>
      simp only [listEq, Bool.and_eq_true] at h
      rw [Fin.ext (Nat.eq_of_beq_eq_true h.1), ih h.2]

def Position.move (c : Position) (m : Move) : Position :=
  if m.left then ⟨m.state, c.ls.tail, symHead c.ls, push m.write c.rs⟩
  else ⟨m.state, push m.write c.ls, symHead c.rs, c.rs.tail⟩

def Position.flip (c : Position) : Position := ⟨c.state, c.rs, c.head, c.ls⟩

theorem flip_move (c : Position) (m : Move) :
    (c.move m).flip = c.flip.move m.flip := by
  cases m with | mk q a d => cases d <;> rfl

theorem mk_push (a : Symbol) (xs : List Symbol) :
    ListBlank.mk (push a xs) = (ListBlank.mk xs).cons a := by
  fin_cases a
  · cases xs with
    | nil => exact (ListBlank.cons_head_tail (ListBlank.mk ([] : List Symbol))).symm
    | cons x xs => exact (ListBlank.cons_mk 0 (x :: xs)).symm
  · exact (ListBlank.cons_mk 1 xs).symm

def Position.view (c : Position) : Cfg Symbol State :=
  ⟨some c.state, ⟨c.head, ListBlank.mk c.ls, ListBlank.mk c.rs⟩⟩

theorem view_start : startPos.view = Machine.init [] := rfl

def Move.command (m : Move) : Option (Option State × Stmt Symbol) :=
  some (some m.state, Stmt.write m.write (if m.left then Dir.left else Dir.right))

def Matches (M : Machine4) (tb : Table) : Prop :=
  ∀ q a m, tb.get q a = some m → M q a = m.command

theorem matches_set {M : Machine4} {tb : Table} {q : State} {a : Symbol} {m : Move}
    (hm : Matches M tb) (h : M q a = m.command) : Matches M (tb.set q a m) := by
  intro q' a' m' hh
  by_cases e : (q', a') = (q, a)
  · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
    rw [Table.get_set_self] at hh
    exact (Option.some.inj hh) ▸ h
  · rw [Table.get_set_ne tb m e] at hh
    exact hm q' a' m' hh

theorem step_move {M : Machine4} {tb : Table} (hm : Matches M tb) (c : Position) (m : Move)
    (h : tb.get c.state c.head = some m) :
    M.step c.view = some (c.move m).view := by
  have he := hm c.state c.head m h
  cases m with
  | mk q a d =>
    cases d <;> simp [Position.view, Machine.step, he, Move.command, Position.move,
      Tape.write, Tape.move, mk_push, symHead_eq_headI]

theorem multi_succ_front (M : Machine4) (c : Cfg Symbol State) (k : ℕ) :
    M.multiStep c (k + 1) = (M.step c).bind (fun c' => M.multiStep c' k) := by
  induction k with
  | zero => rw [Machine.multiStep_one]; cases M.step c <;> rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, ih]
    cases h : M.step c with
    | none => rfl
    | some d => simp [Machine.multiStep_succ]

-- ============================================================
-- Guarded repeatable-segment checker
-- ============================================================

def takePad : ℕ → List Symbol → List Symbol
  | 0, _ => []
  | k + 1, [] => 0 :: takePad k []
  | k + 1, x :: xs => x :: takePad k xs

theorem takePad_foldr_drop (k : ℕ) (xs : List Symbol) :
    (takePad k xs).foldr ListBlank.cons (ListBlank.mk (xs.drop k)) = ListBlank.mk xs := by
  induction k generalizing xs with
  | zero => simp [takePad]
  | succ k ih =>
    cases xs with
    | nil =>
      simp only [takePad, List.foldr_cons, List.drop_nil]
      have h0 := ih []
      simp only [List.drop_nil] at h0
      rw [h0]
      exact ListBlank.cons_head_tail (ListBlank.mk [])
    | cons x xs =>
      simp only [takePad, List.foldr_cons, List.drop_succ_cons]
      rw [ih xs, ListBlank.cons_mk]

def runGuardedLeft (tb : Table) : ℕ → State → Symbol → List Symbol → List Symbol →
    Option (State × Symbol × List Symbol × List Symbol)
  | 0, q, a, near, rs => some (q, a, near, rs)
  | k + 1, q, a, near, rs =>
    match tb.get q a with
    | none => none
    | some m =>
      if m.left then
        match near with
        | [] => none
        | a' :: near' => runGuardedLeft tb k m.state a' near' (push m.write rs)
      else
        runGuardedLeft tb k m.state (symHead rs) (m.write :: near) rs.tail

def checkGuardedLeft (tb : Table) (p : ℕ) (q : State) (a : Symbol)
    (near rs : List Symbol) : Bool :=
  match runGuardedLeft tb p q a near rs with
  | none => false
  | some (q', a', near', rs') =>
    Nat.beq q'.val q.val && Nat.beq a'.val a.val && listEq rs' rs &&
      listEq (near'.take near.length) near && Nat.ble near.length near'.length

theorem runGuardedLeft_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (p : ℕ) (q : State) (a : Symbol) (near rs : List Symbol)
    {q' : State} {a' : Symbol} {near' rs' : List Symbol}
    (h : runGuardedLeft tb p q a near rs = some (q', a', near', rs'))
    (tail : ListBlank Symbol) :
    M.multiStep ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ p =
      some ⟨some q', ⟨a', near'.foldr ListBlank.cons tail, ListBlank.mk rs'⟩⟩ := by
  induction p generalizing q a near rs with
  | zero =>
    simp only [runGuardedLeft, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  | succ p ih =>
    simp only [runGuardedLeft] at h
    cases ht : tb.get q a with
    | none => simp [ht] at h
    | some m =>
      simp only [ht] at h
      have hM := hm q a m ht
      rw [multi_succ_front]
      cases hd : m.left with
      | true =>
        simp only [hd, ↓reduceIte] at h
        cases near with
        | nil => simp at h
        | cons x xs =>
          simp only at h
          have hstep : M.step ⟨some q, ⟨a, (x :: xs).foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ =
              some ⟨some m.state, ⟨x, xs.foldr ListBlank.cons tail, ListBlank.mk (push m.write rs)⟩⟩ := by
            simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, mk_push]
          rw [hstep, Option.bind_some]
          exact ih m.state x xs (push m.write rs) h
      | false =>
        simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
        have hstep : M.step ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ =
            some ⟨some m.state, ⟨symHead rs, (m.write :: near).foldr ListBlank.cons tail, ListBlank.mk rs.tail⟩⟩ := by
          simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, symHead_eq_headI]
        rw [hstep, Option.bind_some]
        exact ih m.state (symHead rs) (m.write :: near) rs.tail h

theorem runGuardedRight_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (p : ℕ) (q : State) (a : Symbol) (near ls : List Symbol)
    {q' : State} {a' : Symbol} {near' ls' : List Symbol}
    (h : runGuardedLeft tb.flip p q a near ls = some (q', a', near', ls'))
    (tail : ListBlank Symbol) :
    M.multiStep ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ p =
      some ⟨some q', ⟨a', ListBlank.mk ls', near'.foldr ListBlank.cons tail⟩⟩ := by
  induction p generalizing q a near ls with
  | zero =>
    simp only [runGuardedLeft, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  | succ p ih =>
    simp only [runGuardedLeft] at h
    rw [Table.get_flip] at h
    cases ht : tb.get q a with
    | none => simp [ht] at h
    | some m =>
      simp only [ht, Option.map_some] at h
      have hM := hm q a m ht
      rw [multi_succ_front]
      cases hd : m.left with
      | false =>
        simp only [Move.flip, hd, Bool.not_false, ↓reduceIte] at h
        cases near with
        | nil => simp at h
        | cons x xs =>
          simp only at h
          have hstep : M.step ⟨some q, ⟨a, ListBlank.mk ls, (x :: xs).foldr ListBlank.cons tail⟩⟩ =
              some ⟨some m.state, ⟨x, ListBlank.mk (push m.write ls), xs.foldr ListBlank.cons tail⟩⟩ := by
            simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, mk_push]
          rw [hstep, Option.bind_some]
          exact ih m.state x xs (push m.write ls) h
      | true =>
        simp only [Move.flip, hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        have hstep : M.step ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ =
            some ⟨some m.state, ⟨symHead ls, ListBlank.mk ls.tail, (m.write :: near).foldr ListBlank.cons tail⟩⟩ := by
          simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, symHead_eq_headI]
        rw [hstep, Option.bind_some]
        exact ih m.state (symHead ls) (m.write :: near) ls.tail h

theorem foldr_append (xs ys : List Symbol) (tail : ListBlank Symbol) :
    (xs ++ ys).foldr ListBlank.cons tail = xs.foldr ListBlank.cons (ys.foldr ListBlank.cons tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem checkGuardedLeft_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    {p : ℕ} {q : State} {a : Symbol} {near rs : List Symbol}
    (h : checkGuardedLeft tb p q a near rs = true) (tail : ListBlank Symbol) :
    ∃ tail', M.multiStep ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ p =
      some ⟨some q, ⟨a, near.foldr ListBlank.cons tail', ListBlank.mk rs⟩⟩ := by
  unfold checkGuardedLeft at h
  cases hr : runGuardedLeft tb p q a near rs with
  | none => simp [hr] at h
  | some res =>
    rcases res with ⟨q', a', near', rs'⟩
    simp only [hr, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hq, ha⟩, hrs⟩, htake⟩, _⟩ := h
    have hq' : q' = q := Fin.ext (Nat.eq_of_beq_eq_true hq)
    have ha' : a' = a := Fin.ext (Nat.eq_of_beq_eq_true ha)
    have hrs' : rs' = rs := listEq_eq_true hrs
    have htake' : near'.take near.length = near := listEq_eq_true htake
    subst hq'; subst ha'; subst hrs'
    refine ⟨(near'.drop near.length).foldr ListBlank.cons tail, ?_⟩
    rw [runGuardedLeft_sound hm p q' a' near rs' hr tail]
    congr 3
    rw [← foldr_append]
    congr 1
    conv_lhs => rw [← List.take_append_drop near.length near']
    rw [htake']

theorem checkGuardedRight_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    {p : ℕ} {q : State} {a : Symbol} {near ls : List Symbol}
    (h : checkGuardedLeft tb.flip p q a near ls = true) (tail : ListBlank Symbol) :
    ∃ tail', M.multiStep ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ p =
      some ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail'⟩⟩ := by
  unfold checkGuardedLeft at h
  cases hr : runGuardedLeft tb.flip p q a near ls with
  | none => simp [hr] at h
  | some res =>
    rcases res with ⟨q', a', near', ls'⟩
    simp only [hr, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hq, ha⟩, hls⟩, htake⟩, _⟩ := h
    have hq' : q' = q := Fin.ext (Nat.eq_of_beq_eq_true hq)
    have ha' : a' = a := Fin.ext (Nat.eq_of_beq_eq_true ha)
    have hls' : ls' = ls := listEq_eq_true hls
    have htake' : near'.take near.length = near := listEq_eq_true htake
    subst hq'; subst ha'; subst hls'
    refine ⟨(near'.drop near.length).foldr ListBlank.cons tail, ?_⟩
    rw [runGuardedRight_sound hm p q' a' near ls' hr tail]
    congr 3
    rw [← foldr_append]
    congr 1
    conv_lhs => rw [← List.take_append_drop near.length near']
    rw [htake']

structure HistItem where
  step : ℕ
  pos : ℕ
  c : Position

def findRepAux (tb : Table) (cur : HistItem) (minp maxp : ℕ) : List HistItem → Bool
  | [] => false
  | hi :: rest =>
    let minp' := if Nat.ble minp hi.pos then minp else hi.pos
    let maxp' := if Nat.ble maxp hi.pos then hi.pos else maxp
    let ok :=
      if Nat.ble (hi.step + 1) cur.step && Nat.beq hi.c.state.val cur.c.state.val && Nat.beq hi.c.head.val cur.c.head.val then
        let p := cur.step - hi.step
        let leftOk :=
          if Nat.ble hi.pos cur.pos && listEq hi.c.rs cur.c.rs then
            let dL := hi.pos - minp'
            let near := takePad dL hi.c.ls
            if listEq (takePad dL cur.c.ls) near then
              checkGuardedLeft tb p hi.c.state hi.c.head near hi.c.rs
            else false
          else false
        if leftOk then true
        else if Nat.ble cur.pos hi.pos && listEq hi.c.ls cur.c.ls then
          let dR := maxp' - hi.pos
          let near := takePad dR hi.c.rs
          if listEq (takePad dR cur.c.rs) near then
            checkGuardedLeft tb.flip p hi.c.state hi.c.head near hi.c.ls
          else false
        else false
      else false
    if ok then true else findRepAux tb cur minp' maxp' rest

def findRep (tb : Table) (cur : HistItem) (prev : List HistItem) : Bool :=
  findRepAux tb cur 1000 0 prev

def HistValid (M : Machine4) (hist : List HistItem) : Prop :=
  ∀ h ∈ hist, h.step ≤ 107 ∧ M.multiStep (Machine.init []) h.step = some h.c.view

def NoRepeatHyp (M : Machine4) : Prop :=
  ∀ (i p : ℕ) (q : State) (a : Symbol) (side : Bool)
      (near : List Symbol) (fixed : ListBlank Symbol), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank Symbol =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg Symbol State)
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')

theorem findRepAux_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hLoop : NoRepeatHyp M) {cur : HistItem} {prev : List HistItem}
    (hcur : cur.step ≤ 107) (hvalid : HistValid M prev)
    {minp maxp : ℕ} (h : findRepAux tb cur minp maxp prev = true) : False := by
  induction prev generalizing minp maxp with
  | nil => simp [findRepAux] at h
  | cons hi rest ih =>
    unfold findRepAux at h
    dsimp only at h
    set minp' := if Nat.ble minp hi.pos then minp else hi.pos
    set maxp' := if Nat.ble maxp hi.pos then hi.pos else maxp
    by_cases hcond : (Nat.ble (hi.step + 1) cur.step && Nat.beq hi.c.state.val cur.c.state.val && Nat.beq hi.c.head.val cur.c.head.val) = true
    · simp only [hcond, ↓reduceIte] at h
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq_true_eq] at hcond
      have ⟨hstep_hi, hrun_hi⟩ := hvalid hi (List.mem_cons_self ..)
      have hp_pos : 0 < cur.step - hi.step := by omega
      have hp_le : hi.step + (cur.step - hi.step) ≤ 107 := by omega
      by_cases hleft : (if Nat.ble hi.pos cur.pos && listEq hi.c.rs cur.c.rs then
          if listEq (takePad (hi.pos - minp') cur.c.ls) (takePad (hi.pos - minp') hi.c.ls) then
            checkGuardedLeft tb (cur.step - hi.step) hi.c.state hi.c.head (takePad (hi.pos - minp') hi.c.ls) hi.c.rs
          else false else false) = true
      · split at hleft
        · split at hleft
          · exact hLoop hi.step (cur.step - hi.step) hi.c.state hi.c.head true
              (takePad (hi.pos - minp') hi.c.ls) (ListBlank.mk hi.c.rs)
              hp_pos hp_le
              ⟨ListBlank.mk (hi.c.ls.drop (hi.pos - minp')), by
                simpa [Position.view, takePad_foldr_drop] using hrun_hi⟩
              (checkGuardedLeft_sound hm hleft)
          · contradiction
        · contradiction
      · simp only [hleft, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hright : (if Nat.ble cur.pos hi.pos && listEq hi.c.ls cur.c.ls then
            if listEq (takePad (maxp' - hi.pos) cur.c.rs) (takePad (maxp' - hi.pos) hi.c.rs) then
              checkGuardedLeft tb.flip (cur.step - hi.step) hi.c.state hi.c.head (takePad (maxp' - hi.pos) hi.c.rs) hi.c.ls
            else false else false) = true
        · split at hright
          · split at hright
            · exact hLoop hi.step (cur.step - hi.step) hi.c.state hi.c.head false
                (takePad (maxp' - hi.pos) hi.c.rs) (ListBlank.mk hi.c.ls)
                hp_pos hp_le
                ⟨ListBlank.mk (hi.c.rs.drop (maxp' - hi.pos)), by
                  simpa [Position.view, takePad_foldr_drop] using hrun_hi⟩
                (checkGuardedRight_sound hm hright)
            · contradiction
          · contradiction
        · simp only [hright, Bool.false_eq_true, ↓reduceIte] at h
          exact ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) h
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h
      exact ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) h

-- ============================================================
-- FAR (Finite Automata Reduction) certificate verifier
-- ============================================================

inductive CanStop (tb : Table) : Position → Prop
  | missing {c} : tb.get c.state c.head = none → CanStop tb c
  | move {c m} : tb.get c.state c.head = some m → CanStop tb (c.move m) → CanStop tb c

theorem canStop_flip {tb : Table} {c : Position} (h : CanStop tb c) :
    CanStop tb.flip c.flip := by
  induction h with
  | missing h => exact .missing (by simpa [Position.flip, Table.get_flip] using h)
  | @move c m h _ ih =>
    refine .move (m := m.flip) ?_ ?_
    · change tb.flip.get c.state c.head = some m.flip
      simp [Table.get_flip, h]
    · rwa [← flip_move]

theorem cannot_stop_run {M : Machine4} {tb : Table}
    (hm : Matches M tb) (c : Position) (hc : ¬ CanStop tb c) (k : ℕ) :
    M.multiStep c.view k ≠ none := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    cases h : tb.get c.state c.head with
    | none => exact (hc (.missing h)).elim
    | some m =>
      rw [multi_succ_front, step_move hm c m h, Option.bind_some]
      exact ih _ (fun hs => hc (.move h hs))

structure TapeDFA where
  extraStates : ℕ
  code : ℕ

abbrev TapeDFA.size (D : TapeDFA) : ℕ := D.extraStates + 1

def TapeDFA.next (D : TapeDFA) (a : Symbol) (l : Fin D.size) : Fin D.size :=
  ⟨(D.code * D.size / D.size ^ (2 * l.val + a.val)) % D.size,
    Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem TapeDFA.blank (D : TapeDFA) : D.next 0 0 = 0 := by
  apply Fin.ext
  simp [TapeDFA.next]

def TapeDFA.read (D : TapeDFA) (xs : List Symbol) : Fin D.size :=
  xs.foldr D.next 0

theorem TapeDFA.read_push (D : TapeDFA) (a : Symbol) (xs : List Symbol) :
    D.read (push a xs) = D.next a (D.read xs) := by
  fin_cases a
  · cases xs with
    | nil => exact D.blank.symm
    | cons x xs => rfl
  · rfl

theorem TapeDFA.read_pop (D : TapeDFA) (xs : List Symbol) :
    D.next xs.headI (D.read xs.tail) = D.read xs := by
  cases xs
  · exact D.blank
  · rfl

structure Certificate where
  mirror : Bool
  dfa : TapeDFA
  edges : ℕ
  blankReach : ℕ

abbrev Node (cert : Certificate) := Option (State × Fin cert.dfa.size)

def nodeId (cert : Certificate) : Node cert → ℕ
  | none => 4 * cert.dfa.size
  | some (q, l) => q.val * cert.dfa.size + l.val

def Certificate.edgeRow (cert : Certificate) (p : Node cert) (a : Symbol) : ℕ :=
  match p with
  | none => 2 ^ (4 * cert.dfa.size)
  | some _ => (cert.edges / 2 ^ ((2 * nodeId cert p + a.val) * (4 * cert.dfa.size + 1))) %
      2 ^ (4 * cert.dfa.size + 1)

def Certificate.edge (cert : Certificate) (p : Node cert) (a : Symbol)
    (q : Node cert) : Bool :=
  (cert.edgeRow p a).testBit (nodeId cert q)

theorem edge_none (cert : Certificate) (a : Symbol) (q : Node cert) :
    cert.edge none a q = q.isNone := by
  unfold Certificate.edge Certificate.edgeRow
  simp only [Nat.testBit_two_pow]
  rcases q with _ | ⟨q, l⟩
  · simp [nodeId]
  · have hq : q.val ≤ 3 := Nat.le_of_lt_succ q.isLt
    have hl : l.val < cert.dfa.size := l.isLt
    have hne : 4 * cert.dfa.size ≠ q.val * cert.dfa.size + l.val := by
      have : q.val * cert.dfa.size ≤ 3 * cert.dfa.size := Nat.mul_le_mul_right _ hq
      omega
    simp [nodeId, hne]

def Certificate.onBlank (cert : Certificate) (p : Node cert) : Bool :=
  cert.blankReach.testBit (nodeId cert p)

def unpack (val : ℕ) : Certificate :=
  let extra := val / 2 % 32
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := val / 64 / dfaBase
  let width := 4 * size + 1
  let initialBase := 2 ^ width
  ⟨val % 2 == 1, ⟨extra, val / 64 % dfaBase⟩, payload / initialBase, payload % initialBase⟩

def nodes (cert : Certificate) : List (Node cert) :=
  none :: (List.finRange 4).flatMap fun q =>
    (List.finRange cert.dfa.size).map fun l => some (q, l)

theorem allFin {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (a : Fin n) : p a = true := (List.all_eq_true.mp h) a (by simp)

theorem allNodes {cert : Certificate} {p : Node cert → Bool}
    (h : (nodes cert).all p = true) (a : Node cert) : p a = true := by
  refine (List.all_eq_true.mp h) a ?_
  rcases a with _ | ⟨q, l⟩ <;> simp [nodes]

def checkBlank (cert : Certificate) : Bool :=
  cert.onBlank (some (0, 0)) && !cert.onBlank none &&
    (nodes cert).all fun p =>
      if cert.onBlank p then
        let row := cert.edgeRow p 0
        (nodes cert).all fun q => !row.testBit (nodeId cert q) || cert.onBlank q
      else true

def checkAt (tb : Table) (cert : Certificate) (q : State) (a : Symbol)
    (l : Fin cert.dfa.size) : Bool :=
  let p : Node cert := some (q, l)
  let pRow := cert.edgeRow p a
  match tb.get q a with
  | none => pRow.testBit (4 * cert.dfa.size)
  | some m =>
    if m.left then
      (List.finRange cert.dfa.size).all fun l' => (List.finRange 2).all fun a' =>
        if Nat.beq (cert.dfa.next a' l').val l.val then
          let sRow := cert.edgeRow (some (m.state, l')) a'
          (nodes cert).all fun s =>
            if sRow.testBit (nodeId cert s) then
              let swRow := cert.edgeRow s m.write
              (nodes cert).all fun t => !swRow.testBit (nodeId cert t) || pRow.testBit (nodeId cert t)
            else true
        else true
    else pRow.testBit (nodeId cert (some (m.state, cert.dfa.next m.write l)))

def checkMachine (tb : Table) (cert : Certificate) : Bool :=
  (List.finRange 4).all fun q => (List.finRange 2).all fun a =>
    (List.finRange cert.dfa.size).all fun l => checkAt tb cert q a l

inductive Reads (cert : Certificate) : Node cert → ListBlank Symbol → Prop
  | done (t) : Reads cert none t
  | step {p q t} : cert.edge p t.head q = true → Reads cert q t.tail → Reads cert p t

theorem Reads.push {cert : Certificate} {p q : Node cert} {a : Symbol} {xs : ListBlank Symbol}
    (he : cert.edge p a q = true) (h : Reads cert q xs) : Reads cert p (xs.cons a) :=
  .step (by simpa using he) (by simpa using h)

theorem Reads.pop {cert : Certificate} {p : Node cert} {xs : ListBlank Symbol} {a : Symbol}
    (h : Reads cert p (xs.cons a)) : ∃ q, cert.edge p a q = true ∧ Reads cert q xs := by
  cases h with
  | done => exact ⟨none, by simp [edge_none], .done _⟩
  | step he hr => exact ⟨_, by simpa using he, by simpa using hr⟩

theorem no_read_blank {cert : Certificate} (hb : checkBlank cert = true) :
    ¬ Reads cert (some (0, 0)) (ListBlank.mk []) := by
  simp only [checkBlank, Bool.and_eq_true_iff, Bool.not_eq_true_eq_eq_false] at hb
  obtain ⟨⟨hstart, hsink⟩, hclosure⟩ := hb
  have each {p : Node cert} {t : ListBlank Symbol} (hr : Reads cert p t) :
      t = ListBlank.mk [] → cert.onBlank p = true → False := by
    induction hr with
    | done _ => intro _ hp; exact Bool.noConfusion (hp.symm.trans hsink)
    | @step p q t he _ ih =>
      rintro rfl hp
      have ht := allNodes hclosure p
      simp only [hp, if_true] at ht
      have hn := allNodes ht q
      have he0 : (cert.edgeRow p 0).testBit (nodeId cert q) = true := he
      simp [he0] at hn
      exact ih rfl hn
  exact fun hr => each hr rfl hstart

theorem reads_of_canStop {tb : Table} {cert : Certificate} (hchk : checkMachine tb cert = true)
    {c : Position} (hs : CanStop tb c) :
    Reads cert (some (c.state, cert.dfa.read c.ls)) ((ListBlank.mk c.rs).cons c.head) := by
  induction hs with
  | @missing c hh =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    simp only [checkAt, hh] at h
    exact Reads.push (show cert.edge (some (c.state, cert.dfa.read c.ls)) c.head none = true from h) (.done _)
  | @move c m hh _ ih =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    simp only [checkAt, hh] at h
    cases hd : m.left with
    | false =>
      have hstep : cert.edge (some (c.state, cert.dfa.read c.ls)) c.head
          (some (m.state, cert.dfa.next m.write (cert.dfa.read c.ls))) = true := by
        simpa [hd, Certificate.edge] using h
      refine Reads.push hstep ?_
      simpa [Position.move, hd, TapeDFA.read_push, symHead_eq_headI, ← ListBlank.head_mk, ← ListBlank.tail_mk]
        using ih
    | true =>
      have hr : Reads cert (some (m.state, cert.dfa.read c.ls.tail))
          (((ListBlank.mk c.rs).cons m.write).cons c.ls.headI) := by
        simpa [Position.move, hd, mk_push, symHead_eq_headI] using ih
      obtain ⟨s, he, hr⟩ := Reads.pop hr
      obtain ⟨t, hf, ht⟩ := Reads.pop hr
      simp only [hd, if_true] at h
      have h' := allFin (allFin h (cert.dfa.read c.ls.tail)) c.ls.headI
      have hbeq : Nat.beq (cert.dfa.next c.ls.headI (cert.dfa.read c.ls.tail)).val (cert.dfa.read c.ls).val = true := by
        simp [TapeDFA.read_pop]
      simp only [hbeq, if_true] at h'
      have h'' := allNodes h' s
      have he' : (cert.edgeRow (some (m.state, cert.dfa.read c.ls.tail)) c.ls.headI).testBit (nodeId cert s) = true := he
      simp only [he', if_true] at h''
      have h''' := allNodes h'' t
      have hf' : (cert.edgeRow s m.write).testBit (nodeId cert t) = true := hf
      simp [hf'] at h'''
      exact Reads.push h''' ht

def checkCertificate (tb : Table) (val : ℕ) : Bool :=
  let C := unpack val
  checkBlank C && checkMachine (if C.mirror then tb.flip else tb) C

theorem certificate_sound {tb : Table} {val : ℕ}
    (h : checkCertificate tb val = true) : ¬ CanStop tb startPos := by
  intro hs
  unfold checkCertificate at h
  have ⟨hb, hm⟩ := Bool.and_eq_true_iff.mp h
  apply no_read_blank hb
  have blank : (ListBlank.mk ([] : List Symbol)).cons 0 = ListBlank.mk [] :=
    ListBlank.cons_head_tail (ListBlank.mk [])
  split at hm
  · simpa only [Position.flip, startPos, TapeDFA.read, List.foldr_nil, blank] using
      (reads_of_canStop hm (canStop_flip hs))
  · simpa only [startPos, TapeDFA.read, List.foldr_nil, blank] using (reads_of_canStop hm hs)

-- ============================================================
-- Symmetry: swapping states 2 and 3
-- ============================================================

def swap23 : Equiv.Perm State := Equiv.swap (2 : State) (3 : State)

theorem swap23_0 : swap23 0 = 0 := by decide
theorem swap23_1 : swap23 1 = 1 := by decide
theorem swap23_2 : swap23 2 = 3 := by decide
theorem swap23_3 : swap23 3 = 2 := by decide
theorem swap23_inv (q : State) : swap23.symm q = swap23 q := by fin_cases q <;> decide

def reindex23 (M : Machine4) : Machine4 :=
  fun q a => (M (swap23 q) a).map fun (s, b) => (s.map swap23, b)

def mapCfg23 (c : Cfg Symbol State) : Cfg Symbol State :=
  ⟨c.q.map swap23, c.tape⟩

theorem reindex23_step (M : Machine4) (c : Cfg Symbol State) :
    (reindex23 M).step (mapCfg23 c) = (M.step c).map mapCfg23 := by
  obtain ⟨q, t⟩ := c
  cases q with
  | none => rfl
  | some q =>
    simp only [Machine.step, mapCfg23, Option.map_some, reindex23]
    have hinv : swap23 (swap23 q) = q := by fin_cases q <;> decide
    rw [hinv]
    cases M q t.head with
    | none => rfl
    | some entry => rfl

theorem reindex23_multi (M : Machine4) (c : Cfg Symbol State) (k : ℕ) :
    (reindex23 M).multiStep (mapCfg23 c) k = (M.multiStep c k).map mapCfg23 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
    cases M.multiStep c k with
    | none => rfl
    | some c' => exact reindex23_step M c'

theorem mapCfg23_init : mapCfg23 (Machine.init []) = Machine.init [] := by
  simp [mapCfg23, Machine.init, swap23_0]


def sp0Table : Table :=
  ⟨some ⟨1, 1, false⟩, some ⟨0, 1, true⟩, some ⟨0, 1, true⟩, some ⟨2, 0, false⟩,
   some ⟨3, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 0, true⟩⟩

def sp1Table : Table :=
  ⟨some ⟨1, 1, false⟩, some ⟨1, 0, false⟩, some ⟨2, 1, true⟩, some ⟨1, 1, false⟩,
   none, some ⟨3, 0, true⟩, some ⟨0, 1, false⟩, some ⟨3, 1, true⟩⟩

def m0Table : Table :=
  ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨2, 1, false⟩, some ⟨3, 1, false⟩,
   some ⟨0, 1, true⟩, some ⟨1, 0, false⟩, some ⟨0, 1, false⟩, none⟩

def tblOfList (entries : List ℕ) : Machine4 := fun q a =>
  let v := entries[2*q.val+a.val]?.getD 16
  if v = 16 then none else some (some ⟨v / 4 % 4, Nat.mod_lt _ (by decide)⟩,
    Stmt.write ⟨v / 2 % 2, Nat.mod_lt _ (by decide)⟩ (if v % 2 = 0 then Dir.right else Dir.left))

theorem eq_sp0_of_matches {M : Machine4} (hm : Matches M sp0Table) (hMiss : ∃ q a, M q a = none) :
    M = tblOfList [6,3,3,8,15,10,16,1] := by
  obtain ⟨qm, am, hMmiss⟩ := hMiss
  have hqm : qm = 3 ∧ am = 0 := by
    fin_cases qm <;> fin_cases am
    · exfalso; change M 0 0 = none at hMmiss; rw [hm 0 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 0 1 = none at hMmiss; rw [hm 0 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 0 = none at hMmiss; rw [hm 1 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 1 = none at hMmiss; rw [hm 1 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 2 0 = none at hMmiss; rw [hm 2 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 2 1 = none at hMmiss; rw [hm 2 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exact ⟨rfl, rfl⟩
    · exfalso; change M 3 1 = none at hMmiss; rw [hm 3 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
  rcases hqm with ⟨rfl, rfl⟩
  funext q a
  fin_cases q <;> fin_cases a
  · exact hm 0 0 _ rfl
  · exact hm 0 1 _ rfl
  · exact hm 1 0 _ rfl
  · exact hm 1 1 _ rfl
  · exact hm 2 0 _ rfl
  · exact hm 2 1 _ rfl
  · exact hMmiss
  · exact hm 3 1 _ rfl

theorem eq_sp1_of_matches {M : Machine4} (hm : Matches M sp1Table) (hMiss : ∃ q a, M q a = none) :
    M = tblOfList [6,4,11,6,16,13,2,15] := by
  obtain ⟨qm, am, hMmiss⟩ := hMiss
  have hqm : qm = 2 ∧ am = 0 := by
    fin_cases qm <;> fin_cases am
    · exfalso; change M 0 0 = none at hMmiss; rw [hm 0 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 0 1 = none at hMmiss; rw [hm 0 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 0 = none at hMmiss; rw [hm 1 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 1 = none at hMmiss; rw [hm 1 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exact ⟨rfl, rfl⟩
    · exfalso; change M 2 1 = none at hMmiss; rw [hm 2 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 3 0 = none at hMmiss; rw [hm 3 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 3 1 = none at hMmiss; rw [hm 3 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
  rcases hqm with ⟨rfl, rfl⟩
  funext q a
  fin_cases q <;> fin_cases a
  · exact hm 0 0 _ rfl
  · exact hm 0 1 _ rfl
  · exact hm 1 0 _ rfl
  · exact hm 1 1 _ rfl
  · exact hMmiss
  · exact hm 2 1 _ rfl
  · exact hm 3 0 _ rfl
  · exact hm 3 1 _ rfl

def runPos (tb : Table) : ℕ → Position → Option Position
  | 0, c => some c
  | k + 1, c =>
    match tb.get c.state c.head with
    | none => none
    | some m => runPos tb k (c.move m)

theorem runPos_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (k : ℕ) (c : Position) {c' : Position} (h : runPos tb k c = some c') :
    M.multiStep c.view k = some c'.view := by
  induction k generalizing c with
  | zero =>
    simp only [runPos, Option.some.injEq] at h; subst h; rfl
  | succ k ih =>
    simp only [runPos] at h
    cases ht : tb.get c.state c.head with
    | none => simp [ht] at h
    | some m =>
      simp only [ht] at h
      rw [multi_succ_front, step_move hm c m ht, Option.bind_some]
      exact ih (c.move m) h

theorem run_add (M : Machine4) (x : Cfg Symbol State) (m n : ℕ) :
    M.multiStep x (m + n) = (M.multiStep x m).bind (fun y => M.multiStep y n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, Machine.multiStep_succ, ih]
    cases M.multiStep x m <;> simp

theorem m0_not_halting {M : Machine4} (hm : Matches M m0Table) (hHalts : M.IsHalting) : False := by
  have h85 : ∃ c85, runPos m0Table 85 startPos = some c85 ∧
      checkGuardedLeft m0Table.flip 29 c85.state c85.head [] c85.ls = true := by
    refine ⟨(runPos m0Table 85 startPos).getD startPos, ?_, ?_⟩ <;> decide +kernel
  obtain ⟨c85, hrun, hcyc⟩ := h85
  have hM85 : M.multiStep (Machine.init []) 85 = some c85.view := runPos_sound hm 85 startPos hrun
  let cfg (tail : ListBlank Symbol) : Cfg Symbol State :=
    ⟨some c85.state, ⟨c85.head, ListBlank.mk c85.ls, tail⟩⟩
  have hEnter : ∃ tail, M.multiStep (Machine.init []) 85 = some (cfg tail) :=
    ⟨ListBlank.mk c85.rs, hM85⟩
  have hStep : ∀ tail, ∃ tail', M.multiStep (cfg tail) 29 = some (cfg tail') := by
    intro tail
    simpa [cfg] using checkGuardedRight_sound hm hcyc tail
  have hRec (m : ℕ) : ∃ tail, M.multiStep (Machine.init []) (85 + 29 * m) = some (cfg tail) := by
    induction m with
    | zero => simpa using hEnter
    | succ m ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨t', ht'⟩ := hStep t
      refine ⟨t', ?_⟩
      rw [Nat.mul_succ, ← Nat.add_assoc, run_add M _ (85 + 29 * m) 29, ht]
      exact ht'
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hHalts
  obtain ⟨t, ht⟩ := hRec (k + 1)
  have hnone := Machine.multiStep_eq_none_mono hk (by omega : k + 1 ≤ 85 + 29 * (k + 1))
  rw [ht] at hnone
  contradiction

def GoodMachine (M : Machine4) : Prop :=
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) ∧
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) ∧
  (∃ q a, M q a = none) ∧
  NoRepeatHyp M ∧
  M.IsHalting ∧
  (M ≠ tblOfList [6,3,3,8,15,10,16,1] ∧ reindex23 M ≠ tblOfList [6,3,3,8,15,10,16,1]) ∧
  (M ≠ tblOfList [6,4,11,6,16,13,2,15] ∧ reindex23 M ≠ tblOfList [6,4,11,6,16,13,2,15])

theorem reindex23_invol (M : Machine4) : reindex23 (reindex23 M) = M := by
  funext q a
  have hinv : swap23 (swap23 q) = q := by fin_cases q <;> decide
  simp only [reindex23, hinv]
  cases M q a with
  | none => rfl
  | some p =>
    rcases p with ⟨s, b⟩
    cases s with
    | none => rfl
    | some s =>
      have hs : swap23 (swap23 s) = s := by fin_cases s <;> decide
      simp [hs]

theorem goodMachine_reindex23 {M : Machine4} (hG : GoodMachine M) :
    GoodMachine (reindex23 M) := by
  obtain ⟨⟨q0, t0, hRun⟩, hForm, ⟨qm, am, hMiss⟩, hLoop, hHalts, ⟨hsp0, hsp0'⟩, ⟨hsp1, hsp1'⟩⟩ := hG
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨hsp0', by rwa [reindex23_invol]⟩, ⟨hsp1', by rwa [reindex23_invol]⟩⟩
  · refine ⟨swap23 q0, t0, ?_⟩
    rw [← mapCfg23_init, reindex23_multi, hRun]; rfl
  · intro q a
    rcases hForm (swap23 q) a with h | ⟨q', z, h⟩
    · left; simp [reindex23, h]
    · right; exact ⟨swap23 q', z, by simp [reindex23, h]⟩
  · exact ⟨swap23 qm, am, by
      have : swap23 (swap23 qm) = qm := by fin_cases qm <;> decide
      simp [reindex23, this, hMiss]⟩
  · intro i p q a side near fixed hp hle cfg hEnter hCycle
    let cfgM : ListBlank Symbol → Cfg Symbol State := fun tail =>
      let free := near.foldr ListBlank.cons tail
      ⟨some (swap23 q), if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩
    have hmap : ∀ tail, mapCfg23 (cfgM tail) = cfg tail := by
      intro tail
      have : swap23 (swap23 q) = q := by fin_cases q <;> decide
      simp [mapCfg23, cfgM, cfg, this]
    apply hLoop i p (swap23 q) a side near fixed hp hle
    · obtain ⟨tail, ht⟩ := hEnter
      rw [← mapCfg23_init, reindex23_multi] at ht
      cases hMi : M.multiStep (Machine.init []) i with
      | none => simp [hMi] at ht
      | some c' =>
        simp only [hMi, Option.map_some, Option.some.injEq] at ht
        refine ⟨tail, ?_⟩
        congr 1
        obtain ⟨q', t'⟩ := c'
        simp only [mapCfg23, cfg, Cfg.mk.injEq] at ht
        rcases ht with ⟨hq', ht'⟩
        cases q' with
        | none => simp at hq'
        | some q' =>
          simp only [Option.map_some, Option.some.injEq] at hq'
          have : q' = swap23 q := by rw [← hq']; fin_cases q' <;> decide
          simp [this, ht']
    · intro tail
      obtain ⟨tail', ht'⟩ := hCycle tail
      rw [← hmap tail, reindex23_multi] at ht'
      cases hMp : M.multiStep (cfgM tail) p with
      | none => simp [hMp] at ht'
      | some c' =>
        simp only [hMp, Option.map_some, Option.some.injEq] at ht'
        refine ⟨tail', ?_⟩
        congr 1
        obtain ⟨q', t'⟩ := c'
        simp only [mapCfg23, cfg, Cfg.mk.injEq] at ht'
        rcases ht' with ⟨hq', ht''⟩
        cases q' with
        | none => simp at hq'
        | some q' =>
          simp only [Option.map_some, Option.some.injEq] at hq'
          have : q' = swap23 q := by rw [← hq']; fin_cases q' <;> decide
          simp [this, ht'']
  · obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hHalts
    refine (Machine.isHalting_iff_exists_haltsAt _).mpr ⟨k, ?_⟩
    unfold Machine.HaltsAfter
    rw [← mapCfg23_init, reindex23_multi, hk]; rfl

def UsesOnly01 (tb : Table) : Prop :=
  tb.t20 = none ∧ tb.t21 = none ∧ tb.t30 = none ∧ tb.t31 = none ∧
  (∀ q a m, tb.get q a = some m → m.state = 0 ∨ m.state = 1)

theorem matches_reindex23 {M : Machine4} {tb : Table}
    (hm : Matches M tb) (h01 : UsesOnly01 tb) : Matches (reindex23 M) tb := by
  intro q a m hget
  have hms := h01.2.2.2.2 q a m hget
  have hq : q = 0 ∨ q = 1 := by
    fin_cases q
    · exact Or.inl rfl
    · exact Or.inr rfl
    · fin_cases a <;> simp [Table.get, h01.1, h01.2.1] at hget
    · fin_cases a <;> simp [Table.get, h01.2.2.1, h01.2.2.2.1] at hget
  have hsq : swap23 q = q := by rcases hq with rfl | rfl <;> decide
  have hsm : swap23 m.state = m.state := by rcases hms with h | h <;> rw [h] <;> decide
  simp only [reindex23, hsq, hm q a m hget, Move.command, Option.map_some, hsm]

theorem histValid_reindex23 {M : Machine4} {hist : List HistItem}
    (hv : HistValid M hist)
    (h01 : ∀ h ∈ hist, h.c.state = 0 ∨ h.c.state = 1) :
    HistValid (reindex23 M) hist := by
  intro h hh
  have ⟨hle, hrun⟩ := hv h hh
  refine ⟨hle, ?_⟩
  rw [← mapCfg23_init, reindex23_multi, hrun]
  have hs : swap23 h.c.state = h.c.state := by
    rcases h01 h hh with hs | hs <;> rw [hs] <;> decide
  simp [mapCfg23, Position.view, hs]

-- ============================================================
-- Stateful DFS Tree Verifier
-- ============================================================

def holes (tb : Table) : Finset Key :=
  Finset.univ.filter fun k => tb.get k.1 k.2 = none

theorem holes_set (tb : Table) (q : State) (a : Symbol) (m : Move) :
    holes (tb.set q a m) = (holes tb).erase (q, a) := by
  ext ⟨q', a'⟩
  simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  by_cases e : (q', a') = (q, a)
  · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
    simp [Table.get_set_self]
  · simp [Table.get_set_ne tb m e, e]

def moves12 : List Move :=
  [⟨0, 0, false⟩, ⟨0, 0, true⟩, ⟨0, 1, false⟩, ⟨0, 1, true⟩,
   ⟨1, 0, false⟩, ⟨1, 0, true⟩, ⟨1, 1, false⟩, ⟨1, 1, true⟩,
   ⟨2, 0, false⟩, ⟨2, 0, true⟩, ⟨2, 1, false⟩, ⟨2, 1, true⟩]

def moves16 : List Move :=
  [⟨0, 0, false⟩, ⟨0, 0, true⟩, ⟨0, 1, false⟩, ⟨0, 1, true⟩,
   ⟨1, 0, false⟩, ⟨1, 0, true⟩, ⟨1, 1, false⟩, ⟨1, 1, true⟩,
   ⟨2, 0, false⟩, ⟨2, 0, true⟩, ⟨2, 1, false⟩, ⟨2, 1, true⟩,
   ⟨3, 0, false⟩, ⟨3, 0, true⟩, ⟨3, 1, false⟩, ⟨3, 1, true⟩]

def movesAllowed (used2 : Bool) : List Move :=
  if used2 then moves16 else moves12

theorem mem_movesAllowed (used2 : Bool) (m : Move) (h : used2 = false → m.state ≠ 3) :
    m ∈ movesAllowed used2 := by
  obtain ⟨q, a, d⟩ := m
  cases used2
  · have h3 := h rfl
    fin_cases q <;> fin_cases a <;> cases d <;> simp_all [movesAllowed, moves12]
  · fin_cases q <;> fin_cases a <;> cases d <;> simp [movesAllowed, moves16]

inductive StepResult where
  | rep
  | done
  | missing (q : State) (a : Symbol) (rem : ℕ) (cur : HistItem) (prev : List HistItem)

def stepLoop (tb : Table) : ℕ → HistItem → List HistItem → StepResult
  | 0, _, _ => .done
  | rem + 1, cur, prev =>
    match tb.get cur.c.state cur.c.head with
    | none => .missing cur.c.state cur.c.head (rem + 1) cur prev
    | some m =>
      let nc := cur.c.move m
      let nstep := cur.step + 1
      let npos := if m.left then cur.pos - 1 else cur.pos + 1
      let ncur : HistItem := ⟨nstep, npos, nc⟩
      let nprev := cur :: prev
      if (Nat.beq nstep 6 || Nat.beq nstep 12 || Nat.beq nstep 24 || Nat.beq nstep 48 || Nat.beq nstep 107) &&
          findRep tb ncur nprev then
        .rep
      else
        stepLoop tb rem ncur nprev

def checkMoves (f : Move → List ℕ → Option (List ℕ)) : List Move → List ℕ → Option (List ℕ)
  | [], certs => some certs
  | m :: ms, certs =>
    match f m certs with
    | none => none
    | some rest => checkMoves f ms rest

def checkTree : ℕ → Bool → Table → ℕ → HistItem → List HistItem → List ℕ → Option (List ℕ)
  | 0, _, _, _, _, _, _ => none
  | holesLeft + 1, used2, tb, rem, cur, prev, certs =>
    match stepLoop tb rem cur prev with
    | .rep => some certs
    | .done =>
      match certs with
      | [] => none
      | v :: rest =>
        if Nat.beq v 0 then
          if tb == sp0Table || tb == sp1Table || tb == m0Table then some rest else none
        else if checkCertificate tb v then some rest else none
    | .missing q a rem' cur' prev' =>
      if Nat.beq holesLeft 0 then some certs
      else
        checkMoves (fun m rest =>
          checkTree holesLeft (used2 || Nat.beq m.state.val 2) (tb.set q a m) rem' cur' prev' rest)
          (movesAllowed used2) certs

theorem checkMoves_each {f : Move → List ℕ → Option (List ℕ)} {ms : List Move}
    {a b : List ℕ} (h : checkMoves f ms a = some b) {m : Move} (hm : m ∈ ms) :
    ∃ x y, f m x = some y := by
  induction ms generalizing a with
  | nil => simp at hm
  | cons head tail ih =>
    unfold checkMoves at h
    cases hh : f head a with
    | none => simp [hh] at h
    | some mid =>
      simp only [hh] at h
      rcases List.mem_cons.mp hm with rfl | ht
      · exact ⟨a, mid, hh⟩
      · exact ih h ht

theorem stepLoop_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hG : GoodMachine M)
    {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    (hsum : cur.step + rem = 107)
    (hv : HistValid M (cur :: prev))
    (h01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) :
    match stepLoop tb rem cur prev with
    | .rep => False
    | .done => True
    | .missing q a rem' cur' prev' =>
      tb.get q a = none ∧ cur'.c.state = q ∧ cur'.c.head = a ∧
      cur'.step + rem' = 107 ∧ 0 < rem' ∧
      HistValid M (cur' :: prev') ∧
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur' :: prev', h.c.state = 0 ∨ h.c.state = 1) := by
  induction rem generalizing cur prev with
  | zero => simp [stepLoop]
  | succ rem ih =>
    unfold stepLoop
    cases ht : tb.get cur.c.state cur.c.head with
    | none =>
      exact ⟨ht, rfl, rfl, hsum, Nat.succ_pos _, hv, h01⟩
    | some m =>
      simp only [ht]
      have ⟨hcur_le, hcur_run⟩ := hv cur (List.mem_cons_self ..)
      let ncur : HistItem := ⟨cur.step + 1, if m.left then cur.pos - 1 else cur.pos + 1, cur.c.move m⟩
      have hncur_run : M.multiStep (Machine.init []) (cur.step + 1) = some ncur.c.view := by
        rw [Machine.multiStep_succ, hcur_run]
        exact step_move hm cur.c m ht
      have hnv : HistValid M (ncur :: cur :: prev) := by
        intro h hh
        rcases List.mem_cons.mp hh with rfl | hh'
        · exact ⟨by dsimp [ncur]; omega, hncur_run⟩
        · exact hv h hh'
      have hn01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ ncur :: cur :: prev, h.c.state = 0 ∨ h.c.state = 1 := by
        intro hu
        have ⟨u, hprev01⟩ := h01 hu
        refine ⟨u, fun h hh => ?_⟩
        rcases List.mem_cons.mp hh with rfl | hh'
        · have hms := u.2.2.2.2 cur.c.state cur.c.head m ht
          cases hd : m.left <;> simpa [ncur, Position.move, hd] using hms
        · exact hprev01 h hh'
      by_cases hrep : ((Nat.beq (cur.step + 1) 6 || Nat.beq (cur.step + 1) 12 || Nat.beq (cur.step + 1) 24 ||
          Nat.beq (cur.step + 1) 48 || Nat.beq (cur.step + 1) 107) && findRep tb ncur (cur :: prev)) = true
      · rw [if_pos hrep]
        simp only [Bool.and_eq_true] at hrep
        exact findRepAux_sound hm hG.2.2.2.1 (by dsimp [ncur]; omega) hv hrep.2
      · rw [if_neg hrep]
        exact ih (by dsimp [ncur]; omega) hnv hn01

theorem usesOnly01_set {tb : Table} (h01 : UsesOnly01 tb) {q : State} {a : Symbol} {m : Move}
    (hq : q = 0 ∨ q = 1) (hm : m.state = 0 ∨ m.state = 1) :
    UsesOnly01 (tb.set q a m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.2.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.2.2.1
  · intro q' a' m' hh
    by_cases e : (q', a') = (q, a)
    · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
      rw [Table.get_set_self] at hh
      exact (Option.some.inj hh) ▸ hm
    · rw [Table.get_set_ne tb m e] at hh
      exact h01.2.2.2.2 q' a' m' hh

theorem checkTree_sound {holesLeft : ℕ} {used2 : Bool} {tb : Table}
    {rem : ℕ} {cur : HistItem} {prev : List HistItem} {a b : List ℕ}
    (hCount : (holes tb).card ≤ holesLeft)
    (hCheck : checkTree holesLeft used2 tb rem cur prev a = some b) :
    ∀ M : Machine4, GoodMachine M → Matches M tb →
      cur.step + rem = 107 →
      HistValid M (cur :: prev) →
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) →
      False := by
  induction holesLeft generalizing used2 tb rem cur prev a b with
  | zero => simp [checkTree] at hCheck
  | succ holesLeft ih =>
    intro M hG hm hsum hv hu
    unfold checkTree at hCheck
    have hstep := stepLoop_sound hm hG hsum hv hu
    cases hsl : stepLoop tb rem cur prev with
    | rep => rw [hsl] at hstep; exact hstep
    | done =>
      simp only [hsl] at hCheck
      cases a with
      | nil => simp at hCheck
      | cons v rest =>
        simp only at hCheck
        by_cases hv0 : Nat.beq v 0 = true
        · simp only [hv0, ↓reduceIte] at hCheck
          split at hCheck
          · rename_i hsp
            simp only [Bool.or_eq_true, beq_iff_eq] at hsp
            rcases hsp with (rfl | rfl) | rfl
            · exact hG.2.2.2.2.2.1.1 (eq_sp0_of_matches hm hG.2.2.1)
            · exact hG.2.2.2.2.2.2.1 (eq_sp1_of_matches hm hG.2.2.1)
            · exact m0_not_halting hm hG.2.2.2.2.1
          · simp at hCheck
        · simp only [hv0, Bool.false_eq_true, ↓reduceIte] at hCheck
          split at hCheck
          · rename_i hcert
            have hns := certificate_sound hcert
            obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hG.2.2.2.2.1
            exact cannot_stop_run hm startPos hns (k + 1) hk
          · simp at hCheck
    | missing q a rem' cur' prev' =>
      simp only [hsl] at hCheck hstep
      obtain ⟨hnone, hq_eq, ha_eq, hsum', hrem_pos, hv', hu'⟩ := hstep
      have hcur'_run := (hv' cur' (List.mem_cons_self ..)).2
      -- M must define (q, a) as some (some q', z) since cur'.step < 107 and M runs past 107
      have hM_def : ∃ q' z, M q a = some (some q', z) := by
        rcases hG.2.1 q a with hMnone | hMsome
        · have hnone_next : M.multiStep (Machine.init []) (cur'.step + 1) = none := by
            rw [Machine.multiStep_succ, hcur'_run]
            simp [Machine.step, Position.view, hq_eq, ha_eq, hMnone]
          have h107 := Machine.multiStep_eq_none_mono hnone_next (by omega : cur'.step + 1 ≤ 107)
          obtain ⟨q0, t0, hrun107⟩ := hG.1
          rw [h107] at hrun107
          contradiction
        · exact hMsome
      obtain ⟨q', ⟨w, d⟩, hMqa⟩ := hM_def
      split at hCheck
      · -- holesLeft == 0: (holes tb).card ≤ 1 and (q, a) ∈ holes tb, so M has no none!
        rename_i h0
        have h0' : holesLeft = 0 := Nat.eq_of_beq_eq_true h0
        have hmem : (q, a) ∈ holes tb := by simp [holes, hnone]
        have hcard1 : (holes tb).card = 1 :=
          le_antisymm (by omega) (Finset.card_pos.mpr ⟨_, hmem⟩)
        obtain ⟨qm, am, hMmiss⟩ := hG.2.2.1
        have hqm_mem : (qm, am) ∈ holes tb := by
          simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and]
          cases hget : tb.get qm am with
          | none => rfl
          | some m =>
            have := hm qm am m hget
            rw [hMmiss] at this
            simp [Move.command] at this
        have heq_key : (qm, am) = (q, a) := by
          have hsub : ({(q, a)} : Finset Key) ⊆ holes tb := Finset.singleton_subset_iff.mpr hmem
          have hEq := Finset.eq_of_subset_of_card_le hsub (by simp [hcard1])
          rw [← hEq, Finset.mem_singleton] at hqm_mem
          exact hqm_mem
        rcases Prod.mk.inj heq_key with ⟨rfl, rfl⟩
        rw [hMmiss] at hMqa
        contradiction
      · -- Branch on movesAllowed used2
        let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
        have hm_cmd : M q a = m.command := by
          cases d <;> simpa [m, Move.command] using hMqa
        have hmem_hole : (q, a) ∈ holes tb := by simp [holes, hnone]
        have hcard_next : (holes (tb.set q a m)).card ≤ holesLeft := by
          rw [holes_set, Finset.card_erase_of_mem hmem_hole]
          omega
        by_cases hswap : used2 = false ∧ q' = 3
        · rcases hswap with ⟨hu2, rfl⟩
          have ⟨h01, hprev01⟩ := hu' hu2
          let m2 : Move := ⟨2, w, match d with | .left => true | .right => false⟩
          have hmem_m2 : m2 ∈ movesAllowed used2 := mem_movesAllowed used2 m2 (by simp [m2])
          obtain ⟨x, y, hxy⟩ := checkMoves_each hCheck hmem_m2
          have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
          have hsq : swap23 q = q := by rcases hq01 with rfl | rfl <;> decide
          have hM2qa : (reindex23 M) q a = m2.command := by
            cases d <;> simp [reindex23, hsq, hm_cmd, m, m2, Move.command, swap23_3]
          have hcard2 : (holes (tb.set q a m2)).card ≤ holesLeft := by
            rw [holes_set, Finset.card_erase_of_mem hmem_hole]
            omega
          exact ih hcard2 hxy (reindex23 M) (goodMachine_reindex23 hG)
            (matches_set (matches_reindex23 hm h01) hM2qa) hsum'
            (histValid_reindex23 hv' hprev01) (by simp [m2])
        · have hmem_m : m ∈ movesAllowed used2 :=
            mem_movesAllowed used2 m (fun hu2 h3 => hswap ⟨hu2, h3⟩)
          obtain ⟨x, y, hxy⟩ := checkMoves_each hCheck hmem_m
          refine ih hcard_next hxy M hG (matches_set hm hm_cmd) hsum' hv' ?_
          intro hnext_u2
          simp only [Bool.or_eq_false_iff] at hnext_u2
          have ⟨h01, hprev01⟩ := hu' hnext_u2.1
          have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
          have hm01 : m.state = 0 ∨ m.state = 1 := by
            have hne2 : q' ≠ 2 := by intro h2; subst h2; simp [m] at hnext_u2
            have hne3 : q' ≠ 3 := fun h3 => hswap ⟨hnext_u2.1, h3⟩
            fin_cases q' <;> simp_all [m]
          exact ⟨usesOnly01_set h01 hq01 hm01, hprev01⟩

def TreeValid (tb : Table) (used2 : Bool) (rem : ℕ) (cur : HistItem) (prev : List HistItem) : Prop :=
  ∀ M : Machine4, GoodMachine M → Matches M tb →
    cur.step + rem = 107 →
    HistValid M (cur :: prev) →
    (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) →
    False

theorem branch_one {tb : Table} {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    {q : State} {a : Symbol} {rem' : ℕ} {cur' : HistItem} {prev' : List HistItem}
    (hsl : stepLoop tb rem cur prev = .missing q a rem' cur' prev')
    (hChildren : ∀ m ∈ movesAllowed used2,
      TreeValid (tb.set q a m) (used2 || Nat.beq m.state.val 2) rem' cur' prev') :
    TreeValid tb used2 rem cur prev := by
  intro M hG hm hsum hv hu
  have hstep := stepLoop_sound hm hG hsum hv hu
  simp only [hsl] at hstep
  obtain ⟨hnone, hq_eq, ha_eq, hsum', hrem_pos, hv', hu'⟩ := hstep
  have hcur'_run := (hv' cur' (List.mem_cons_self ..)).2
  have hM_def : ∃ q' z, M q a = some (some q', z) := by
    rcases hG.2.1 q a with hMnone | hMsome
    · have hnone_next : M.multiStep (Machine.init []) (cur'.step + 1) = none := by
        rw [Machine.multiStep_succ, hcur'_run]
        simp [Machine.step, Position.view, hq_eq, ha_eq, hMnone]
      have h107 := Machine.multiStep_eq_none_mono hnone_next (by omega : cur'.step + 1 ≤ 107)
      obtain ⟨q0, t0, hrun107⟩ := hG.1
      rw [h107] at hrun107
      contradiction
    · exact hMsome
  obtain ⟨q', ⟨w, d⟩, hMqa⟩ := hM_def
  let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
  have hm_cmd : M q a = m.command := by cases d <;> simpa [m, Move.command] using hMqa
  by_cases hswap : used2 = false ∧ q' = 3
  · rcases hswap with ⟨hu2, rfl⟩
    have ⟨h01, hprev01⟩ := hu' hu2
    let m2 : Move := ⟨2, w, match d with | .left => true | .right => false⟩
    have hmem_m2 : m2 ∈ movesAllowed used2 := mem_movesAllowed used2 m2 (by simp [m2])
    have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
    have hsq : swap23 q = q := by rcases hq01 with rfl | rfl <;> decide
    have hM2qa : (reindex23 M) q a = m2.command := by
      cases d <;> simp [reindex23, hsq, hm_cmd, m, m2, Move.command, swap23_3]
    exact hChildren m2 hmem_m2 (reindex23 M) (goodMachine_reindex23 hG)
      (matches_set (matches_reindex23 hm h01) hM2qa) hsum'
      (histValid_reindex23 hv' hprev01) (by simp [m2])
  · have hmem_m : m ∈ movesAllowed used2 :=
      mem_movesAllowed used2 m (fun hu2 h3 => hswap ⟨hu2, h3⟩)
    refine hChildren m hmem_m M hG (matches_set hm hm_cmd) hsum' hv' ?_
    intro hnext_u2
    simp only [Bool.or_eq_false_iff] at hnext_u2
    have ⟨h01, hprev01⟩ := hu' hnext_u2.1
    have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
    have hm01 : m.state = 0 ∨ m.state = 1 := by
      have hne2 : q' ≠ 2 := by intro h2; subst h2; simp [m] at hnext_u2
      have hne3 : q' ≠ 3 := fun h3 => hswap ⟨hnext_u2.1, h3⟩
      fin_cases q' <;> simp_all [m]
    exact ⟨usesOnly01_set h01 hq01 hm01, hprev01⟩



def baseTable : Table := Table.empty.set 0 0 ⟨1, 1, false⟩
def h0 : HistItem := ⟨0, 128, startPos⟩
def h1 : HistItem := ⟨1, 129, startPos.move ⟨1, 1, false⟩⟩

private theorem mk_good_ne_sp1 (M : Machine4) (h : M 1 0 ≠ some (some 2, Stmt.write 1 Dir.left))
    (h2 : M 1 0 ≠ some (some 3, Stmt.write 1 Dir.left)) :
    M ≠ tblOfList [6,4,11,6,16,13,2,15] ∧ reindex23 M ≠ tblOfList [6,4,11,6,16,13,2,15] := by
  refine ⟨fun heq => h (by rw [heq]; rfl), fun heq => h2 ?_⟩
  have h10 := congrFun (congrFun heq 1) 0
  have hrhs : tblOfList [6,4,11,6,16,13,2,15] 1 0 = some (some 2, Stmt.write 1 Dir.left) := rfl
  rw [hrhs] at h10
  simp only [reindex23, swap23_1] at h10
  cases hM : M 1 0 with
  | none => simp [hM] at h10
  | some p =>
    rcases p with ⟨s, z⟩
    cases s with
    | none => simp [hM] at h10
    | some s =>
      simp only [hM, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h10
      rcases h10 with ⟨hs, hz⟩
      have hs3 : s = 3 := by revert hs; fin_cases s <;> decide
      subst hs3; subst hz; rfl

private theorem mk_good_ne_sp0 (M : Machine4) (h : M 1 0 ≠ some (some 0, Stmt.write 1 Dir.left)) :
    M ≠ tblOfList [6,3,3,8,15,10,16,1] ∧ reindex23 M ≠ tblOfList [6,3,3,8,15,10,16,1] := by
  refine ⟨fun heq => h (by rw [heq]; rfl), fun heq => h ?_⟩
  have h10 := congrFun (congrFun heq 1) 0
  have hrhs : tblOfList [6,3,3,8,15,10,16,1] 1 0 = some (some 0, Stmt.write 1 Dir.left) := rfl
  rw [hrhs] at h10
  simp only [reindex23, swap23_1] at h10
  cases hM : M 1 0 with
  | none => simp [hM] at h10
  | some p =>
    rcases p with ⟨s, z⟩
    cases s with
    | none => simp [hM] at h10
    | some s =>
      simp only [hM, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h10
      rcases h10 with ⟨hs, hz⟩
      have hs0 : s = 0 := by revert hs; fin_cases s <;> decide
      subst hs0; subst hz; rfl

private theorem mk_base_hm_hv {M : Machine4}
    (hFirst : M 0 0 = some (some 1, Stmt.write 1 Dir.right)) :
    Matches M baseTable ∧ HistValid M [h1, h0] := by
  have hm0 : Matches M baseTable := by
    intro q a m hget
    fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
    subst hget; exact hFirst
  have hrun1 : M.multiStep (Machine.init []) 1 = some h1.c.view := by
    rw [Machine.multiStep_one]
    exact step_move hm0 startPos ⟨1, 1, false⟩ rfl
  refine ⟨hm0, ?_⟩
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl
  · exact ⟨by decide, hrun1⟩
  · exact ⟨by decide, rfl⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_0 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 0, false⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_1 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 0, true⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_2 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 1, false⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_3 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 1, true⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1162218284650688, 1162218284650688, 1161359425540288, 1161221986717888, 1161221986717888, 1161359425540288, 
    1161359425540288, 1128650902669377, 1128650902669377, 1128650902669377, 1128650902669377, 1128650902669377, 
    1161292860035264, 1161361575121088, 1128650902669377, 1161368023863744, 1143784436142784, 1143646997320384, 
    1143646997320384, 1143784436142784, 1143784436142784, 1128184898717761, 1128665935054913, 1128184898717761, 
    1128184898717761, 1128184898717761, 1128184898717761, 1128184898717761, 1128184898717761, 1128184898717761, 
    1128184898717761, 1128665935054913, 1128184898717761, 1128184898717761, 1128184898717761, 1128184898717761, 
    1128665935054913, 1134782236919873, 1128391273353920, 1134988343120832, 1130590296609472, 2923103628717052382937775513005439984455848630850, 
    1130590296609472, 1128184898717761, 1128665935054913, 1128184898717761, 2923728051605758559929334276757643509464395952962, 1134782236919873, 
    1161187628746817, 1128185100044353, 1161363586158784, 105639286212673, 1130849991004352, 1130849991004352, 
    1130849991004352, 1130865023389888, 1130865023389888, 2923192831697908886674815267011186569844562596674, 79268187015233, 88064280037441, 
    1161157566337216, 1161221986717888, 1161221986717888, 1161359425540288, 1161359425540288, 106105088837697, 
    106105088837697, 106105088837697, 106105088837697, 106105088837697, 1161155420950720, 1161224136298688, 
    1161361575121088, 123695392443150858820591777138241287708825726074733356504626524195064473634394268577294083227923073218533723088961746289330626501757291695701286401593906351367146623914162247, 106105088837697, 176478262204609, 90575098211533486263658875835525405515358351472487469792651516296289590232579100934942599969632568283198045465077605830062341624718609275858506052794192554468313079524934, 996326080379589994933119520496743091780632193719475123663182334198861550534239569946444288701343641990105059288028069548690203341894586471298313726532562400440301548252742, 
    996326080379589994946213082928518195671226700079501682212343895443687410653028751724423254853736349715181338242544107204094981917810529656369385040256671782517122620501574, 106105088837697, 106105088837697, 1161164019274176, 1161234884202944, 1161234884202944, 
    1161368023863744, 315644150232281319585688704440047274065724013520332675535085965997850670123086943329007405005672771716, 106105088837697, 188397414118873100197553748895780383986991256386, 513258889805605223322046716863513927553819518280132834263281228172320860999911596063740260963625352875095824763134914377741866617114409547089353692289987584628235068979270, 996326080379589994946213082928518195671226700243443580738849358166764116412959026040972814590148060441793607815440897892094600917346023932979611893342875396401053266259526, 
    33283751113574826881503524441640741768576169950950972639539258418565105856761192235198831410344587396, 106105088837697, 106105088837697, 1161157566337216, 1161226285879488, 1161226285879488, 
    1161226285879488, 1161363724701888, 123695392498937389873713026031008379330873147588545895400391457557604110633460828093831015139243145793763408518099314117208101559145445604203144583998661393877280829614632518, 106105088837697, 106105088837697, 960990105657226062769635081172618079611504952060852645863230911642428452751397879683873220130559456907866490428904379317648157635879586238909394047167586864342476995411672461361448301686504701911649763469843899544976159534999512425332082780975633555593363457496956553, 
    3957316615499431320073279171356055356640806738310767369103099384446583731722692406816474953440271611483648845082893338714131617477384177224370051912442134216524142926776938055, 30946491887137527512635394397712577111473074304103548947696709224767658918871193176911689626346964846920216999509526631456566954319190070711612740200181544283574470532443718, 106105088837697, 106105088837697, 1161157566337216, 1161226285879488, 
    1161226285879488, 1161226285879488, 1161363724701888, 315644150232281319585688704314262946501856155622764999339044754014754774866838305152974215541193719940, 92779092257213226545578303205766881518739472876252974769390464281075765781395168786082674482541344247867599410983594215192131751852105624239955368227590427282549589180460614, 106105088837697, 
    106105088837697, 271725294602967471171253495722962312279370570131803326628008940989019454074612551576159206000636453783149834841471288035893460953275693217190243603702515851463238383480390, 961842399437839889284103792053779316418144121300324526075100356006171277760259907745812225731337023463209014380993258277996721322364797791244751441692418865127267592749633778063342900308201234248835943932972174217609624296591492558636969619703306718336253992246956552, 996326080379589994946213082928518195671226700158828398485643417724627314700239057465505778076212840529566937250655311516815746776064003636950500376106014795642844413603398, 33283751113574826881503524289022424008528992618783719834858524410198564458202100755346952774217908356, 106105088837697, 
    176478262204609, 106105088837697, 1161234884202944, 1161234884202944, 106107236321345, 1161221986717888, 
    1161221986717888, 106112068159553, 996326080379589994946213082928518195671226700158828416733697537429820499893377464952279651801182834835163047546087203246882595951977229169225299658196849499922083123211846, 1147976328483520, 1143646997320384, 1143646997320384, 
    1143784436142784, 1128253834531520, 1128253834531520, 1147976328483520, 1143646997320384, 1143646997320384, 
    1143784436142784, 1143784436142784, 105639084886081, 105639084886081, 105707804362817, 105639084886081, 
    105639084886081, 106120121223233, 105639084886081, 105639084886081, 105639084886081, 105639084886081, 
    105639084886081, 105639084886081, 105639084886081, 105639084886081, 106120121223233, 105639084886081, 
    105639084886081, 105639084886081, 105639084886081, 106120121223233, 176145402239169, 1147976328483520, 
    1143646997320384, 1143646997320384, 1143784436142784, 1128185119183552, 1128253834531520, 1128253834531520, 
    1128391273353920, 1136981212206016, 1139248950809536, 1134988343120832, 1130384142439104, 1130452857787072, 
    1130590296609472, 1130384142439104, 1130452857787072, 1130590296609472, 2923192852775435601243924277142057057921917850434, 1143646997320384, 
    1143646997320384, 105639084886081, 105639084886081, 105639084886081, 105639084886081, 106120121223233, 
    105639084886081, 105639084886081, 105639084886081, 105639084886081, 123695392498937389873713026031008379330873147599292021254716145819189694294113370892891617908248666722941868301592323487903906592442059199090883659927010629186415777931374150, 105639084886081, 
    105639084886081, 49893186923645615822906216981397004028374829219736362062085763478657007460236387236461919470222713540, 316745585854529, 1161230442172608, 176076613619904, 176076613619904, 
    1161359425540288, 1161361575121088, 1161368023863744, 1161363724701888, 1161363724701888, 2924441678176966633867303379489457218622389785410, 
    2930150663503272602656521107953261480259629388610, 105639286212673, 105639286212673, 51381112945374834761192540617938412326780670786, 105639286212673, 2925868931314211233750039684930286717407825302338, 
    2923059026700301817224644585331632889757373110082, 2923728051608375487825929132855121896340814123842, 2923103628360840061931396888499865490196269177666, 2923192831681916551344901494836330691074061308738, 105639286212673, 105639286212673, 
    176076613619904, 2928712635670479399483352131567433629247236739906, 565252326492225, 72671117248577, 72671117248577, 1461596415848995981871032070828548605059021151042, 
    72671117248577, 176473898094784, 176476045578432, 176488930480320, 176488930480320, 97053213352571288021877315120692359634201088834, 
    283777349781569, 33283751113574826881503524498662970085759807968101034111121810745119851012841042868601256650153881732, 583933376907551283496523466295691399312212449876432247584513562488549585930299222531723288864935749, 33283751113574826881503524289022424008528992619056471116423766856593064236336656465239706865408163972, 72671117248577, 72671117248577, 
    72671117248577, 72671117248577, 1461596415859629846402130605115119909435766479682, 72671117248577]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_4 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 0, false⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_5 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 0, true⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_6 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 1, false⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_7 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 1, true⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_8 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, false⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ true 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [581659384877760, 581659384877760, 581110165934784, 581110165934784, 1128253618194497, 1128665935054913, 
    1128665935054913, 360713906557120, 290547021648064, 290547021648064, 564067198833344, 581659384877760, 
    146252780278464, 146252780278464, 291388315145152, 563517979890368, 563517979890368, 581110165934784, 
    145703561335488, 145703561335488, 290839096202176, 1128184898717761, 1128253618194497, 1128665935054913, 
    290555619971520, 290555619971520, 290555619971520, 290839096202176]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_9 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ true 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161155213136064, 1161155213136064, 1130850393657536, 1130850393657536, 1130850393657536, 316730754998593, 
    1130850393657536, 1130850393657536, 1128665935258433, 1133048951410880, 1130849991004352, 1130849991004352, 
    1162186007519553, 1161155213136064, 1161155213136064, 1130849923895488, 1130849923895488, 1130849923895488, 
    1135265169413056, 317211791335745, 317211791335745, 1128655266975936, 1161226147074240, 1128655266975936, 
    1128655334084800, 28545062747135879611981261830047916220198430531, 531567574968091860714533399135376918339997661924541019674117510384365364133959247851279918596547944709, 531566814648499095465420701781988736595641843044821287822516628326810816182114398730380326603230026309, 531566814648499095465420701781988736595641843044821287822516628326810816182114398730380326603230026309, 1134784602837952, 
    1135263489463232, 300169428214081, 316936913428801, 2923048573263167642360227223487895748593718404931, 1128260532637888, 1128260532637888, 
    531566925528426725179185920008209103178318478741675602874657015773459190990796046109048847669484842245, 1128329252114624, 531566909688434973202219461557242787687172698874170557935882800277009552915750199992038822820593639685, 531566909688434973202219461557252614587781686025470080892501606030944956469237596925188191146167443717, 1130384389705920, 1130865426043072, 
    1130865426043072, 1130384389705920, 1130865426043072, 1130865426043072, 1130384389705920, 2923728051608344334045009583117213363704120234818, 
    1135263489463232, 2923728073386415816985071244773188239337285768002, 794795350131107216651266565750479472874606026378291508152101953328944784947054013552650451611032133, 316730754998593, 1128322339901632, 531567574968091860714533399350101250042629270675420179531867449285253672062817069944619042340714030981, 
    565716990365888, 1130865023389888, 1130865023389888, 581110166196928, 581110166196928, 1134988328444737, 
    284791230702401, 290547021385920, 290547021385920, 565716990365888, 1130383919943872, 1130383919943872, 
    1130865426043072, 1130865426043072, 567916009492672, 567916009492672, 1130383919943872, 1130383919943872, 
    1130383919943872, 1130865426043072, 1130865426043072, 567916009492672, 567916009492672, 1130383919943872, 
    1130383919943872, 1130383919943872, 563517962850496, 563517962850496, 2923103649793976862218096171306685863984187315010, 581110166196928, 
    290839096202176, 24263303375345770896986316015129411222748800835, 275742584636184205613406846034137913783194350178934808980844662576456463492384977937197697392998981, 1128391258678081, 1128665935258433, 494660804241896241172350407130366198807300135516730496499336552710643233838780815666659548674794953127261701276425510203606449996155290121596743439904417874637138464651790919, 
    1134781968687937, 531566814648499095465418945014108932579159164373903206171963734832622162826772809524370449743269241029, 291388300469057, 1134781968687937, 1134988328444737, 513258889803854699919224884912180393193610003644175699051626634350090433525623781843474305260102692833725396076192513019967347631296573566286687020510030334223086119733831, 
    291388300469057, 1464361709306320934963368874146888773213339329347, 531502440922007731439362805349204800220111663201298714905114586039107019415045319257765639161909625540, 1134781968687937, 290555619971520, 290555619971520, 
    290555619971520, 290839096202176]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_10 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ true 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [105624522197057, 1161226151530688, 316936913428801, 106105088837697, 317211321573697, 317211791335745, 
    159451353191104, 581110165934784, 572314072912832, 581110165934784, 736462602516499213080195151913596401921747358530, 581659384877760, 
    581659384877760, 581110165934784, 581110165934784, 79457985762240, 79457985762240, 290564218295232, 
    106120121223233, 106120121223233, 532021042251963798731965620738255825052933231100913922460738971489517686740326361572558854738082546564, 564720867784877012998555968431296901372581001159985163451773454085468456024885130562598110765965919108, 33218934237609691583668613689565492339516550384879083642386580358529374957665948028891745604532228357, 18160212513472, 
    354116836790464, 354116836790464, 283954251043008, 1461551814220297022957588449697953938337899284291, 146235180978368, 146235180978368, 
    360713906557120, 290547021648064, 290547021648064, 1464361729701995221157789699309467283913485390658, 1464361729701995221157789699309467283913485390658, 564067198833344, 
    159446517158592, 564067198833344, 564067198833344, 581659384877760, 146252377625280, 581659384877760, 
    291388315145152, 563517979890368, 563517979890368, 563517979890368, 581110165934784, 581110165934784, 
    290839096202176, 105639084886081, 105707804362817, 106120121223233, 535654799719835974809215259227172449821233679073785839725814537201633001844478443033808768575106990980, 3965015557583982423210411951551003875558362109770769960731021193173264684250448327117364812627585909760122287926861108762682700131797655803188129827033392869388816682412105286, 
    183045214891533273169480434135240809249369039683, 290839096202176, 290555619971520, 290555619971520, 354123285533120, 354123285533120, 
    290343012798656, 290343012798656, 369516448321984, 11440630863596311125393325258501935482577883714, 91366501655132336094549906607691565591341044546, 290555619971520, 
    564067198833344, 581659384877760, 354123285533120, 283958550204864, 354123285533120, 283958550204864, 
    847200578180032, 1461551814220317792224250751522732397916760115011, 146239480139968, 146239480139968, 360720355299776, 290555619971520, 
    360720355299776, 290555619971520]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1_11 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 0, true⟩, none, none, none, none, none⟩ true 105 ⟨2, 128, ⟨0, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161223999721664, 1161223999721664, 176474300747968, 176474300747968, 2928712635670479399483487531775739301778671276866, 387108089112897, 
    176474300747968, 176474300747968, 531501949882260587742187830062414698959871411178907549532385743774434787400884770463977069734789423493, 176473830985920, 176473830985920, 317211791335745, 
    2928723437625836206828661337346230193136414507587, 1161157427728576, 1161226147205312, 1161226147205312, 1161226147205312, 176476045578432, 
    176476045578432, 176476045578432, 16674316169753703049456973052159692846972879344314065496498823346327746508403284215685671574029906629, 106109453144256, 176476045578432, 194641827349582167937822535207896829731286410724276174072915146918076379398640739720950428249068677, 
    194641827349460347516036140984851240202421779949205371133701919113346631041889312156360769311577221, 188398111022467325020803783223353612469522154051, 1161234884202944, 1161234884202944, 531566909688435445270766647306599960300812085340397854899768740023933445296751185224118506156267121221, 531826329162053553315165129197468780527532868576765067630728426049125342907269368677077696553064311365, 
    106191460044992, 2928713681049811849681036917535521245733725422147, 2928713681049811849681036917535521245733725422147, 11441676211027492211214883842859275298204041795, 66502657011482485683975418660535663683493140541512266197393429665551231760379979799990423058212956741, 387374377085249, 
    387099499178305, 316936913428801, 106191460044992, 176008296796352, 176489333133504, 2928713768122220799590905130185202007702459400771, 
    176489333133504, 176008296796352, 176489333133504, 2928713681009934867830658483561302505169797268035, 176489333133504, 97064015254883712830528379875874712688498053954, 
    1161226084225216, 106107238420672, 1161226285748416, 1161226285748416, 736461225021556852340425886462068721602793577282, 531570869686402707761685416603420552789875510672134056138890254989290451153210782960536848898386220933, 
    531570869687339291746654147297259676408698011019253240184879360078160204937694825583285702377858848645, 531505989080216822504544562357606592115969372888303575522164052474287359415636455443273412827559155589, 1128309922992320, 1135113162068416, 2923728051603682931639956306296919650334832333634, 1130440228868288, 
    1130440228868288, 531570869686402707761685416603420552789875510672134056138890254989290451153210782960536848898386220933, 1130440228868288, 1135113162068416, 1161226084225216, 106107238420672, 
    2928713681017920316200195249965283578443787682627, 317218233786689, 176485040402881, 317218233786689, 317218233786689, 1161226147205312, 
    1161226147205312, 176476045578432, 531501949882260587742187830250252627534123313290520250389698900651112097731945054691486857074338734469, 531503961561272569453176849296600449553407749980215696019373356001629649039305350429159374259900167621, 1161226147205312, 1161226147205312, 
    176476045578432, 1161226285748416, 736461225021558150419592299215655364399091159874, 913583824049833597744960904047466594291126219279848021177616615091961792534202176697279498445727389573, 4217239420481885636211905528504706373481450877615487711356448544200414901534734349183358764247695492, 581395120223413659886870286864224289706534368493510732575586968646840280950643763726017139457468416132, 
    1128309922992320, 1135113162068416, 387108089112897, 316943355879745, 387108089112897, 316943355879745, 
    1130440228868288, 1130440228868288, 1161230442172608, 1161230442172608, 387108089112897, 2923059026705577860035993389379773591928667391811, 
    2923036725960379045539581087516726097270450176579, 290280733413568, 28545062744819344518725395727102842299561808706, 28545062755111126011002843102967246484179797827, 17127081213463163188300992345426861088336527939, 194641827349460347516036140984851240202468760084615670170484725776112606321775166234804832251647109, 
    290280733413568, 290280733413568, 105707806462144, 105707806462144, 105776593178816, 28545062745826614654543029232837489191295128386, 
    105639086985408, 105707873702080, 106189312561344, 88528943911104, 105707806462144, 176076613619904, 
    176076613619904, 176488930480320, 176076613619904, 176076613619904, 176488930480320, 299635189224128, 
    299635189224128, 284242026435264, 290564218295232, 730798207961675627337607787192139971889641572163, 730778694777745561334076002866873053985015599682, 565716988727488, 
    1464361729701974451891127397484692202047229989698, 1464361729701974451891127397484692202047229989698, 567916014080192, 567916014080192, 581110166196928, 581110166196928, 
    730778694809626588843191397572614116631780540995, 863134346928961, 300184393491265, 161645995504577, 300184393491265, 581659370218305, 
    581659370218305, 1143578061710145, 1154573446425409, 1143784421466945, 830569081465494324235659410972036305767317320715633077299430481097281786347336683455359527211440297861, 4152422219672461384471280166053395763395061385806633017960438100971533611579564929654828621615088516, 
    4249743129117221364078374533308045464327129430935861725777469754760466304662076933127327270353524613, 564720867784877012998555968431296901372581001159985163451773454085468475277328890482360673887077024644, 2076195269844596962911890946643072449601311215635376849574122079255351821539917221265510242929882628, 564720867784877012998555968431296901372581001159985163451773454085468475277328890482360673887077024644, 616365761107369935875276490466496853443364381645574111911633086191001298933290101796430467974059909, 581659370218305, 
    1128184898921281, 3957286424721394490114101738518282362886921201196299553201562905280450810657515740549079966798692764162922757159122101148760297488599953218604748133382347946997899749722705479, 3957286659672668496337989637600028909787294103027356811861162672253209267508687166180195617051010144819530808975358738149843456798279515958469346339026478223724564940902911559, 1136981260380993, 1134988328444737, 1136981260380993, 
    1136981260380993, 531567321528221940808921109181222713137757811364297980594643159978147318175541457877436991737884720517, 22881958582964738358842411450472348493912524611, 284791230702401, 144053809460161, 284791230702401, 
    1128184898921281, 290547021648064, 290547021648064, 18160195473600, 551485156945714612346271653900167931923794792963912399726678340277892810707364535652063001792758468, 23549675405742972881518131472947460019920626499, 
    158897683960000, 158897683960000, 18160195473600, 105707806462144, 105707806462144, 106189312561344, 
    80007754748864, 88528943911104, 176007827034304, 176076613619904, 176076613619904, 176489333133504, 
    176489333133504, 158897683960000, 158897683960000, 176076613619904, 176076613619904, 176076613619904, 
    176007827034304, 176076613619904, 176076613619904, 176489333133504, 176489333133504, 158897683960000, 
    158897683960000, 176145270247616, 176076613619904, 176076613619904, 176076613619904, 176076613619904, 
    286441049690816, 286441049690816, 286441049690816, 286441049690816, 3965015557583982423210411951551003875558362109944019509041653996947765856354101691510085722095635277211358800638834888165820845461381827266788346797746215999017726515454369351, 282043003179712, 
    290839096202176, 290839096202176, 97064015254883712830221311546324348197566157634, 299635189224128, 284242026435264, 368231320314093308013187036825078897603753612098, 
    286441049690816, 286441049690816, 282043003179712, 290839096202176, 308431282246592, 176076613619904, 
    176076613619904, 18160195473600, 18160195473600, 563517963374784, 563517963374784, 563517963374784, 
    565716988727488, 1464361729701995221157789699309470661626090820418, 494660810374815527393634228433672799510426386911147855795382443246755255418035739300749860498064824530080026711131690642690439663831144486552856469863088204487509116225629766, 567916014080192, 265751470930873414351167253733339532646648254310819408008978200344445803270900394969617927887542042756, 567916014080192, 
    563517963374784, 265864505112980430064054651196173104792529041277022130300530685823542496871090893010757219391945687172, 581110166196928, 66437760565274650815393729049215226922465765636340765606658184082304408279524570091370759689827819909, 265783407325208761503692730946094334871500034189964688377712750467639293199055656237129324008665565701, 1464361710667450402964035378057445116266693083971, 
    531501949882260587756833167802570655661729585301604032896135132833126849084466260000481359766468469125, 1136981260380993, 1136981260380993, 72852317671872, 283958550204864, 531501949882260587742189368830738681766497685397094971057175438684888048951616581383737290994751938949, 
    1128185167358785, 1128391258678081, 1128185167358785, 1154573446425409, 1152580514489153, 291388300469057, 
    265783407325208909025111734337395657818138524017505032669723278016951772654539461688596411280733293061, 129777061125114666772444043603941826967452216841934935959646736138634724465661388102913095270441349, 188398091998576775301587150664493928186961248835, 265783407325208761503692730946094334871499974606538059511953937495106877595034597140552253510212962821, 1136981260380993, 1134988328444737, 
    291388300469057, 1464361710667450402647122728000387765892517282627, 1136981260380993, 79449387438528, 290555619971520, 290555619971520, 
    79449387438528, 290555619971520, 290839096202176, 129777061125114688385544090139422961131954691772945946369347430163358179898092070109933362506670469]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 0) (a := 1) (rem' := 105) (cur' := ⟨2, 128, ⟨0, [], 1, []⟩⟩) (prev' := [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b1_0
  · exact tv_b1_1
  · exact tv_b1_2
  · exact tv_b1_3
  · exact tv_b1_4
  · exact tv_b1_5
  · exact tv_b1_6
  · exact tv_b1_7
  · exact tv_b1_8
  · exact tv_b1_9
  · exact tv_b1_10
  · exact tv_b1_11

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem step_proof : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1_H1_R1_H1_R1.H1 := by
  intro M hFirst hSecond hRun _hUsed hForm hMissing hLoop hHalts
  -- Specials require write-1 left; this leaf writes 0 left into state 0.
  have hNeSp0 := mk_good_ne_sp0 M (by simp [hSecond])
  have hNeSp1 := mk_good_ne_sp1 M (by simp [hSecond]) (by simp [hSecond])
  have hG : GoodMachine M := ⟨hRun, hForm, hMissing, hLoop, hHalts, hNeSp0, hNeSp1⟩
  obtain ⟨hm0, hv⟩ := mk_base_hm_hv hFirst
  let m : Move := ⟨0, 0, true⟩
  have hm_cmd : M 1 0 = m.command := hSecond
  have hm1 : Matches M (baseTable.set 1 0 m) := matches_set hm0 hm_cmd
  have h01_base : UsesOnly01 baseTable := by
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro q a m' hget
    fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
    subst hget; exact Or.inr rfl
  have hprev01 : ∀ h ∈ [h1, h0], h.c.state = 0 ∨ h.c.state = 1 := by
    intro h hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl <;> simp [h0, h1, startPos, Position.move]
  have h01_1 : UsesOnly01 (baseTable.set 1 0 m) := usesOnly01_set h01_base (Or.inr rfl) (Or.inl rfl)
  exact tv_b1 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)

end OMA.BB4H2

-- Step BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H1.R1.H1.R1.H1.R1.H1
-- Credit: @pageman (adaptation); certificates from @hyprspacecoyote
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1_H1_R1_H1_R1.H1 :=
  OMA.BB4H2.step_proof
