import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1_H1_R1_H2_R1_H1_R1

/-!
Write-1 a=1 state-0 residual FAR leaf (away from special0): certificates from
@hyprspacecoyote `BusyBeaver.BB_4.R2.H2.R1.H1` (`tv_b3`).
-/
-- Credit: @pageman (adaptation); certificates from @hyprspacecoyote
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

private theorem tv_b3_0 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 0, false⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_1 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 0, true⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_2 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 1, false⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_3 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 1, true⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1162218288844992, 1161368023863744, 1161359433929152, 1161368023863744, 1161368023863744, 1128184898717761, 
    1128184898717761, 1128184898717761, 1134782236919873, 1128184898717761, 1128184898717761, 2923728051605758559929334276757643509464395952962, 
    1134782236919873, 1130521495148737, 1161359433929152, 1128184898717761, 1128184898717761, 1130521495148737, 
    1161567746331072, 2923192831701854956069828851223165909485802828610, 1161368023863744, 1161361581412800, 1161359433929152, 1161363728896448, 
    1152580520776640, 1134988334732224, 28545062749796141052404049172839978084073493314, 371085815683512892761663113785397083557700064066, 1128391264965568, 1134988334732224, 
    1130590288221120, 0, 532475143136476034682091077449233593412869620005009072438221334007730491800481848812872401524132181125, 1461551814188457737164009853868230242900040062786, 531566893848442985190985249522199105822813568075341756756410668758397244700911634967345250972221338757, 1128650902669377, 
    1128653050153025, 1128653050153025, 2923728051645554914121068579668246994825835983682, 960962161246946106553613076086465357131036759660803363331028550136622751973873839949714083699625142260122285134979453199878756407568506525751747395987767421232175962233671343587496824696231790638523008917484602459398108449929247573600068349380187907831645184499554313, 182711399388994469185623956647917522934328005186, 730778694777807788003844806864852698386281861698, 
    1461685619180706335815364995428042193136366195522, 1461507212527919533022076455774187177650054828610, 1128650902669377, 1128653050153025, 1128653050153025, 1128650902669377, 
    1128653050153025, 1128650902669377, 1128653050153025, 1128653050153025, 1128665935054913, 531502947801800442927268112574106554765563024389499914220724115473771179463628086895855583082361949829, 
    532475254015451974217798680216874913809582043784759478467505259314638549496020801393414608256211907717, 1161187628746817, 1128185100044353, 1161363590353088, 105639286212673, 4217239420481885636210232910575905170131155133257385298410841763908885746709091950686474488267423876, 
    1130849995198656, 960962621259340297160237214365777891717823722704926564183036830625967204577774570381472448983296891367838364334089242133432813258495900773360678187203359897699384377212925242438340283139698190255741390354758687864485121268592656535515274456990729511404306441249877513, 1130849995198656, 2923192831697908886674815304790262547989800162114, 79268187015233, 88064280037441, 
    72671117248577, 1161234884202944, 105639084886081, 105639084886081, 1161501172175296, 105707804362817, 
    531566814649450785657874923859239530147417212175932137192867954720507871274989159351168379776087113860, 1161368023863744, 1161361581412800, 1161368023863744, 1161363728896448, 1152580520776640, 
    1143784427754432, 1134988334732224, 105639084886081, 105639084886081, 105639084886081, 1152580520776640, 
    1128391264965568, 1134988334732224, 1130590288221120, 105639084886081, 105639084886081, 30195301736472391287196081120801443646156085058, 
    315683686851694254074744945814974539430333763952391537188801836021867973491092901266803384498698174596, 265871601429285315743838129785401450789746865156878494670530786089685978537051426205107963566764179588, 1461551814188457737164048539642320094001606268738, 24263303513663245531547580060276979485565294402, 315618806244994758245201884414474607739653996945947310482339672651678242581382163279000254584289345668, 23014462463110264477498506763757886104766814018, 
    24307905004060306777830651496822276208577255234, 551485154891272322737425054725652954449109543248202756215848172856478848626210119674864478472139909, 106105088837697, 532215612793549360890572975897818411474821744694817750350284335985236788138267684338715710615235097733, 106105088837697, 106105088837697, 
    106105088837697, 106105088837697, 176478262204609, 188397414118873100197553748895780383986991256386, 106105088837697, 265751470930873414351164612517385363006526932848833352699993503936025169955921796374149913246871863428, 
    243435318459281101955884183820061200465616851474123496610325489776771565493717089432877368014337269893398361380223867357606548872831624865727935408758339651246816572386886, 968021362195185393955541101495028777103712441320427193813939515089859961385475162891900479937982250157392375683657837093797066113693603705474201267525171394414719754481222, 265750967022100742192852272687657642285675031833739272164551234581456532686019287313506943848749348356, 265750967022100712688568472009397377696347321951545877532997366477087553674118314403898112294645282308, 60383859499976435730403761470995364169612090338329641679981479879968377396599368043751888711380204380392985356984737324240556876816235350051317340344719168356700306583110, 966134841668032944412957968563988154325480438945343854099673859027366197817049018833234425556091877858065361851484401504515447359956175597260687796910455834134424558153286, 
    1461551814199091601695146771697434242921244202818, 33218933866359176793896429000030302162540211265592764255553101123654622642221373355633629364103889028, 1461551814199091601695146771697434242921244202818, 1464361710646224212118018748175097492209259320130, 33265503442351452126331306229090706639815515675445730576512081064714911858832635625702179921282416772, 1464361710646224212118018748175097492209259320130, 
    483126158568163769936501183021458442214978864003385233287427045967609357358697082995825063905635277027025539003036140677226989204883607484234060645099444991819360497514566, 7729134014253641377469069931430460801357106564174282698180304698507398390950695855234361168600494459521130675772798662716340151125115898905320411904846327609700017466456134, 1461685619180706335815403681202132044237932401474, 961431374112543373399802241676619621526755095224203917564019382330997668318913802368541227380713093534363923595529660516887058331628859746694685748028881437438963899961549286524892966014367282331035723849744925578071923792388653269399992298138906893897203720246956552, 1461685619180706335815403681202132044237932401474, 483185357100068365494086066509854758621066598132873743333501577308872303428656333094588653105998800873741776117627680836949308397851406203941537768769378434836886587616839, 
    106105088837697, 106105088837697, 106105088837697, 106105088837697, 106105088837697, 176478262204609, 
    106105088837697, 106105088837697, 106105088837697, 106105088837697, 106120121223233, 265750967022100712688568472009397377696835429382489545829193237462636181814634433563259635618368075268, 
    1461551814199091601695146771697434242921244202818, 1464361710646224212118018748175097492209259320130, 1461685619180706274968174870247120772396178543426, 176076617814208, 1161368023863744, 1161361581412800, 
    1161368023863744, 1161363728896448, 2924441675454707698499795520666156446587293848386, 2930150668947790473391536372250951286586970526530, 2929437042379178558083499521559229679564633461570, 105639286212673, 
    105639286212673, 105639286212673, 2925868923147434427647516108460384401302537458498, 2923059026700301817224644131982721152014522341186, 2923728051608375487825928679506210158597963338562, 2923192831681916551344901041487418953331210539842, 
    105639286212673, 105639286212673, 176076617814208, 2928712635670479399483352169346509607392474305346, 565252326492225, 72671117248577, 
    72671117248577, 72671117248577, 97053213352571288021877352899768337779438654274, 283777349781569, 33218933866359176793896429000030302162540211271412168552074016993561849657143123079468080075535499396, 33330384048567549770084055013415606785296572831131718200920138323459738797924972306243578106104725636, 
    736462597050775921082969575171684009976866575170, 72671117248577, 72671117248577, 72671117248577, 72671117248577]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_4 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 0, false⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1128653050220736, 1135263212508096, 1128653050220736, 1135263212508096, 1130383991247040, 1161224003915968, 
    1161224003915968, 1161224003915968, 176473902289088, 3969876362449279587023773784201311402369501389713847401676384797769533677602154454237057162814751608845230593972819504591941710474419655384267326079615695722629895083247268422, 3969876362218935200743158856010803934634109105350022081620174449512728949210889883916176840023130312133685581996091875929538725339482789862424418527173649517922794999480578630, 1161368023732672, 
    176476049772736, 106107236389056, 106107236389056, 176076617814208, 176076617814208, 176076617814208]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_5 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 0, true⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1162218219638976, 1162188362486208, 3957286427485527111805477507569384677388174872222237410024406292647907900443146743993405640663897620220073825072464373454032373082400979230717181442025676032411935522854755910, 1161161867661760, 1130856593101760, 1161234884202944, 
    1128657613640385, 291388038583232, 286989992072128, 2923036725907292758956389560910397270399058457410, 1130521495214273, 80268920754624, 
    12993372403592331447569820076407047088587792363790735895221254607475192483360961638661980320815642249303881098552780318792508246499268354499863948046455487517824257065642233648397056181274535156756564893856318414024869468271382605914745952455080433022767682281056272633665843284915037072392165276646605109014147792982468300268452679753742189378642234704382106507242033437258, 284790968816576, 291388038583232, 291388038583232, 291388038583232, 568464985691072, 
    1128253618262209, 1134850956464321, 92771453962089640475985543543959562145872491330, 1128185037263040, 1130383991247040, 1128185037263040, 
    1130383991247040, 1161361512140992, 3957286482768179819956743135435490142320236426393206203005979382968247650497248826284140458187723898373244746626373010450178397345030322089894618712352107334879571705969211974, 1128651041214656, 1128653050220736, 1135250327605696, 
    5097036280423969610201709399962407920194101339788260799209709442026457053222829840227101965451515868807853500053614401318439558085539394673225519690745432103883396511122500590658546805345835940829058537491604771177320227952665842325201410070567692340831400261178086946523621832517094839287826584650812746102909956397309303374751235380244970563756950070915615882392395383313196619, 2923059026737561721892799147367000187441815490371, 1130849995198656, 1135250327605696, 79336906559681, 106107236389057, 
    1161168314372544, 2923192831687194541275072571900340981922369917762, 97053213341856942701362782524111109305552360258, 300184131605440, 286989992072128, 581659125093312, 
    17127037689224021982697993882382837718703952706, 176007896240321, 284778083520960, 730932012943292308569259329476995080233949352770, 284790968816576, 291388038583232, 
    246514146482369, 176145335193793, 188397414114877470853535339535104718619711394626, 105707804430528, 1161361789227456, 469678024263002803969059354250323281735195029067236688987664472590475199230583221470803247223486634092478792402831130654558931494702556178397237330764484168658154560104375812904345254266868362940875142492084193595269817461386899830446297987075292721577992246988552, 
    7092060380424047868404154416372824444409726272950638568475071432799406037037550152021456712531181827839551431686547651439636744800763451056819411806580810998347610983812266567, 176076617814208, 106107236389056, 28545062745224465645369903110165791312823979843, 317213676540352, 283846069326017, 
    123695392436852379508231302202309582380611299138249354451941716835427149370432261510863739071184262518860493724989703396936371459049139197359354396089814538793296204924924486, 1978643270868171354322361283930174228601284962845105804639348381733724010968143266958989667586136805319989612453004291435201554674975673361423606726905498467825742565330614854]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_6 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 1, false⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1135263212508096, 176076617814208]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_7 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 1, true⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161221994844608, 1128253618262209, 1128253618262209, 1161221994844608, 1161226289811904, 1161226289811904, 
    1161230584779200, 1161234879746496, 1134850895647680, 1128253618262209, 1128253618262209, 1128253618262209, 
    1134850956464321, 1128253825881024, 1134850895647680, 1134850895647680, 1134850895647680, 1128253618262209, 
    1128253618262209, 1128253618262209, 1128253618262209, 1128253618262209, 1134850956464321, 1134850956464321, 
    1161359433929152, 1128322471958721, 1128322471958721, 1130521495214273, 1161368023863744, 1161359433929152, 
    33283751484824631724445051627210082194809946813980746898519477829269031640047025888964423347658088900, 371085815683512892761663113785397083559847547714, 317209381966272, 317213676933568, 317209381966272, 317211529449920, 
    317209381966272, 317213676933568, 1128653050220737, 1128653050220737, 1128653050220737, 1128657613640385, 
    1128657613640385, 1128665935122625, 2923036725907251063541399658703168873825122202434, 1128665935122625, 1130854355179713, 1128653050220737, 
    1135267568309185, 1461507224778084742175861140455673045191562957378, 1461507212527919533022076455774187177647907344962, 317209381966272, 317213676933568, 317209381966272, 
    1461507223427589098458386613583099229212397081410, 1133051230951617, 1161224142328256, 1161230584779200, 1143646988669888, 1130452849136576, 
    176145335193793, 176145335193793, 105707804430529, 317211529449920, 317217971900864, 106107236389057, 
    106120121290945, 106120121290945, 176473900191937, 317213676933568, 246842711480513, 176007898337472, 
    176076617814208, 106107236257984, 123695392436852379508388424951488597190371932243698236059193498588685328018306518443888141631917266983146116073042837963539898866351765217494789343149944693126224803616733254, 123695392436852379508388424951488597190371932452147692587773842471043694693409327193109287156765831685205099948195166082646954971816042516581432055597668750585564564778072134, 317209381966272, 317213676933568, 
    259649206680927326188185176368381884021418068928640242872405190109537197128348708061024725416569029]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_8 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, false⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ true 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1128184898717761, 316730754998593, 149705518747840, 1128253618194497, 1130452775803073, 1128253618194497, 
    1130452775803073, 1128253618194497, 1161256216301760, 28545062744814772085679259178330447438583707458, 736462602484659927286886454528217304575992959810, 563534622888640, 
    581126808933056, 581126808933056, 7183239312607841750766374482127784713146958266082543664089944534876562400055352646690460001251963619416600690578432362887667815075445556022286553899669163281364672134569259590, 188398111017150027669405916961649806552260956738, 563534622888640, 844975584193022572032254998072954565079158789954, 
    565733646144192, 563534622888640, 567932669399744, 1461507234316624839928533501733352279662529680194, 28545062788424218319647242640094975333704405826, 371085815722063085269019155095449815187409867586, 
    567519937302720, 708807600902848, 7759266745884737787867324976944749980514209378719387916340366124477009657047840760964969804889525979180308937459557012811488376509000364282775949980132271366790941127995974, 371085815683523277078352415059357357718932312898, 371085815683513541484604461078992454791341299522, 371085815683523277197194658830753864109248238402, 
    371085815683515488603354051875065435376859501378, 565733646144192, 581126808933056, 567932669399744, 1461551814199091601695378885308951740738200213314, 581126808933056, 
    567932669399744, 183045216212744210328599737795323594158871949890, 1130452710854848, 732183652444147467471916537350491047862898627138, 365376805856876505348543652512910940000300847938, 548422019342044858184672169340773557859549991490, 
    366090429703239869922403946410024917357922636610, 23549676769515329767857079556025016139802243906, 365555209776780933718674877191158893668573664066, 183045911749907399204496550401769052250298151490, 1462220839091172936848157817860184486645629801282, 366090429703239869922403946410024917357922636610, 
    183045911749907399204496550401769052250298151490, 548422019342060435134668895709357402543695622722, 1161226151530688, 105830680692801, 7759266745884737787867324976944749980517070666467077457085701427852851118392282739691609808804726878792129465282199210198567801628606815797690150546984998577259126213046854, 1161432249143744, 
    2923192831719096013134373994256807618075860964162, 176076617945280, 732183652444147467471916537350491047862898627138, 3957286427485527111805477507569384677388244432552460802929910892738581610295799659392145110719306832369226979032977702619102839107473506149601343459173291316945571091251690055, 176076617945280, 730753606269255909307343381566585698401885655618, 
    730756393883673454697433746569728038524365673026, 735038153295344946545654850720057680658388062786, 960962621259340297160237214365777891717823722704926564183036830625967204577774570381472448983296891367838364334089242133432813258495900773360678187203359897699384377212925242438340283139698405936960232166237360261630916807558747101240760436257672778097885193249877513, 365733617785390696851019944090217798610005840450, 1130849925992641, 1130852207761601, 
    1130849925992641, 145720204333760, 1128653050153025, 6707465290378267800188040996305299253104276013836041762246681885221414074130258631026200768032554559002344796950434382194368757363173302624732023885784762686877725576012656367131333017091582937952485570274490407242245783128058865051780508958952263461404729989372662270095591926834682043978127293739138341988210718215821280159899633067198863444335062403851012519530581611739683402, 1135247972639041, 183045214870244774920159312189431438296834191938, 
    368944933271410546523299430241253656209246999362, 1464361718812959479687758868483785126154015413058, 145720204333760, 731110419553561907446953153934130837375913407042, 732180859406479780409008429971713247909418996290, 732180859406479780409008429971713247909418996290, 
    182710702482653691391103801502118927892735865410, 182710702482653691391103801502118927892735865410, 2923192831719176458548337942775563387488159404866, 1464361710646224212118018748175093551557437887298, 23014456840475806813029255431838236901917070146, 163449833525952, 
    581126808933056, 581126808933056, 2923192831719176454111543883894030792306185999170, 1130849925992641, 1130854355245249, 145720204333760, 
    1135263005025089, 1135247972639041, 548065208777344551960654481272888362446866092610, 149705518747840, 149636730065088, 183045216210090936512490604121723426668925686338, 
    548422019339391574247165198911752306503888933442, 158501611770048]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_0 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161155215233216, 1161155215233216, 1161292658446528, 1161292658446528, 1130849925992640, 317209643852097, 
    317209643852097, 317209643852097, 1133048953508032, 317209643852097, 317209643852097, 1161224003915968, 
    1161224003915968, 1161224003915968, 1130849995198656, 1130849995198656, 1130849995198656, 1130849995198656, 
    1130849995198656, 1128170350842560, 316934765945153, 316934765945153, 316934765945153, 531501949882260587742187610640932542974807645288718787159258359276052401589683382162037222221468536196, 
    1130850410435264, 1130850410435264, 2923103628706398111610211875378732297219236467266, 316934765945153]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_1 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_2 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161155215233216, 1130849925992640, 1161224003915968, 1130849995198656, 1130849995198656, 1130849995198656, 
    1130849995198656, 1161155422851520, 1128665935258433, 1161224146784704, 1128170350842560, 1130850410435264, 
    1135317178782656, 316943355879745, 316730754998593, 316730754998593, 1130850410435264, 1135317178782656, 
    316943355879745, 316943355879745]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_3 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1162186007519553, 1161155215233216, 1130849925992640, 1130849925992640, 1135265169413056, 317211791335745, 
    317211791335745, 317211791335745, 1161226151399616, 1130852142682304, 2928723416496430135774501206776895241258467857218, 1130852142682304, 
    1161368023863744, 1161234884202944, 1161368023863744, 6707465088723695756462041669331607964978116025472644350312872008527489413480729830512419988308139866264102676286666761550018666423864731055799429689640502814051701247239290373143927504507708192171950852658069962247565145082869537081160711912673013399816860144408012705988244565038151531621218891125366586274413564454694792398682296176605500909924042870819947976146372816011481162, 5765546543805391563381780853924709238853624682097217448921726523468025461793079394510719890329506207983260271377111842401099837013826329162216149249734838870697934150649561153814630356535787652784276409710848724886353907245471475500900463352808269735804134831032812500655887619441585648113447440476089469258687458514422704349040470191907302233501588958812997946592902300903161196928722514493756837698394298190833531335663452693804644100294543053829839362861708450471532548120642931032330832578185839676411574097595425037773466463660037352315832732027158123062609650693436073081680264634467789622894675813500232006517081906232752004865746168015056575166892979278, 2923371247867926600616147513671789334131671905090, 
    1128655336181952, 28545062747135879611981266552432413488353126211, 3957286482768179819956743135535386095930392185957388735263790078597741482313362023276041525026819706854350726151904883571767552696887348366975288748257375469730979548300795462, 1134784602837952, 1135263489463232, 498163040083692684825852622929707446383026283959372068153189136402887009246095278371583180794839436562966802500504694062888340005545539376625240932180461818802371370638918, 
    300169428214081, 316936913428801, 2923048573263167642360227228210280245861873100611, 960962154094212046835217857624440951243359382280315518482490121323070426323277455699297028984069885226678794144529785608723642152796426120844668831185037509327352773188446086011102625968962983901773993338880499978799650584871690942765673940116450413828374537246988552, 531501997402235843673078834018290835123961472008431187880139878726963244024552043015232619089636900996, 960962154094212046835217857624440951243359382280315518482490121323070426323277455699297059175538939419593693333797690981723307594003155694007602076818512820324125820110646703180740266647387479781198414869470911330768347804102530914224977349563430270301896713246988552, 
    1130865442820800, 1135263489463232, 3957318153739228932148079060346538864749506376802247475269367249545118780987149966454479051656757805495389180426890228976503108632634552257653435241740960192102002137451413063, 1130384406483648, 2923728051608344334045009583118942745961030505282, 1135263489463232, 
    2923728073386415816985071244774917621594196038466, 3957905353407350526976139120631990221013971080350490939812062224469849275693334582203039745551161875459259158922408130754688843673099772880427130004109069471874027487982739015, 316730754998593]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_4 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161294805930176, 1161226151399616, 1161226151399616, 1130852142682304, 1130852142682304, 1130852142682304, 
    1130852142682304, 1161226294268352, 28545062745807143467047121272107683336918405954, 4217239420481885636210136631897281682805133657625230862662893845621218483648979899785746140019048580, 371085815679526491324735453298479054058709586754]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_5 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [317213938819521, 1130852142682304, 960962161246946106553613076086465357131036759660803363331028550136622752105596062168272324174643017485134504712718546396182672776165498904677657589363237544916356401199219525425291049760101678965401314875898914088716951341871252039210347014497361154258519048249554312, 531502947801800442927268112574106554765563024389158977541438140010253705632169459728148631423571714308, 51381112945376274500313517365355780285050941251, 960962154094212046835217857624440951243359382280253876264893850955702859236005891397848311548779795992396783474157869387115280259616121763049322769887715023624252920582967569292670280706590847209466829945088566270357078386980932931709931271994527378070061065246991112, 
    1128170350842560, 5765546543806702476887127026601062026605812030159620377100539157072316557996865869353718756750242612998280499196503965765527403436404618376908544929450028048242747956843974717956178919156422278267492449560675789658796752808977728998210570252406826675328309438627628770529475709694893165380783294185179595984201318444706452921526469961249775982314998367068753299928443052751405426538768353505364613350919292712222075825825184311969840584046626745930359087354271284027881815528895339764729037880184333402173811706678186116750663554698544436553836074427258868073131513038242683710875097976666206804699438802683370971841663816832619515282054027692999150245504758862, 1134980030010304, 1135254899528640, 1135254899528640, 1134980030010304, 
    1134980030010304, 1135254899528640]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_6 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_7 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1128655201964224, 1161226151399616, 188398111022468298584047141096600982326068916803, 1161155422851520, 1130865165996992, 960962621259340297160237214365777891717823722704926564183036830625967204577774570381472448983296891367838364334089242133432813258495900773360678187203359897699384377212925242438340283139698193622445720953353922562986015005398446925428865531440026700331614729249877513, 
    146239410938305, 146239410938305, 146239410938305, 11260833764567861763437557153734853033907794192826732298546929741907961230004605123328973664641727499991108580225857996139622150252236501403308628750457037143179028690838037255152830044769237909524521568103801399025370937031681933697497111081678701265353030614027495393316535528674913698511923276844179637971846830992443288139421725635580111614559986572710677937362441046181061930093172384435988629171565262483725516321192957877266021710090690687593812603047808265729947446372022652367941458013021844290597801002799217984534396022805831732875770163464252495560477726099875259210060161765252856278131778248370604273235402590734085597601242021289111057321571406, 188397414116209299771323610296853618801017631298, 316939060912577, 
    2928712984111648387311812611712244798555905077827]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_8 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161161657946304, 1130856853148352, 1130856385483456, 3957286482768179819956743135435490142318804043455087200613195225556331186938021567337730073743051180760786641548782103839078459737764019706812171476754983316938681111870922311, 183045216210090936512490604121722863718972265026]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_9 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_10 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161161657946304, 1161161657946304, 1130856853148352, 1130856853148352, 1161230446629056, 1161230589235648, 
    1986402478530383591740645431997337819791171788675796430653565237023851118354980214322308842411105945809702174575946134962554092433377358682657474990143708397479193414375305798, 316943355879745, 316943355879745, 583925464646046181219545626144286278998196297855793523923241066406662934343686816847999484091973764, 4217239420481885636210136643637152243686984520854128963665930779374045935371929240087726707370639492, 316943355879745, 
    316943355879745, 25199934811928839270715624678261517534665676610, 1098268501511232091905869633526353011828144001858, 732894483252822335151386912506948860254055600962, 1466502595785871271813270028059675190130773185346, 1130856385483456, 
    1130856385483456, 368944944160415134053722878190673754241141658434, 1464361729701964067257796246574608815254128366402, 548065208777344551960654481272887799501207638594, 548422019339391574247165198911751743558230479426]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_11 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_12 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1128322341998784, 1128322341998784, 1128322409107648, 531501949882260587742187830062401799953215849079026943354492420063986475236549166128290397425645231876, 730778694777745480204437588260200400562725851714, 1130452710723776, 
    1130865027584192, 1139248946615232, 1130383922041024, 1130383922041024, 1130521365254336, 2923103628398100126009056459261574791546791798595, 
    1130383922041024, 1130864958378176, 1130383922041024, 1130383922041024, 1130521365254336, 1130452710723776, 
    1130452710723776, 1130865442820800, 1130865442820800, 2923103628706418556357082578737498593367177597506, 1130452710723776, 1130865027584192, 
    1139248946615232, 1139248946615232, 1139248946615232, 286974751809857, 1134781968814272, 1134850757497024, 
    150635309965633, 732183652444147467471916235119037833070497600066, 732183652444147467471916235119037833070497600066, 12845327246330068286464786420232794390791197250, 12845327246329986523001071699465389776035648066, 94198707078061318990342671869547179995270484802]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_13 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1136981260380993, 1134988328444737, 284791230702401, 291388300469057, 1134781968687937, 1152580514489153, 
    2924798486096674534384251172123657001624626307907, 183045216212744210328599662237171074916295905858, 548422019342044858184672018224469082326498808386, 551485154891272322737669299355073173284666149280410440930095278427231507486311991189088993968963716, 551485154891272322737669299355073173284666149280410440930095278427231507486311991189088993968963716, 23192863565144762642011961595397522946516886339, 
    23192863482566482911253564702969020551874519875, 4184799132117481470136590384804912716631711481930189956367360877061461175575155759908857578235642564, 1427258613643295182688179585388232154623775298]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_14 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1461551814199050063162363173866953964345177937730, 1130383922041024, 1130452710723776, 1130383922041024, 1130864958378176, 1130383922041024, 
    1130452710723776, 1130865165996992, 1130452853593024, 1130865442820800, 1130383922041024, 1130452710723776, 
    1130865027584192, 1139248946615232, 1134781968814272, 1130383922041024, 1130383922041024, 730753606269255909307343079333977310287884194370, 
    730756393883673454697432839871904000086563099202, 1134781968814272, 1134781968814272, 1134850757497024, 1134850900104128, 2923192852775435601243865681795213828755325719362, 
    2923728070660200336199320718810620743812372321090, 735038153295344946545654850720063873131498017346, 183045214870244774920159312189431438296834191938, 732178071813350692782958228063152817355968484162, 732178071802716868816678901079922360873725727554, 1427253147878464493681672394497185267807425090, 
    24263303375345770896986320737513908490903496515, 25690556491338218685467278954852468211901798210, 2865656668356194139858815234164401938578281282, 4184799116527889978398784983509455867973112952273844462953411369790883352524593908054419120161308804, 94198707078082088257004973694325639574131315522, 1427258613664064290894156381638016546396705346]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9_15 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1128391258678081, 1128665935258433, 155048925737921, 291388300469057, 291388300469057, 1134781968687937, 
    146252832715713, 286990253958081, 1130383922176961, 2923103628398058426798542396605370472132140674883, 155048925737921, 291388300469057, 
    1134781968687937, 1134988328444737, 1136981260380993, 155048925737921, 291388300469057, 531502440922007731439362805349204800220111663201299247622464039188945310879928234391177846635449762500, 
    146252832715713, 1130590281933761, 2923192831719134916212085688697190549796929222467, 427727809426369, 1134781968687937, 183045911749907399204496625959632778168916537922, 
    183045911749907399204496625959632778168916537922, 548422019342060435134668971267510484738372563522, 365733617785390696851019944090218361562106745410, 185542907841756436101577024607429705419141944130]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b3_9 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ true 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 104) (cur' := ⟨3, 127, ⟨2, [], 0, [0, 1]⟩⟩) (prev' := [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b3_9_0
  · exact tv_b3_9_1
  · exact tv_b3_9_2
  · exact tv_b3_9_3
  · exact tv_b3_9_4
  · exact tv_b3_9_5
  · exact tv_b3_9_6
  · exact tv_b3_9_7
  · exact tv_b3_9_8
  · exact tv_b3_9_9
  · exact tv_b3_9_10
  · exact tv_b3_9_11
  · exact tv_b3_9_12
  · exact tv_b3_9_13
  · exact tv_b3_9_14
  · exact tv_b3_9_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_0 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨0, 0, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_1 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨0, 0, true⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105639084886081, 176007829131457]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_2 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_3 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨0, 1, true⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_4 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨1, 0, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161226151530688, 105639084886081, 176145268152513, 149705518747840, 149705518747840, 149705518747840]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_5 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨1, 0, true⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [581126808933056]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_6 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨1, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_7 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨1, 1, true⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105707804362817]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_8 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨2, 0, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105624522197057, 1161363728896448, 188397414116205405533708373595759726027698355010, 3957316615270872440218284450964402880176463350301640623975954510969620871668465798660522435042921180529501278331389240189367591667146742056196177173991223282418501148015120966, 1161368023863744, 188397414116292376520944112429962175140002280258, 
    188397414116292376520944112429962175140002280258, 188397414116292376520944112429962175140002280258, 1134988334732224, 12131653030211263320436298952777171890153255490, 731108328850724106237889998034922089232461771586, 11774884663177739230295050772364549372388635202, 
    183045911749922965993481358757799644274104513090, 183045216212744210328599737795323594161019433538, 357510185251877869385279852002119825634636610, 1134988334732224, 2923371238321452602275315853772966510340150932290, 91701014069372659985672593271794370763135398722, 
    183045911749907389043484632389215799589958857282, 183045214851619934961511459397732112177341412162, 183045911749907389043484632389215799589958857282]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_9 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨2, 0, true⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [732183652444147467471916235119036144207752434242]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_10 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨2, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161368023863744, 589699837819074158287220465640199798039190773543901636070630101367690750358739775402030175611111305348, 365376805856876505348543652512911502952401752898, 365421404795155814697691768288430286136345121602, 548422019342044858184672093782909831947374047810, 371085815683523277355960470052001911043786822466, 
    176145268152513, 33218886717633724322929770282846208316896973432055939921869632362847460197118888930266014152742991364, 183045911749907399204496474843905326338122216002, 182711399295870563903854201082160823046401716802, 366090429703239869922403946410025480310023541570, 548087505611964723880507308402094395470668395074, 
    183045911749907399204496474843905326338122216002, 548422019342060435134668820151493676631519687234]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_11 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161226151530688, 316936913428801, 1161226151530688, 1161432249143744, 1161226151530688, 1161226151530688, 
    316943355879745, 316943355879745, 472395693875842482956046913392939744696981894344502252394457110387779621481057921742590850848549781636, 4217239420481885636211459010914495579850478051834331480633611333426374285526127186683842987020271748, 1161226151530688, 371085815683515488603199167106595216787909924675, 
    4217239420481885636211685893556066751628065196321258164476361138277165062869735580239512175978496132, 176076617945280, 7090248878460238971847168764376121580924161159599739832445669322451766280998293458925408810295074962702220768570014119489516125596154773376161653185522624110307880995022404166, 176076617945280, 176076617945280, 1462934471120232750540038280689557734390872773442, 
    1461551814199029293895701467060353401876803295042, 1464361729701974451891127397486994667343838253890, 730845597523764622455270188121439019564347200066, 732183652444147467471916235119036144207752434242, 2930150668947790473391536228513381033966198375235, 2929437042379178558083499377821659426943861310275, 
    2924441675454707698499795376928586193966521697091, 1461551814199050063162363768885131861455664125762, 1464361729701995221157789699311773126922699084610, 1461685619180664797282620678389829662772352324418, 1461507212538511818455611465716899261016768058178, 1464361718812959479687758868483785689106116318018, 
    176076617945280, 176076617945280, 176076617945280, 730753606269255909307343381566585698404033139266, 1461551814199050063162363768885131861455664125762, 1464361729701995221157789699311773126922699084610, 
    1461685619180664797282620678389829662772352324418, 730756393883673454697433746569728038526513156674, 735038153295344946545654850720057680660535546434, 2923059026700301817224643988245150899393750189891, 2925868923147434427647515964722814148681765307203, 2923728051608375487825928535768639905977191187267, 
    2923192831681916551344900897749848700710438393667]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_12 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨3, 0, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [16609689126196325622104005442823024946530596308274601818506553493546011761593282162978424220278950788, 567932669399744, 567932669399744, 737889850177365887167944742268554793740593566530, 581126808933056, 581126808933056, 
    581126808933056, 730753606269255909148887056536904664937169720130, 960962621259340297160237214365777891717823722704926564183036830625967204577774570381472448983296891367838364334089242133432813258495900773360678187203359897699384377212925242438340283139698410144517391555203383019726431675329061162382854593963477062199017993249877513, 365733617785390696851019944090217798612153324098, 732180859406479739844188920434612216575387800386, 732180859406479739844188920434612216575387800386, 
    732180859406479739844188920434612216575387800386, 732180859406461566735859406337931064443884573506]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_13 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨3, 0, true⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [176473833083073, 176473833083073, 176473765974209, 188397414114877627735142496094846674943464182594, 183045214870244774920159312189431438298981675586, 365555209771786573848675774793044587099723929410, 
    365733616413939552675684987465974988855308195650, 366090429698245510329703412811835792366476728130, 366090429698245510329703412811835792366476728130, 366804056266857464934908870578668845786613159746, 368231309404081336115801779265452907725789861698, 513259132768038800474175964706704692261092562407525630748202311746230247119141891044612907742193048287433231501385123929710136643594373121026885464005511627082753788784198, 
    532345381924043839394587245521308376725660196668060491222886909406200259710064848276242323962337706116, 581395120223413659886870286864224289706534368493510796390685804915720311209218530050177253139760300164, 567519937302720, 538318444843818352625747870026928865776155664585269536744159261350800007087387631276628120358193742724, 731470020425680264485449940204603903107611513410, 11441676168658192657512816332381206285819843138, 
    145307472236736, 145307472236736, 145307472236736, 260536679351365601131353048012217414298923408451769360803044306647922988559202114043481681260458820]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_14 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [731110419553561907446952851702675933720767148610, 732180859406479780409008127740258344254272737858, 732180859406479780409008127740258344254272737858]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10_15 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, some ⟨3, 1, true⟩, none, none⟩ true 104 ⟨3, 129, ⟨2, [1], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [106107236321345, 106105088837697, 97053213332632949214742027125497506952405586754, 736462602484660089546163283741581259106104152898, 563534622888640, 581126808933056, 
    581126808933056, 97053213331469874718413267653976985831148098370, 176473833083073, 17127037652003366155131344662127781168166228802, 97053213333881696302229904093361571651471291202, 176473900191937, 
    145720204333760, 286044960592064, 285976171909312, 317209643852097, 538573920120789213425353466224105219252594956484929593476579784052431455608546684046917380427619672196, 317211321573697, 
    317211791335745, 123695392436852379508231302202309582380611299138883968182017294871231182967881494299882077372607881232518396150089644403984529888440624926876026417525603307667037761541452359, 538833442545653603971551570866998823909590292472244879188418925154166886589646466480771229735903838340, 537795352846196041671507583448299033723535104648666075136836646333152692322021630364820225837043564676, 33283751113574826881503524289022424008528992624147109085483142072053836773789625477334668085453615237, 11440630821309779291363373863291032965052633666, 
    91366501614006607126956147614147983362398098242, 4122285245674505847143378038682325532780561649984459292953562054229768522310403176464356902532241792097914428979329971361195017689484872911506692060846704069185264368842930758, 581126808933056, 548065208777344551960654481272888362449013576258, 183045216210090936512490604121723426671073169986, 548422019339391574247165198911752306506036417090, 
    145307472236736, 145307472236736, 145307472236736, 145307472236736]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b3_10 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ true 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨2, [1], 1, []⟩⟩) (prev' := [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b3_10_0
  · exact tv_b3_10_1
  · exact tv_b3_10_2
  · exact tv_b3_10_3
  · exact tv_b3_10_4
  · exact tv_b3_10_5
  · exact tv_b3_10_6
  · exact tv_b3_10_7
  · exact tv_b3_10_8
  · exact tv_b3_10_9
  · exact tv_b3_10_10
  · exact tv_b3_10_11
  · exact tv_b3_10_12
  · exact tv_b3_10_13
  · exact tv_b3_10_14
  · exact tv_b3_10_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_0 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_1 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_2 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161224003915968, 387108089112897, 176473833083072, 176473833083072, 176473902289088]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_3 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [317211791335745, 1161157431922880, 1161226151399616, 1161226151399616, 176476049772736, 176476049772736, 
    176476049772736, 106109455241408, 176476049772736, 176476049772736, 15121341268958217710875072373595407989066104045286341663380634753164010131433675931824323699828682602480388021252343388347481447343383692004792457209737244219556390287473307614333170560465107496906349978451521716638175222273004245172083208759901346070536245997512, 3957316615500260807304154415383440348927267595372264587085710692772190009006833202005339550497400995901920204607463307506685797027284630189518952922225429864765653395661041222, 
    3894729222642533753454633438695733600004827690999301372656108772787500907251409886434889887586380201191854365589197580735557456620136737334365980216858748533079684433489479, 123695392443150858820748899887423351101132307054565268552766093658242440827669435164447072354331205580417522669252454813790871653099234909909757433336287348861039697731778630, 286974751809857, 291372798320961, 286974751809857, 291372798320961, 
    286974751809857, 291372798320961, 581401195107750416007191794568255233073116302102285076771127196732521940463555942674784446413048598597, 291372798320961, 300169428214081, 300169428214081, 
    259649639805701794309992690999734302692173818757712368079334104336847107039161359853902533958144197, 260536679396684181050952589472245220540275783041502437805346388639005094477002472826235519449796805, 387374377085249, 387099499178305, 316936913428801, 188397414134813289413053047802213214345767162690]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_4 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [246844729004224, 1161226151399616, 1161226151399616, 1161226151399616, 176476049772736, 176476049772736, 
    176476049772736, 176476049772736, 176476049772736]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_5 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161294801604800, 106107236323520, 317213938819521, 1161226151399616, 176476049772736, 176476049772736, 
    106107236323520, 980451739385969150888343969809978742182270209167727407721141055242693991245226150522649341588692610866921972032698977051883825423620538371525391140331004168466776067010347357011322395957228509183560776823330244463712333920278928373783299266348637166323630624496988553, 980451739385969150888344019478428648220147385561789404268107228890713197510403322232087939361625284217174574318905441783400686254218711462944154905497953109136825973993571419298528383716670608464411585356681333281449698108986486171771275332941186491704410656496988553, 595676670629787017905321979609534791171029194473468858239729616289250502301020951173880704076082185221, 387101646662081]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_6 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161294801604800, 317218233786689, 1161226151399616, 1161226151399616, 1161226151399616, 176476049772736, 
    176476049772736, 2928712635670481346602101760142582587977992508226, 4217239420481885636211905528504706373480688209436428399965435642922752135354437041699651781677826180, 176476049772736, 176476049772736, 537795352846196041671507583448299033723535104648666075136836646333152710596802257706630088144919478404, 
    535719165589160008864095972014603836760261255336619568614554831432541605829894529516146986239258502277, 123695392436852379508597921950393950270075578820492944895569140678978550854728653870293730418107306841233384385773186286837813280235800887570153469345555756291045078018768454, 387108089112897, 316943355879745, 387108089112897, 316943355879745, 
    4217239420481885636211459010914495579850478051834331480633611333426387709593167330518164797183508612, 4217239420481885636211459010914495579850478051834331480633611333426387709593167330518164797183508612, 4217239420481885636213217603269787319958959480924795854986572478733381898422885272826539808160759940]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_7 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161226151399616, 1161226151399616, 1161226151399616, 106109455241408, 176476049772736, 176476049772736, 
    315644150232281319585688704314262946501856155625855461232454189291733778341090208390390226743559680133, 176476049772736, 176476049772736, 33283751113574826881503524289022424008528992622601518489946768323548366981567576093258237713549848709, 1161368023863744, 966141751781705548019613169737220069598330966578509521367459913286620445093495564617124603374409325802326268440779776899402024049658976481374712665448095140265385450819143, 
    1932386705032721835166147498657400595096127451292464175214118570451404764257704470282644924926731473541168758117052047956738062999286749505273990107990399167857596493527111, 387101646662081, 316939060912577, 4217239420481885636211685893556066751628065196321258164476361138277180968697069481439940090161021060, 4217239420481885636211685893556066751628065196321258164476361138277180968697069481439940090161021060, 581395120223413659886869390394306174360970745381749438953295130813180498077819102404032219069449203845, 
    33283751484824631724446673034145557602850011312660391937804027336362161820511497469990245838091415684]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_8 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161230446366912, 387108089112897, 4217239420481885636211459022654366309422256211303055778504927565358861624338774724532483390993350788, 1161299100897472, 3957286482768179819956743135535386095930392296355129030498711427557556327111262820624217108510860923131694491049815261948198693592731188554005086751172623798169230916332772934, 176480345264320, 
    2923059026705577860035993394102158089196822087491, 183045216210090936512490604121722863716824781378]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_9 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_10 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [28545062755111126011002847825351743752334493507, 3957316615500260807304154415383440348927267595027034717924758774570976823971489438878570443832231515775145962619810172600358564178996374617032710923655175259339015605204463174, 548065208777344551960654481272887799494765187650, 548422019339391574247165198911751743551788028482]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_11 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_12 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105776595275968, 28545062745826614654543029232837489191295128386, 105707804364992, 12845327246329986523001071699463173143682617922, 105776523841728, 176076617814208, 
    176076617814208, 176076617814208, 176488934674624, 51381112982594009657072199027247165031418185539, 176007829131456, 176488865468608, 
    176076617814208, 150635309965633, 176076617814208, 176076617814208, 176076617814208, 176007898337472, 
    176076617814208, 176076617814208, 176488934674624, 316814106431680, 286974751809857, 366804056277179102129321366273149421138810540866, 
    365421404800493516219999968057938807533032478530, 183045911749922965993481358757799644276251996738, 730798207961675627337607791914524469157796267843, 1461551814199029293895701467060356779589408724802, 1464361729701974451891127397486998045056443683650, 1464361729701974451891127397486998045056443683650, 
    730845597523764703584908602725823316606324871746, 730845597523764546396234174425377531015127405122, 730845597523764622455270188121440708427092365890, 732183652444147467471916235119037833070497600066, 732183652444147467471916235119037833070497600066]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_13 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [300184393491265, 581659370218305, 1143578061710145, 1154573446425409, 1145846139990977, 1143784421466945, 
    300184393491265, 300184393491265, 581659370218305, 581659370218305, 1136981260380993, 1134988328444737, 
    1136981260380993, 1136981260380993, 284791230702401, 1128184898921281, 1128185167358785, 1154573446425409, 
    1152580514489153, 1130384190614465, 427727809426369, 183045216212744210328599737795323594158871949890, 548422019342044858184672093782909831947374047810, 2854506295715390453419768753995330170384290626, 
    551485156945714612346274229963188378808147325411661199656862362124108071542390895894757363660667972, 23549675405742972881518136195331957288075322179, 185542907860407166556083409849073839022402442050, 1427258613643295182688179585381476729412915778]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_14 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105776523841728, 105776523841728, 23549676790819323897268334994930058939231983426, 25690556491338218685467278954848034964107171650, 176076617814208, 176488865468608, 
    176076617814208, 176076617814208, 176076617814208, 4217239420481885636211905634163541590107273274736337505861047344877831224551020933453754128264347780, 176076617814208, 176076617814208, 
    176076617814208, 176488934674624, 316814106431680, 183045214870244774920159312189431438296834191938, 97064015254883712830221316268708845465720853314, 97064015256046791763327176539032271825439560514, 
    316814106431680, 176076617814208, 1427253147878464493681672394494933459403805250, 1427258613664064290894156381631261121185845826, 114224765568707201138575675023949865376649598787, 23014456880280111481682556663805046034580652867, 
    730753606258642854528498193892718131531533554498, 730753606269255909307343381566587387258188370498, 1461507223427547559925642296544890076545956254530, 265751027411102706756238584108673700935104377932504382232310647715003511817823568740195403513925681284, 1461551814199050063162363768885135239168269555522, 265856395036478320592505678676601135255137476060407965144773031101668207124754874668396762032126771332, 
    1464361729701995221157789699311776504635304514370, 265872615188032345003444305520771183226437239218958493411093882538055198614076720122253921545340010628, 1461685619180664797282620678389833040484957754178, 730756393883673454697433746569734230997475627586, 735038153295344946545654850720063873131498017346, 1464361710667450402964035382779829613534847779651]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11_15 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1136981260380993, 1136981260380993, 11440326015804412236795739343173366503989867074, 548087505611964723880507459517821847301462716994, 1128185167358785, 1128253953946561, 
    1128391258678081, 1128185167358785, 1154573446425409, 1159040279524289, 1152580514489153, 286990253958081, 
    1130384190614465, 291388300469057, 1136981260380993, 1134988328444737, 291388300469057, 1464361710667450402647122732722772263160671978307, 
    1130384190614465, 1130590281933761, 1136981260380993, 11774838384770655807203397239074217937768313410, 183045911749907399204496625959632778168916537922, 183045911749907399204496625959632778168916537922, 
    11774839745900123490957251092572647664841159234, 548422019342060435134668971267221128462314009154, 365733617785390696851019944090218361562106745410]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b3_11 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, none, none, none, none⟩ true 105 ⟨2, 128, ⟨0, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 104) (cur' := ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩) (prev' := [⟨2, 128, ⟨0, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b3_11_0
  · exact tv_b3_11_1
  · exact tv_b3_11_2
  · exact tv_b3_11_3
  · exact tv_b3_11_4
  · exact tv_b3_11_5
  · exact tv_b3_11_6
  · exact tv_b3_11_7
  · exact tv_b3_11_8
  · exact tv_b3_11_9
  · exact tv_b3_11_10
  · exact tv_b3_11_11
  · exact tv_b3_11_12
  · exact tv_b3_11_13
  · exact tv_b3_11_14
  · exact tv_b3_11_15

private theorem tv_b3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 0) (a := 1) (rem' := 105) (cur' := ⟨2, 128, ⟨0, [], 1, [1]⟩⟩) (prev' := [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b3_0
  · exact tv_b3_1
  · exact tv_b3_2
  · exact tv_b3_3
  · exact tv_b3_4
  · exact tv_b3_5
  · exact tv_b3_6
  · exact tv_b3_7
  · exact tv_b3_8
  · exact tv_b3_9
  · exact tv_b3_10
  · exact tv_b3_11

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem step_proof : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1_H1_R1_H2_R1_H1_R1.H1 := by
  intro M hFirst hSecond hRun _hUsed hForm hMissing hLoop tbl hNe0 hNe0s hHalts
  have hNeSp0 : M ≠ tblOfList [6,3,3,8,15,10,16,1] := hNe0
  have hNeSp0' : reindex23 M ≠ tblOfList [6,3,3,8,15,10,16,1] := by
    intro heq; apply hNe0s
    have hinv := congrArg reindex23 heq
    rw [reindex23_invol] at hinv
    have hswap2 : swap23 2 = 3 := by decide
    rw [hinv]; funext q a; fin_cases q <;> fin_cases a <;>
      simp [reindex23, tblOfList, tbl, swap23_0, swap23_1, hswap2, swap23_3]
  have hNeSp1 := mk_good_ne_sp1 M (by simp [hSecond]) (by simp [hSecond])
  have hG : GoodMachine M := ⟨hRun, hForm, hMissing, hLoop, hHalts, ⟨hNeSp0, hNeSp0'⟩, hNeSp1⟩
  obtain ⟨hm0, hv⟩ := mk_base_hm_hv hFirst
  let m : Move := ⟨0, 1, true⟩
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
  exact tv_b3 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)

end OMA.BB4H2

-- Step BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H1.R1.H1.R1.H2.R1.H1.R1.H1
-- Credit: @pageman (adaptation); certificates from @hyprspacecoyote
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1_H1_R1_H2_R1_H1_R1.H1 :=
  OMA.BB4H2.step_proof
