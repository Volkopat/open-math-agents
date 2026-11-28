import FormalConjectures.OptimizationConstants.«14»

-- Reduction Constant14.c14_lower_bound_improved.R2
-- Credit: @Narden91
-- Credit: @yuka30240 (adapting bounded Tree Normal Form structure from reductions/Constant14.c14_lower_bound.R1.lean to unbounded runs)

/-!
# Reduction `Constant14.c14_lower_bound_improved.R2`

Reduction of `Constant14.c14_lower_bound_improved` (`6 < Constant14.C14`, i.e., `7 ≤ C14`)
to four orthogonal statements, generalizing the bounded Tree Normal Form reduction in
`Constant14.c14_lower_bound.R1` (`#21878`, `@yuka30240`) to **unbounded** non-halting
trajectories (requiring no known step bound `BB(6)`):

* `H1`: `6 ≤ Constant14.C14` (`Constant14.c14_lower_bound`, supplying nonemptiness of the
  defining set and ruling out `n ≤ 5`).
* `H2`: Σ₁-completeness for halting 6-state machines (`M.IsHalting → 𝗭𝗙𝗖 ⊢ halts M`).
* `H3`: ZFC non-halting certification for canonical Tree Normal Form (TNF) 6-state partial
  tables (first move right into state `0` or `1`, non-halting, every defined entry reached
  along the infinite run with non-halting target, and states numbered in order of first visit).
* `H4`: Transport of a ZFC non-halting proof through table extension, state permutation fixing
  state `0`, and optional tape reflection for 6-state machines.

Inside `main`, we prove unconditionally (with zero extra `def`s) unbounded-run first-visit
canonicalization (`order_visits_inf`), infinite-trajectory table trimming (`trim_inf_trace`),
coordinate-change replay under state permutation and tape reflection, and assembly of `6 < C14`.
-/

namespace OMA.R_Constant14_c14_lower_bound_improved_R2

open Turing BusyBeaver FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

/-- The `BB(5)` lower bound supplies nonemptiness of the defining set of `C14` and rules out `n ≤ 5`. -/
def H1 : Prop := 6 ≤ Constant14.C14

/-- Σ₁-completeness for halting 6-state binary Turing machines in `𝗭𝗙𝗖`. -/
def H2 : Prop := ∀ M : Machine (Fin 2) (Fin 6),
  M.IsHalting → Entailment.Provable 𝗭𝗙𝗖 (Constant14.halts M)

/-- Certify canonical Tree Normal Form non-halting 6-state partial tables in `𝗭𝗙𝗖`:
first move is right into state `0` or `1`, every defined entry is reached on the infinite run
with a non-halting target, and states appear in canonical order of first visit. -/
def H3 : Prop := ∀ P : Machine (Fin 2) (Fin 6),
  (∃ q b, (q = 0 ∨ q = 1) ∧ P 0 0 = some (some q, Stmt.write b Dir.right)) →
  ¬ P.IsHalting →
  (∀ q a out, P q a = some out →
    out.1 ≠ none ∧ ∃ j : ℕ, ∃ T : Tape (Fin 2),
      P.multiStep (Machine.init []) j = some ⟨some q, T⟩ ∧ T.head = a) →
  (∀ j : ℕ, ∀ q (T : Tape (Fin 2)),
    P.multiStep (Machine.init []) j = some ⟨some q, T⟩ →
    ∀ r < q, ∃ i < j, ∃ U : Tape (Fin 2),
      P.multiStep (Machine.init []) i = some ⟨some r, U⟩) →
  Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts P)

/-- Transport a `𝗭𝗙𝗖` non-halting proof through table extension, state permutation fixing `0`,
and optional tape reflection for 6-state machines. -/
def H4 : Prop := ∀ (P M : Machine (Fin 2) (Fin 6)) (e : Equiv.Perm (Fin 6)) (mirror : Bool),
  e 0 = 0 →
  (∀ q a out, P q a = some out →
    ((M (e.symm q) a).map fun (next, act) =>
      (next.map e, Stmt.write act.symbol
        (if mirror then (match act.dir with | .left => .right | .right => .left) else act.dir)))
        = some out) →
  Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts P) → Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M)

section Helpers

/-- Sort states by first visit time along an infinite run (sentinel `⊤` for unvisited states). -/
private lemma order_visits_inf {n : ℕ} [NeZero n] (state : ℕ → Option (Fin n))
    (start : state 0 = some 0) :
    ∃ e : Equiv.Perm (Fin n), e 0 = 0 ∧
      ∀ j : ℕ, ∀ q, state j = some q → ∀ r < e q,
        ∃ i < j, state i = some (e.symm r) := by
  classical
  let first (q : Fin n) : WithTop ℕ :=
    if h : ∃ j : ℕ, state j = some q then ↑(Nat.find h) else ⊤
  have first_le {q : Fin n} {j : ℕ} (hq : state j = some q) : first q ≤ ↑j := by
    have h : ∃ i : ℕ, state i = some q := ⟨j, hq⟩
    simp only [first, dif_pos h]
    exact WithTop.coe_le_coe.mpr (Nat.find_min' h hq)
  have at_first {q : Fin n} {m : ℕ} (h : first q = ↑m) : state m = some q := by
    unfold first at h
    split at h
    · rename_i hit
      have hm : Nat.find hit = m := WithTop.coe_eq_coe.mp h
      exact hm ▸ Nat.find_spec hit
    · exact (WithTop.top_ne_coe h).elim
  let e := (Tuple.sort first).symm
  have sorted {r s : Fin n} (h : r ≤ s) : first (e.symm r) ≤ first (e.symm s) :=
    Tuple.monotone_sort first h
  have earlier {j : ℕ} {q : Fin n} (hq : state j = some q) {r : Fin n} (hr : r < e q) :
      ∃ i < j, state i = some (e.symm r) := by
    have hrj : first (e.symm r) ≤ ↑j := by
      have h1 := sorted hr.le
      rw [Equiv.symm_apply_apply] at h1
      exact h1.trans (first_le hq)
    cases hf : first (e.symm r) with
    | top =>
      rw [hf] at hrj
      simp at hrj
    | coe i =>
      have hij : i ≤ j := WithTop.coe_le_coe.mp (hf ▸ hrj)
      have hv : state i = some (e.symm r) := at_first hf
      refine ⟨i, lt_of_le_of_ne hij ?_, hv⟩
      intro eqTime
      rw [eqTime, hq] at hv
      have eqState := congrArg e (Option.some.inj hv)
      exact hr.ne (by simpa using eqState.symm)
  refine ⟨e, ?_, fun _ _ hq _ hr => earlier hq hr⟩
  by_contra hn
  obtain ⟨i, hi, _⟩ := earlier start (Fin.pos_iff_ne_zero.mpr hn)
  omega

/-- Retain precisely the entries queried during the entire infinite run of a non-halting machine. -/
private lemma trim_inf_trace (M : Machine (Fin 2) (Fin 6)) (hnh : ¬ M.IsHalting) :
    ∃ P : Machine (Fin 2) (Fin 6),
      (∀ j : ℕ, P.multiStep (Machine.init []) j = M.multiStep (Machine.init []) j) ∧
      (∀ q a out, P q a = some out → M q a = some out) ∧
      (∀ q a out, P q a = some out →
        out.1 ≠ none ∧ ∃ j : ℕ, ∃ T : Tape (Fin 2),
          P.multiStep (Machine.init []) j = some ⟨some q, T⟩ ∧ T.head = a) ∧
      (∀ q a, (∃ j : ℕ, ∃ T : Tape (Fin 2),
        M.multiStep (Machine.init []) j = some ⟨some q, T⟩ ∧ T.head = a) → P q a = M q a) := by
  classical
  let seen (q : Fin 6) (a : Fin 2) := ∃ j : ℕ, ∃ T : Tape (Fin 2),
    M.multiStep (Machine.init []) j = some ⟨some q, T⟩ ∧ T.head = a
  let P : Machine (Fin 2) (Fin 6) := fun q a => if seen q a then M q a else none
  have replay (j : ℕ) :
      P.multiStep (Machine.init []) j = M.multiStep (Machine.init []) j := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
      cases h : M.multiStep (Machine.init []) j with
      | none => rfl
      | some c =>
        obtain ⟨s, T⟩ := c
        cases s with
        | none => rfl
        | some q =>
          have used : seen q T.head := ⟨j, T, h, rfl⟩
          simp [Machine.step, P, used]
  have definedAt {q a out} (h : P q a = some out) : seen q a ∧ M q a = some out := by
    by_cases used : seen q a
    · exact ⟨used, by simpa [P, used] using h⟩
    · simp [P, used] at h
  refine ⟨P, replay, fun _ _ _ h => (definedAt h).2, ?_,
    fun q a h => if_pos (show seen q a from h)⟩
  intro q a out h
  obtain ⟨⟨j, T, atJ, rfl⟩, entry⟩ := definedAt h
  refine ⟨?_, j, T, (replay j).trans atJ, rfl⟩
  intro terminal
  obtain ⟨s, cmd⟩ := out
  change s = none at terminal
  subst s
  have lastCfg : M.multiStep (Machine.init []) (j + 1) =
      some ⟨none, (T.write cmd.symbol).move cmd.dir⟩ := by
    simp [Machine.multiStep_succ, atJ, Machine.step, entry]
  have haltsAt : M.HaltsAfter (Machine.init []) (j + 1) := by
    unfold Machine.HaltsAfter
    rw [Machine.multiStep_succ, lastCfg]
    rfl
  exact hnh ((Machine.isHalting_iff_exists_haltsAt M).mpr ⟨j + 1, haltsAt⟩)

private lemma first_running_inf (M : Machine (Fin 2) (Fin 6)) (hnh : ¬ M.IsHalting) :
    ∃ q a d, M 0 0 = some (some q, Stmt.write a d) := by
  have alive : ¬ M.HaltsAfter (Machine.init []) 1 :=
    fun h => hnh ((Machine.isHalting_iff_exists_haltsAt M).mpr ⟨1, h⟩)
  obtain ⟨q, T, h⟩ := M.exists_of_not_haltsAfter (Machine.init []) 1 alive
  change (M 0 0).map _ = some (⟨some q, T⟩ : Cfg (Fin 2) (Fin 6)) at h
  cases ht : M 0 0 with
  | none => rw [ht] at h; cases h
  | some entry =>
    obtain ⟨s, a, d⟩ := entry
    rw [ht] at h
    cases s with
    | none => cases h
    | some r => exact ⟨r, a, d, rfl⟩

private lemma certify_nonhalting (M : Machine (Fin 2) (Fin 6))
    (hnh : ¬ M.IsHalting) (cert : H3) (extend : H4) :
    Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M) := by
  classical
  obtain ⟨q₁, a₁, d₁, first⟩ := first_running_inf M hnh
  let state (j : ℕ) := (M.multiStep (Machine.init []) j).bind Cfg.q
  obtain ⟨e, e0, ordered⟩ := order_visits_inf state (by rfl)
  let mirror := match d₁ with | .left => true | .right => false
  let turn (d : Dir) := if mirror then (match d with | .left => Dir.right | .right => Dir.left) else d
  let N : Machine (Fin 2) (Fin 6) := fun q a =>
    (M (e.symm q) a).map fun (s, act) => (s.map e, Stmt.write act.symbol (turn act.dir))
  let image (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
    ⟨c.q.map e, if mirror then ⟨c.tape.head, c.tape.right, c.tape.left⟩ else c.tape⟩
  have step (c : Cfg (Fin 2) (Fin 6)) : N.step (image c) = (M.step c).map image := by
    obtain ⟨s, ⟨a, l, r⟩⟩ := c
    cases s with
    | none => rfl
    | some q =>
      cases d₁ <;>
        simp only [Machine.step, image, mirror, Option.map_some, N, Equiv.symm_apply_apply,
          Bool.false_eq_true, if_false, if_true]
      all_goals
        cases h : M q a with
        | none => rfl
        | some entry =>
          obtain ⟨next, b, d⟩ := entry
          cases d <;> rfl
  have start : image (Machine.init []) = Machine.init [] := by
    cases d₁ <;> simpa [image, Machine.init, Tape.mk₁, Tape.mk₂, Tape.mk'] using e0
  have trace (j : ℕ) : N.multiStep (Machine.init []) j =
      (M.multiStep (Machine.init []) j).map image := by
    induction j with
    | zero => exact congrArg some start.symm
    | succ j ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
      cases h : M.multiStep (Machine.init []) j with
      | none => rfl
      | some c => exact step c
  have hN_nh : ¬ N.IsHalting := by
    intro hN
    obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt N).mp hN
    unfold Machine.HaltsAfter at hk
    rw [trace, Option.map_eq_none_iff] at hk
    exact hnh ((Machine.isHalting_iff_exists_haltsAt M).mpr ⟨k, hk⟩)
  have stateTrace (j : ℕ) :
      (N.multiStep (Machine.init []) j).bind Cfg.q = (state j).map e := by
    rw [trace]
    unfold state
    cases M.multiStep (Machine.init []) j <;> rfl
  have stateRun {j r} (h : state j = some r) :
      ∃ U, N.multiStep (Machine.init []) j = some ⟨some (e r), U⟩ := by
    have hs := stateTrace j
    rw [h] at hs
    cases hc : N.multiStep (Machine.init []) j with
    | none => rw [hc] at hs; cases hs
    | some c =>
      obtain ⟨s, U⟩ := c
      rw [hc] at hs
      exact ⟨U, by simpa using hs⟩
  obtain ⟨P, replay, agrees, used, retain⟩ := trim_inf_trace N hN_nh
  apply extend P M e mirror e0 agrees
  apply cert P
  · have e0' : e.symm 0 = 0 := e.symm_apply_eq.mpr e0.symm
    have hfirst : N 0 0 = some (some (e q₁), Stmt.write a₁ Dir.right) := by
      cases d₁ <;> simp [N, first, e0', turn, mirror]
    have hq1_le : e q₁ = 0 ∨ e q₁ = 1 := by
      by_contra hgt
      push Not at hgt
      have h1lt : (1 : Fin 6) < e q₁ := by omega
      have hstate1 : state 1 = some q₁ := by
        simp [state, Machine.step, Machine.init, Tape.mk₁, Tape.mk₂,
          Tape.mk', Fin.default_eq_zero, first]
      obtain ⟨i, hi, hiState⟩ := ordered 1 q₁ hstate1 1 h1lt
      have hi0 : i = 0 := by omega
      subst hi0
      have h0eq : state 0 = some 0 := rfl
      rw [h0eq] at hiState
      have hsymm : e.symm 1 = 0 := (Option.some.inj hiState).symm
      have : (1 : Fin 6) = 0 := by simpa [e0] using congrArg e hsymm
      exact absurd this (by decide)
    exact ⟨e q₁, a₁, hq1_le, (retain 0 0 ⟨0, Tape.mk₁ [], rfl, rfl⟩).trans hfirst⟩
  · intro hP
    obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt P).mp hP
    unfold Machine.HaltsAfter at hk
    rw [replay] at hk
    exact hN_nh ((Machine.isHalting_iff_exists_haltsAt N).mpr ⟨k, hk⟩)
  · exact used
  · intro j r T atJ s hsr
    have atN := (replay j).symm.trans atJ
    have hs := stateTrace j
    rw [atN] at hs
    have hs' : (state j).map e = some r := hs.symm
    obtain ⟨old, hold, eqOld⟩ := Option.map_eq_some_iff.mp hs'
    subst r
    obtain ⟨i, hi, hiState⟩ := ordered j old hold s hsr
    obtain ⟨V, hiN⟩ := stateRun hiState
    exact ⟨i, hi, V, by simpa using (replay i).trans hiN⟩

end Helpers

theorem main : H1 → H2 → H3 → H4 → type_of% @Constant14.c14_lower_bound_improved := by
  classical
  intro six halts cert extend
  let sizes : Set ℕ := {n | ∃ _ : NeZero n, ∃ M : Machine (Fin 2) (Fin n),
    𝗭𝗙𝗖 ⊬ Constant14.halts M ∧ 𝗭𝗙𝗖 ⊬ ∼Constant14.halts M}
  change 6 ≤ sInf sizes at six
  change 6 < sInf sizes
  have nonempty : sizes.Nonempty := by
    by_contra empty
    rw [Set.not_nonempty_iff_eq_empty.mp empty, Nat.sInf_empty] at six
    omega
  have sixExcluded : 6 ∉ sizes := by
    rintro ⟨_, M, noPos, noNeg⟩
    by_cases h : M.IsHalting
    · exact noPos (halts M h)
    · exact noNeg (certify_nonhalting M h cert extend)
  by_contra small
  have eqSix : sInf sizes = 6 := by omega
  exact sixExcluded (eqSix ▸ Nat.sInf_mem nonempty)

end OMA.R_Constant14_c14_lower_bound_improved_R2
