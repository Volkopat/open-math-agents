import FormalConjectures.OptimizationConstants.«14»
import Mathlib.Tactic

/-!
# Reduction `Constant14.c14_le_20.R1`

Reduction of Scott Aaronson's Conjecture 11 (`Constant14.C14 ≤ 20`, [A2020]) to two
independent statements:

* `H1`: Conservativity of the Axiom of Choice over `𝗭𝗙` for Turing machine non-halting
  (Gödel's constructible universe `L` / Shoenfield absoluteness): if `𝗭𝗙𝗖` proves
  `∼Constant14.halts M`, then `𝗭𝗙` already proves it. This is a known theorem of set theory,
  completely independent of the state bound `20`.
* `H2`: Existence of a non-halting binary Turing machine `M` with at most `20` states whose
  non-halting sentence `∼Constant14.halts M` is unprovable in `𝗭𝗙`.

What `main` itself proves unconditionally (with zero extra top-level definitions):
1. Full soundness of the copied one-sided LK sequent calculus `FFL.FirstOrder.Derivation`
   with respect to Tarski semantics in Mathlib's `ZFSet.{0}`.
2. Full model verification that `ZFSet.{0}` satisfies every axiom of `𝗭𝗙𝗖` (equality axioms,
   Empty, Extensionality, Pairing, Union, Power Set, Infinity, Foundation, Separation schema,
   Replacement schema, and Choice).
3. Full semantic faithfulness of `Constant14.halts M` in `ZFSet.{0}` for every `n` and every
   binary Turing machine `M`: if `¬ M.IsHalting`, then `Constant14.halts M` is false in
   `ZFSet.{0}`, and therefore `𝗭𝗙𝗖 ⊬ Constant14.halts M`.
4. Combining (1)-(3) with `H1` and `H2` yields `Constant14.C14 ≤ 20` via `Nat.sInf_le`.
-/

namespace OMA.R_Constant14_c14_le_20_R1

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver
open scoped Classical

/-- Conservativity of the Axiom of Choice over `𝗭𝗙` for Turing machine non-halting
(Gödel's constructible universe / Shoenfield absoluteness). -/
def H1 : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : Machine (Fin 2) (Fin n)),
    FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M) →
    FFL.Entailment.Provable 𝗭𝗙 (∼Constant14.halts M)

/-- Conjecture 11 of Aaronson [A2020] reduced to `𝗭𝗙` non-halting unprovability:
there exists a non-halting binary Turing machine with at most `20` states whose
non-halting sentence is not provable in `𝗭𝗙`. -/
def H2 : Prop :=
  ∃ (n : ℕ) (_ : NeZero n) (M : Machine (Fin 2) (Fin n)),
    n ≤ 20 ∧ ¬ M.IsHalting ∧ 𝗭𝗙 ⊬ ∼Constant14.halts M

section Helpers

/- ## Part 1: Tarski Semantics in `ZFSet.{0}` and Soundness of `𝗭𝗙𝗖` -/

private lemma exTv : ∃ tv : ∀ {ξ : Type} {n : ℕ}, (Fin n → ZFSet.{0}) → (ξ → ZFSet.{0}) →
      Semiterm ℒₛₑₜ ξ n → ZFSet.{0},
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}) (i : Fin n),
      tv e ε (Semiterm.bvar i) = e i) ∧
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}) (x : ξ),
      tv e ε (Semiterm.fvar x) = ε x) :=
  ⟨fun {_} {_} e ε t => match t with
      | Semiterm.bvar i => e i
      | Semiterm.fvar x => ε x
      | Semiterm.func f _ => (f : Empty).elim,
    fun _ _ _ => rfl, fun _ _ _ => rfl⟩

private lemma exEv : ∃ ev : ∀ {ξ : Type} {n : ℕ}, (Fin n → ZFSet.{0}) → (ξ → ZFSet.{0}) →
      Semiformula ℒₛₑₜ ξ n → Prop,
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}),
      (ev e ε (Semiformula.verum : Semiformula ℒₛₑₜ ξ n) ↔ True)) ∧
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}),
      (ev e ε (Semiformula.falsum : Semiformula ℒₛₑₜ ξ n) ↔ False)) ∧
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
      (v : Fin 2 → Semiterm ℒₛₑₜ ξ n),
      (ev e ε (Semiformula.rel Language.Set.Rel.eq v) ↔
        exTv.choose e ε (v 0) = exTv.choose e ε (v 1))) ∧
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
      (v : Fin 2 → Semiterm ℒₛₑₜ ξ n),
      (ev e ε (Semiformula.rel Language.Set.Rel.mem v) ↔
        exTv.choose e ε (v 0) ∈ exTv.choose e ε (v 1))) ∧
    (∀ {ξ : Type} {n k : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}) (r : (ℒₛₑₜ).Rel k)
      (v : Fin k → Semiterm ℒₛₑₜ ξ n),
      (ev e ε (Semiformula.nrel r v) ↔ ¬ ev e ε (Semiformula.rel r v))) ∧
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
      (φ ψ : Semiformula ℒₛₑₜ ξ n),
      (ev e ε (Semiformula.and φ ψ) ↔ ev e ε φ ∧ ev e ε ψ)) ∧
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
      (φ ψ : Semiformula ℒₛₑₜ ξ n),
      (ev e ε (Semiformula.or φ ψ) ↔ ev e ε φ ∨ ev e ε ψ)) ∧
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
      (φ : Semiformula ℒₛₑₜ ξ (n + 1)),
      (ev e ε (Semiformula.all φ) ↔ ∀ d, ev (Matrix.vecCons d e) ε φ)) ∧
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
      (φ : Semiformula ℒₛₑₜ ξ (n + 1)),
      (ev e ε (Semiformula.exs φ) ↔ ∃ d, ev (Matrix.vecCons d e) ε φ)) :=
  ⟨fun {ξ} {n} e ε φ =>
      @Semiformula.rec ℒₛₑₜ ξ (fun m _ => (Fin m → ZFSet.{0}) → Prop)
        (fun {_} _ => True)
        (fun {_} _ => False)
        (fun {m k} r v e' =>
          @Language.Set.Rel.rec (fun k' _ => (Fin k' → Semiterm ℒₛₑₜ ξ m) → Prop)
            (fun w => exTv.choose e' ε (w 0) = exTv.choose e' ε (w 1))
            (fun w => exTv.choose e' ε (w 0) ∈ exTv.choose e' ε (w 1)) k r v)
        (fun {m k} r v e' =>
          ¬ @Language.Set.Rel.rec (fun k' _ => (Fin k' → Semiterm ℒₛₑₜ ξ m) → Prop)
            (fun w => exTv.choose e' ε (w 0) = exTv.choose e' ε (w 1))
            (fun w => exTv.choose e' ε (w 0) ∈ exTv.choose e' ε (w 1)) k r v)
        (fun {_} _ _ ih1 ih2 e' => ih1 e' ∧ ih2 e')
        (fun {_} _ _ ih1 ih2 e' => ih1 e' ∨ ih2 e')
        (fun {_} _ ih e' => ∀ d, ih (Matrix.vecCons d e'))
        (fun {_} _ ih e' => ∃ d, ih (Matrix.vecCons d e'))
        n φ e,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
    fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
    fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩

private lemma tv_bvar {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}) (i : Fin n) :
    exTv.choose e ε (Semiterm.bvar i : Semiterm ℒₛₑₜ ξ n) = e i := exTv.choose_spec.1 e ε i

private lemma tv_fvar {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}) (x : ξ) :
    exTv.choose e ε (Semiterm.fvar x : Semiterm ℒₛₑₜ ξ n) = ε x := exTv.choose_spec.2 e ε x

private lemma ev_verum_c {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}) :
    exEv.choose e ε (Semiformula.verum : Semiformula ℒₛₑₜ ξ n) ↔ True := exEv.choose_spec.1 e ε

private lemma ev_falsum_c {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}) :
    exEv.choose e ε (Semiformula.falsum : Semiformula ℒₛₑₜ ξ n) ↔ False :=
  exEv.choose_spec.2.1 e ε

private lemma ev_rel_eq_c {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.rel Language.Set.Rel.eq v) ↔
      exTv.choose e ε (v 0) = exTv.choose e ε (v 1) := exEv.choose_spec.2.2.1 e ε v

private lemma ev_rel_mem_c {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.rel Language.Set.Rel.mem v) ↔
      exTv.choose e ε (v 0) ∈ exTv.choose e ε (v 1) := exEv.choose_spec.2.2.2.1 e ε v

private lemma ev_nrel_c {ξ : Type} {n k : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.nrel r v) ↔ ¬ exEv.choose e ε (Semiformula.rel r v) :=
  exEv.choose_spec.2.2.2.2.1 e ε r v

private lemma ev_and_c {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.and φ ψ) ↔ exEv.choose e ε φ ∧ exEv.choose e ε ψ :=
  exEv.choose_spec.2.2.2.2.2.1 e ε φ ψ

private lemma ev_or_c {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.or φ ψ) ↔ exEv.choose e ε φ ∨ exEv.choose e ε ψ :=
  exEv.choose_spec.2.2.2.2.2.2.1 e ε φ ψ

private lemma ev_all_c {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose e ε (Semiformula.all φ) ↔ ∀ d, exEv.choose (Matrix.vecCons d e) ε φ :=
  exEv.choose_spec.2.2.2.2.2.2.2.1 e ε φ

private lemma ev_exs_c {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose e ε (Semiformula.exs φ) ↔ ∃ d, exEv.choose (Matrix.vecCons d e) ε φ :=
  exEv.choose_spec.2.2.2.2.2.2.2.2 e ε φ

private lemma ev_congr {ξ : Type} {n : ℕ} {e e' : Fin n → ZFSet.{0}} {ε ε' : ξ → ZFSet.{0}}
    (φ : Semiformula ℒₛₑₜ ξ n) (h1 : e = e') (h2 : ε = ε') :
    exEv.choose e ε φ ↔ exEv.choose e' ε' φ := by
  subst h1 h2
  exact Iff.rfl

private lemma ev_neg {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (φ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.neg φ) ↔ ¬ exEv.choose e ε φ := by
  induction φ with
  | verum => simp [Semiformula.neg, ev_verum_c, ev_falsum_c]
  | falsum => simp [Semiformula.neg, ev_verum_c, ev_falsum_c]
  | rel r v => simp [Semiformula.neg, ev_nrel_c]
  | nrel r v => simp [Semiformula.neg, ev_nrel_c]
  | and φ ψ ih1 ih2 => simp only [Semiformula.neg, ev_and_c, ev_or_c, ih1, ih2]; tauto
  | or φ ψ ih1 ih2 => simp only [Semiformula.neg, ev_and_c, ev_or_c, ih1, ih2]; tauto
  | all φ ih => simp only [Semiformula.neg, ev_all_c, ev_exs_c, ih]; exact not_forall.symm
  | exs φ ih => simp only [Semiformula.neg, ev_all_c, ev_exs_c, ih]; exact not_exists.symm

private lemma tval_rew {ξ₁ ξ₂ : Type} {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
    (e : Fin n₂ → ZFSet.{0}) (ε : ξ₂ → ZFSet.{0}) (t : Semiterm ℒₛₑₜ ξ₁ n₁) :
    exTv.choose e ε (ω t) = exTv.choose (fun i => exTv.choose e ε (ω (Semiterm.bvar i)))
      (fun x => exTv.choose e ε (ω (Semiterm.fvar x))) t := by
  cases t with
  | bvar i =>
    exact (tv_bvar (fun i => exTv.choose e ε (ω (Semiterm.bvar i)))
      (fun x => exTv.choose e ε (ω (Semiterm.fvar x))) i).symm
  | fvar x =>
    exact (tv_fvar (fun i => exTv.choose e ε (ω (Semiterm.bvar i)))
      (fun x => exTv.choose e ε (ω (Semiterm.fvar x))) x).symm
  | func f _ => exact (f : Empty).elim

private lemma tval_bShift {ξ : Type} {n : ℕ} (d : ZFSet.{0}) (e : Fin n → ZFSet.{0})
    (ε : ξ → ZFSet.{0}) (t : Semiterm ℒₛₑₜ ξ n) :
    exTv.choose (Matrix.vecCons d e) ε (Rew.bShift t) = exTv.choose e ε t := by
  cases t with
  | bvar i =>
    exact (tv_bvar (Matrix.vecCons d e) ε (Fin.succ i)).trans
      ((Matrix.cons_val_succ d e i).trans (tv_bvar e ε i).symm)
  | fvar x => exact (tv_fvar (Matrix.vecCons d e) ε x).trans (tv_fvar e ε x).symm
  | func f _ => exact (f : Empty).elim

private lemma tval_q {ξ₁ ξ₂ : Type} {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
    (d : ZFSet.{0}) (e : Fin n₂ → ZFSet.{0}) (ε : ξ₂ → ZFSet.{0}) :
    (fun i => exTv.choose (Matrix.vecCons d e) ε (ω.q (Semiterm.bvar i))) =
      Matrix.vecCons d (fun i => exTv.choose e ε (ω (Semiterm.bvar i))) ∧
    (fun x => exTv.choose (Matrix.vecCons d e) ε (ω.q (Semiterm.fvar x))) =
      (fun x => exTv.choose e ε (ω (Semiterm.fvar x))) := by
  constructor
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (tv_bvar (Matrix.vecCons d e) ε 0).trans (Matrix.cons_val_zero d e)
    · exact tval_bShift d e ε (ω (Semiterm.bvar j))
  · funext x
    exact tval_bShift d e ε (ω (Semiterm.fvar x))

private lemma ev_rel_congr {ξ₁ ξ₂ : Type} {n₁ n₂ k : ℕ} (r : (ℒₛₑₜ).Rel k)
    (e₁ : Fin n₁ → ZFSet.{0}) (ε₁ : ξ₁ → ZFSet.{0}) (e₂ : Fin n₂ → ZFSet.{0}) (ε₂ : ξ₂ → ZFSet.{0})
    (v₁ : Fin k → Semiterm ℒₛₑₜ ξ₁ n₁) (v₂ : Fin k → Semiterm ℒₛₑₜ ξ₂ n₂)
    (h : ∀ i, exTv.choose e₁ ε₁ (v₁ i) = exTv.choose e₂ ε₂ (v₂ i)) :
    exEv.choose e₁ ε₁ (Semiformula.rel r v₁) ↔ exEv.choose e₂ ε₂ (Semiformula.rel r v₂) := by
  cases r with
  | eq => rw [ev_rel_eq_c, ev_rel_eq_c, h 0, h 1]
  | mem => rw [ev_rel_mem_c, ev_rel_mem_c, h 0, h 1]

private lemma ev_rew {ξ₁ ξ₂ : Type} {n₁ : ℕ} (φ : Semiformula ℒₛₑₜ ξ₁ n₁) :
    ∀ {n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (e : Fin n₂ → ZFSet.{0}) (ε : ξ₂ → ZFSet.{0}),
    exEv.choose e ε (Semiformula.rewAux ω φ) ↔
      exEv.choose (fun i => exTv.choose e ε (ω (Semiterm.bvar i)))
        (fun x => exTv.choose e ε (ω (Semiterm.fvar x))) φ := by
  induction φ with
  | verum =>
    intro n₂ ω e ε
    show exEv.choose e ε Semiformula.verum ↔ _
    rw [ev_verum_c, ev_verum_c]
  | falsum =>
    intro n₂ ω e ε
    show exEv.choose e ε Semiformula.falsum ↔ _
    rw [ev_falsum_c, ev_falsum_c]
  | rel r v =>
    intro n₂ ω e ε
    show exEv.choose e ε (Semiformula.rel r (fun i => ω (v i))) ↔ _
    exact ev_rel_congr r _ _ _ _ _ _ (fun i => tval_rew ω e ε (v i))
  | nrel r v =>
    intro n₂ ω e ε
    show exEv.choose e ε (Semiformula.nrel r (fun i => ω (v i))) ↔ _
    rw [ev_nrel_c, ev_nrel_c]
    exact not_congr (ev_rel_congr r _ _ _ _ _ _ (fun i => tval_rew ω e ε (v i)))
  | and φ ψ ih1 ih2 =>
    intro n₂ ω e ε
    show exEv.choose e ε (Semiformula.and (Semiformula.rewAux ω φ) (Semiformula.rewAux ω ψ)) ↔ _
    rw [ev_and_c, ev_and_c]
    exact and_congr (ih1 ω e ε) (ih2 ω e ε)
  | or φ ψ ih1 ih2 =>
    intro n₂ ω e ε
    show exEv.choose e ε (Semiformula.or (Semiformula.rewAux ω φ) (Semiformula.rewAux ω ψ)) ↔ _
    rw [ev_or_c, ev_or_c]
    exact or_congr (ih1 ω e ε) (ih2 ω e ε)
  | all φ ih =>
    intro n₂ ω e ε
    show exEv.choose e ε (Semiformula.all (Semiformula.rewAux ω.q φ)) ↔ _
    rw [ev_all_c, ev_all_c]
    refine forall_congr' fun d => ?_
    exact (ih ω.q (Matrix.vecCons d e) ε).trans (ev_congr φ (tval_q ω d e ε).1 (tval_q ω d e ε).2)
  | exs φ ih =>
    intro n₂ ω e ε
    show exEv.choose e ε (Semiformula.exs (Semiformula.rewAux ω.q φ)) ↔ _
    rw [ev_exs_c, ev_exs_c]
    refine exists_congr fun d => ?_
    exact (ih ω.q (Matrix.vecCons d e) ε).trans (ev_congr φ (tval_q ω d e ε).1 (tval_q ω d e ε).2)

private lemma mem_atom {α : Type*} {a x : α} : x ∈ Multiset.atom a ↔ x = a := Multiset.mem_singleton

private lemma ev_e0 {ξ : Type} (e e' : Fin 0 → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (φ : Semiformula ℒₛₑₜ ξ 0) :
    exEv.choose e ε φ ↔ exEv.choose e' ε φ := by
  rw [Subsingleton.elim e e']

private lemma ev_shift {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ℕ → ZFSet.{0})
    (φ : Semiproposition ℒₛₑₜ n) :
    exEv.choose e ε (Rewriting.shift φ) ↔ exEv.choose e (fun k => ε (k + 1)) φ := by
  show exEv.choose e ε (Semiformula.rewAux Rew.shift φ) ↔ _
  exact (ev_rew φ Rew.shift e ε).trans
    (ev_congr φ (funext fun i => tv_bvar e ε i) (funext fun x => tv_fvar e ε (x + 1)))

private lemma ev_free (e : Fin 0 → ZFSet.{0}) (ε : ℕ → ZFSet.{0}) (φ : Semiproposition ℒₛₑₜ (0 + 1)) :
    exEv.choose e ε (Rewriting.free φ) ↔
      exEv.choose (Matrix.vecCons (ε 0) e) (fun k => ε (k + 1)) φ := by
  show exEv.choose e ε (Semiformula.rewAux Rew.free φ) ↔ _
  refine (ev_rew φ Rew.free e ε).trans (ev_congr φ ?_ (funext fun x => tv_fvar e ε (x + 1)))
  funext i
  refine Fin.cases ?_ (fun j => Fin.elim0 j) i
  exact tv_fvar e ε 0

private lemma ev_subst_gen {ξ : Type} {n m : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (φ : Semiformula ℒₛₑₜ ξ m) (v : Fin m → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (φ ⇜ v) ↔ exEv.choose (fun i => exTv.choose e ε (v i)) ε φ := by
  show exEv.choose e ε (Semiformula.rewAux (Rew.subst v) φ) ↔ _
  exact (ev_rew φ (Rew.subst v) e ε).trans (ev_congr φ rfl (funext fun x => tv_fvar e ε x))

private lemma ev_subst1 (e : Fin 0 → ZFSet.{0}) (ε : ℕ → ZFSet.{0}) (φ : Semiproposition ℒₛₑₜ (0 + 1))
    (t : Semiterm ℒₛₑₜ ℕ 0) :
    exEv.choose e ε (φ ⇜ ![t]) ↔ exEv.choose (Matrix.vecCons (exTv.choose e ε t) e) ε φ := by
  refine (ev_subst_gen e ε φ ![t]).trans (ev_congr φ ?_ rfl)
  funext i
  refine Fin.cases ?_ (fun j => Fin.elim0 j) i
  rfl

private lemma sound {Γ : Sequent ℒₛₑₜ} (d : Derivation Γ) :
    ∀ ε : ℕ → ZFSet.{0}, ∃ φ ∈ Γ, exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) ε φ := by
  induction d with
  | identity r v =>
    intro ε
    by_cases h : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) ε (Semiformula.rel r v)
    · exact ⟨_, Multiset.mem_add.2 (Or.inl (mem_atom.2 rfl)), h⟩
    · exact ⟨Semiformula.nrel r v, Multiset.mem_add.2 (Or.inr (mem_atom.2 rfl)),
        (ev_nrel_c _ _ r v).2 h⟩
  | cut d1 d2 ih1 ih2 =>
    rename_i Γ φ Δ
    intro ε
    obtain ⟨χ1, h1, e1⟩ := ih1 ε
    obtain ⟨χ2, h2, e2⟩ := ih2 ε
    rcases Multiset.mem_add.1 h1 with h1 | h1
    · exact ⟨χ1, Multiset.mem_add.2 (Or.inl h1), e1⟩
    rcases Multiset.mem_add.1 h2 with h2 | h2
    · exact ⟨χ2, Multiset.mem_add.2 (Or.inr h2), e2⟩
    rw [mem_atom] at h1 h2
    subst h1 h2
    exact absurd e1 ((ev_neg _ _ _).1 e2)
  | contraction d hsub ih =>
    intro ε
    obtain ⟨χ, h, e⟩ := ih ε
    exact ⟨χ, hsub h, e⟩
  | verum =>
    intro ε
    exact ⟨_, mem_atom.2 rfl, (ev_verum_c _ _).2 trivial⟩
  | or d ih =>
    rename_i Γ φ ψ
    intro ε
    obtain ⟨χ, h, e⟩ := ih ε
    rcases Multiset.mem_add.1 h with h | h
    · exact ⟨χ, Multiset.mem_add.2 (Or.inl h), e⟩
    · refine ⟨φ ⋎ ψ, Multiset.mem_add.2 (Or.inr (mem_atom.2 rfl)), ?_⟩
      rcases Multiset.mem_add.1 h with h | h
      · rw [mem_atom] at h; subst h; exact (ev_or_c _ _ _ _).2 (Or.inl e)
      · rw [mem_atom] at h; subst h; exact (ev_or_c _ _ _ _).2 (Or.inr e)
  | and d1 d2 ih1 ih2 =>
    rename_i Γ φ ψ
    intro ε
    obtain ⟨χ1, h1, e1⟩ := ih1 ε
    obtain ⟨χ2, h2, e2⟩ := ih2 ε
    rcases Multiset.mem_add.1 h1 with h1 | h1
    · exact ⟨χ1, Multiset.mem_add.2 (Or.inl h1), e1⟩
    rcases Multiset.mem_add.1 h2 with h2 | h2
    · exact ⟨χ2, Multiset.mem_add.2 (Or.inl h2), e2⟩
    rw [mem_atom] at h1 h2
    subst h1 h2
    exact ⟨_, Multiset.mem_add.2 (Or.inr (mem_atom.2 rfl)), (ev_and_c _ _ _ _).2 ⟨e1, e2⟩⟩
  | all d ih =>
    rename_i Γ φ
    intro ε
    by_cases hΓ : ∃ χ ∈ Γ, exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) ε χ
    · obtain ⟨χ, h, e⟩ := hΓ
      exact ⟨χ, Multiset.mem_add.2 (Or.inl h), e⟩
    refine ⟨∀¹ φ, Multiset.mem_add.2 (Or.inr (mem_atom.2 rfl)), ?_⟩
    refine (ev_all_c _ _ _).2 ?_
    intro x
    let ε' : ℕ → ZFSet.{0} := fun k => Nat.casesOn k x ε
    obtain ⟨χ, h, e⟩ := ih ε'
    rcases Multiset.mem_add.1 h with h | h
    · obtain ⟨ψ, hψ, rfl⟩ := Multiset.mem_map.1 h
      exact absurd ⟨ψ, hψ, (ev_shift _ ε' ψ).1 e⟩ hΓ
    · rw [mem_atom] at h
      subst h
      exact (ev_free _ ε' φ).1 e
  | exs d ih =>
    rename_i Γ φ t
    intro ε
    obtain ⟨χ, h, e⟩ := ih ε
    rcases Multiset.mem_add.1 h with h | h
    · exact ⟨χ, Multiset.mem_add.2 (Or.inl h), e⟩
    · rw [mem_atom] at h
      subst h
      exact ⟨∃¹ φ, Multiset.mem_add.2 (Or.inr (mem_atom.2 rfl)),
        (ev_exs_c _ _ _).2 ⟨exTv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) ε t,
          (ev_subst1 _ ε φ t).1 e⟩⟩

private lemma ev_emb {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ℕ → ZFSet.{0}) (σ : Semisentence ℒₛₑₜ n) :
    exEv.choose e ε (Rewriting.emb σ : Semiproposition ℒₛₑₜ n) ↔
      exEv.choose e (Empty.elim : Empty → ZFSet.{0}) σ := by
  show exEv.choose e ε (Semiformula.rewAux Rew.emb σ) ↔ _
  exact (ev_rew σ Rew.emb e ε).trans
    (ev_congr σ (funext fun i => tv_bvar e ε i) (funext fun x => x.elim))

private lemma sound_theory {T : Theory ℒₛₑₜ} {σ : Sentence ℒₛₑₜ}
    (hT : ∀ ψ ∈ T, exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0}) ψ)
    (h : FFL.Entailment.Provable T σ) :
    exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0}) σ := by
  obtain ⟨pf⟩ := h
  have hv := sound pf.derivation (fun _ => (∅ : ZFSet.{0}))
  obtain ⟨χ, hχ, he⟩ := hv
  obtain ⟨χ0, h0, rfl⟩ := Multiset.mem_map.1 hχ
  rw [ev_emb] at he
  rcases Multiset.mem_add.1 h0 with h0 | h0
  · rw [mem_atom] at h0
    subst h0
    exact (ev_e0 _ _ _ _).1 he
  · obtain ⟨ψ, hψ, rfl⟩ := Multiset.mem_map.1 h0
    have := (ev_neg _ _ ψ).1 he
    exact absurd ((ev_e0 _ _ _ _).1 (hT ψ (pf.axioms_mem ψ hψ))) this

private lemma ev_eq {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (t u : Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.Operator.operator Semiformula.Operator.Eq.eq ![t, u]) ↔
      exTv.choose e ε t = exTv.choose e ε u := by
  show exEv.choose e ε (Semiformula.rel Language.Set.Rel.eq
    (fun i => (Rew.subst ![t, u]) ((Rew.emb : Rew ℒₛₑₜ Empty 2 ξ 2) (Semiterm.bvar i)))) ↔ _
  rw [ev_rel_eq_c]
  exact Iff.rfl

private lemma ev_mem {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (t u : Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.Operator.operator Semiformula.Operator.Mem.mem ![t, u]) ↔
      exTv.choose e ε t ∈ exTv.choose e ε u := by
  show exEv.choose e ε (Semiformula.rel Language.Set.Rel.mem
    (fun i => (Rew.subst ![t, u]) ((Rew.emb : Rew ℒₛₑₜ Empty 2 ξ 2) (Semiterm.bvar i)))) ↔ _
  rw [ev_rel_mem_c]
  exact Iff.rfl

section Simpset
variable {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})

@[local simp] private lemma tval_bvar (i : Fin n) :
    exTv.choose e ε (Semiterm.bvar i : Semiterm ℒₛₑₜ ξ n) = e i := tv_bvar e ε i
@[local simp] private lemma tval_fvar (x : ξ) :
    exTv.choose e ε (Semiterm.fvar x : Semiterm ℒₛₑₜ ξ n) = ε x := tv_fvar e ε x
@[local simp] private lemma ev_and' (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose e ε (φ ⋏ ψ) ↔ exEv.choose e ε φ ∧ exEv.choose e ε ψ := ev_and_c e ε φ ψ
@[local simp] private lemma ev_or' (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose e ε (φ ⋎ ψ) ↔ exEv.choose e ε φ ∨ exEv.choose e ε ψ := ev_or_c e ε φ ψ
@[local simp] private lemma ev_not' (φ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose e ε (∼φ) ↔ ¬ exEv.choose e ε φ := ev_neg e ε φ
@[local simp] private lemma ev_imp' (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose e ε (φ 🡒 ψ) ↔ (exEv.choose e ε φ → exEv.choose e ε ψ) := by
  show exEv.choose e ε (Semiformula.or (Semiformula.neg φ) ψ) ↔ _
  rw [ev_or_c, ev_neg]; tauto
@[local simp] private lemma ev_iff' (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose e ε (φ 🡘 ψ) ↔ (exEv.choose e ε φ ↔ exEv.choose e ε ψ) := by
  show exEv.choose e ε ((φ 🡒 ψ) ⋏ (ψ 🡒 φ)) ↔ _
  rw [ev_and', ev_imp', ev_imp']; tauto
@[local simp] private lemma ev_all' (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose e ε (∀¹ φ) ↔ ∀ d, exEv.choose (Matrix.vecCons d e) ε φ := ev_all_c e ε φ
@[local simp] private lemma ev_exs' (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose e ε (∃¹ φ) ↔ ∃ d, exEv.choose (Matrix.vecCons d e) ε φ := ev_exs_c e ε φ
@[local simp] private lemma ev_top' : exEv.choose e ε (⊤ : Semiformula ℒₛₑₜ ξ n) ↔ True :=
  ev_verum_c e ε
@[local simp] private lemma ev_subst' {m : ℕ} (φ : Semiformula ℒₛₑₜ ξ m)
    (v : Fin m → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (φ ⇜ v) ↔ exEv.choose (fun i => exTv.choose e ε (v i)) ε φ :=
  ev_subst_gen e ε φ v
@[local simp] private lemma ev_eq' (t u : Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.Operator.operator Semiformula.Operator.Eq.eq ![t, u]) ↔
      exTv.choose e ε t = exTv.choose e ε u :=
  ev_eq e ε t u
@[local simp] private lemma ev_mem' (t u : Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.Operator.operator Semiformula.Operator.Mem.mem ![t, u]) ↔
      exTv.choose e ε t ∈ exTv.choose e ε u :=
  ev_mem e ε t u
@[local simp] private lemma ev_ballMem (t : Semiterm ℒₛₑₜ ξ n) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose e ε (Semiformula.ballMem t φ) ↔
      ∀ d ∈ exTv.choose e ε t, exEv.choose (Matrix.vecCons d e) ε φ := by
  show exEv.choose e ε (∀¹ _) ↔ _
  rw [ev_all']
  refine forall_congr' fun d => ?_
  rw [ev_imp', ev_mem']
  simp [tval_bShift]
@[local simp] private lemma ev_bexsMem (t : Semiterm ℒₛₑₜ ξ n) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose e ε (Semiformula.bexsMem t φ) ↔
      ∃ d ∈ exTv.choose e ε t, exEv.choose (Matrix.vecCons d e) ε φ := by
  show exEv.choose e ε (∃¹ _) ↔ _
  rw [ev_exs']
  refine exists_congr fun d => ?_
  show exEv.choose _ ε (Semiformula.and _ _) ↔ _
  rw [ev_and_c, ev_mem']
  simp [tval_bShift]
@[local simp] private lemma ev_rel_eq (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.rel Language.Set.Rel.eq v) ↔
      exTv.choose e ε (v 0) = exTv.choose e ε (v 1) := ev_rel_eq_c e ε v
@[local simp] private lemma ev_rel_mem (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.rel Language.Set.Rel.mem v) ↔
      exTv.choose e ε (v 0) ∈ exTv.choose e ε (v 1) := ev_rel_mem_c e ε v

private lemma sat_empty : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
    Axiom.empty := by
  unfold Axiom.empty; simp
  exact ⟨∅, fun y => ZFSet.notMem_empty y⟩

private lemma sat_ext : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
    Axiom.extentionality := by
  unfold Axiom.extentionality; simp
  intro x y
  exact ⟨fun h => by simp [h], fun h => ZFSet.ext fun z => h z⟩

private lemma sat_pairing : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0})
    (Empty.elim : Empty → ZFSet.{0}) Axiom.pairing := by
  unfold Axiom.pairing; simp
  intro x y
  exact ⟨{y, x}, fun w => by simp [or_comm]⟩

private lemma sat_union : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0})
    (Empty.elim : Empty → ZFSet.{0}) Axiom.union := by
  unfold Axiom.union; simp
  intro x
  exact ⟨ZFSet.sUnion x, fun z => by simp⟩

private lemma sat_power : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0})
    (Empty.elim : Empty → ZFSet.{0}) Axiom.power := by
  unfold Axiom.power; simp [isSubsetOf]
  intro x
  refine ⟨ZFSet.powerset x, fun z => ?_⟩
  rw [ZFSet.mem_powerset]
  exact ⟨fun h w hw => h hw, fun h w hw => h w hw⟩

private lemma sat_infinity : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0})
    (Empty.elim : Empty → ZFSet.{0}) Axiom.infinity := by
  unfold Axiom.infinity; simp [isEmpty, isSucc]
  refine ⟨ZFSet.omega, fun e he => ?_, fun x hx x' hx' => ?_⟩
  · have : e = ∅ := (ZFSet.eq_empty e).2 he
    subst this
    exact ZFSet.omega_zero
  · have : x' = insert x x := ZFSet.ext fun z => by rw [hx' z, ZFSet.mem_insert_iff]
    subst this
    exact ZFSet.omega_succ hx

private lemma sat_foundation : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0})
    (Empty.elim : Empty → ZFSet.{0}) Axiom.foundation := by
  unfold Axiom.foundation; simp [isNonempty]
  intro x y hy
  have hne : x ≠ ∅ := fun h => by rw [h] at hy; exact ZFSet.notMem_empty y hy
  obtain ⟨w, hw, hint⟩ := ZFSet.regularity x hne
  refine ⟨w, hw, fun z hz hzw => ?_⟩
  have : z ∈ x ∩ w := ZFSet.mem_inter.2 ⟨hz, hzw⟩
  rw [hint] at this
  exact ZFSet.notMem_empty z this

private lemma sat_eqAxiom : ∀ φ ∈ 𝗘𝗤 ℒₛₑₜ,
    exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0}) φ := by
  intro φ h
  cases h with
  | refl => unfold Theory.Eq.refl; simp
  | symm => unfold Theory.Eq.symm; simp
  | trans => unfold Theory.Eq.trans; simp
  | funcExt f => exact (f : Empty).elim
  | relExt r =>
    cases r with
    | eq =>
      unfold Theory.Eq.relExt
      simp [allClosure, Matrix.conj, Matrix.vecTail, Fin.addCast, Fin.addNat, Fin.castLE]
    | mem =>
      unfold Theory.Eq.relExt
      simp [allClosure, Matrix.conj, Matrix.vecTail, Fin.addCast, Fin.addNat, Fin.castLE]

private lemma sat_choice : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0})
    (Empty.elim : Empty → ZFSet.{0}) Axiom.choice := by
  unfold Axiom.choice; simp [isNonempty, Semiformula.existsUnique]
  intro 𝓧 hne hdis
  refine ⟨ZFSet.sep (fun x => ∃ X ∈ 𝓧, x = Classical.epsilon (fun y => y ∈ X)) (ZFSet.sUnion 𝓧),
    fun X hX => ?_⟩
  have hchX : Classical.epsilon (fun y => y ∈ X) ∈ X := Classical.epsilon_spec (hne X hX)
  refine ⟨Classical.epsilon (fun y => y ∈ X),
    ⟨ZFSet.mem_sep.2 ⟨ZFSet.mem_sUnion.2 ⟨X, hX, hchX⟩, X, hX, rfl⟩, hchX⟩, ?_⟩
  intro z hzC hzX
  obtain ⟨_, X', hX', rfl⟩ := ZFSet.mem_sep.1 hzC
  have hX'mem : Classical.epsilon (fun y => y ∈ X') ∈ X' := Classical.epsilon_spec (hne X' hX')
  have := hdis X hX X' hX' (Classical.epsilon (fun y => y ∈ X')) hzX hX'mem
  subst this
  rfl

private lemma tval_toEmpty {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ℕ → ZFSet.{0})
    (ε0 : Empty → ZFSet.{0}) (t : Semiterm ℒₛₑₜ ℕ n) (h : t.freeVariables = ∅) :
    exTv.choose e ε0 (t.toEmpty h) = exTv.choose e ε t := by
  cases t with
  | bvar i => exact (tv_bvar e ε0 i).trans (tv_bvar e ε i).symm
  | fvar x => exact absurd h (by simp [Semiterm.freeVariables])
  | func f _ => exact (f : Empty).elim

private lemma ev_toEmpty {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) :
    ∀ (h : φ.freeVariables = ∅) (e : Fin n → ZFSet.{0}) (ε : ℕ → ZFSet.{0})
      (ε0 : Empty → ZFSet.{0}),
    exEv.choose e ε0 (φ.toEmpty h) ↔ exEv.choose e ε φ := by
  induction φ with
  | verum => intro _ e ε ε0; show exEv.choose e ε0 Semiformula.verum ↔ _; rw [ev_verum_c, ev_verum_c]
  | falsum => intro _ e ε ε0; show exEv.choose e ε0 Semiformula.falsum ↔ _; rw [ev_falsum_c, ev_falsum_c]
  | rel r v =>
    intro _ e ε ε0
    show exEv.choose e ε0 (Semiformula.rel r _) ↔ _
    exact ev_rel_congr r _ _ _ _ _ _ (fun i => tval_toEmpty e ε ε0 (v i) _)
  | nrel r v =>
    intro _ e ε ε0
    show exEv.choose e ε0 (Semiformula.nrel r _) ↔ _
    rw [ev_nrel_c, ev_nrel_c]
    exact not_congr (ev_rel_congr r _ _ _ _ _ _ (fun i => tval_toEmpty e ε ε0 (v i) _))
  | and φ ψ ih1 ih2 =>
    intro _ e ε ε0
    show exEv.choose e ε0 (Semiformula.and (φ.toEmpty _) (ψ.toEmpty _)) ↔ _
    rw [ev_and_c, ev_and_c]
    exact and_congr (ih1 _ e ε ε0) (ih2 _ e ε ε0)
  | or φ ψ ih1 ih2 =>
    intro _ e ε ε0
    show exEv.choose e ε0 (Semiformula.or (φ.toEmpty _) (ψ.toEmpty _)) ↔ _
    rw [ev_or_c, ev_or_c]
    exact or_congr (ih1 _ e ε ε0) (ih2 _ e ε ε0)
  | all φ ih =>
    intro h e ε ε0
    show exEv.choose e ε0 (Semiformula.all (φ.toEmpty _)) ↔ _
    rw [ev_all_c, ev_all_c]
    exact forall_congr' fun d => ih h _ ε ε0
  | exs φ ih =>
    intro h e ε ε0
    show exEv.choose e ε0 (Semiformula.exs (φ.toEmpty _)) ↔ _
    rw [ev_exs_c, ev_exs_c]
    exact exists_congr fun d => ih h _ ε ε0

private lemma ev_allClosure : ∀ {m : ℕ} (ψ : Semiformula ℒₛₑₜ ℕ m) (ε : ℕ → ZFSet.{0}),
    (∀ w : Fin m → ZFSet.{0}, exEv.choose w ε ψ) →
      exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) ε (∀¹* ψ)
  | 0, _, _, h => h _
  | m + 1, ψ, ε, h => ev_allClosure (m := m) (∀¹ ψ) ε
      (fun w => (ev_all_c w ε ψ).2 fun d => h (Matrix.vecCons d w))

private lemma fixitr_fvar (n m x : ℕ) :
    Rew.fixitr n m (Semiterm.fvar x : Semiterm ℒₛₑₜ ℕ n) =
      if h : x < m then Semiterm.bvar (Fin.natAdd n ⟨x, h⟩) else Semiterm.fvar (x - m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Rew.fix (Rew.fixitr n m (Semiterm.fvar x)) = _
    rw [ih]
    by_cases hx : x < m
    · have hx' : x < m + 1 := by omega
      simp only [dif_pos hx, dif_pos hx']; rfl
    · by_cases hx' : x < m + 1
      · have he : x = m := by omega
        subst x
        simp only [dif_neg (Nat.lt_irrefl m), dif_pos (Nat.lt_succ_self m), Nat.sub_self]; rfl
      · have he : x - m = x - (m + 1) + 1 := by omega
        simp only [dif_neg hx, dif_neg hx', he]; rfl

private lemma ev_fixitr (m : ℕ) (φ : Semiproposition ℒₛₑₜ 0) (w : Fin (0 + m) → ZFSet.{0})
    (ε : ℕ → ZFSet.{0}) :
    exEv.choose w ε (Rew.fixitr 0 m ▹ φ) ↔
      exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0})
        (fun x => if h : x < m then w ⟨x, by omega⟩ else ε (x - m)) φ := by
  show exEv.choose w ε (Semiformula.rewAux (Rew.fixitr 0 m) φ) ↔ _
  have h1 : (fun x => exTv.choose w ε
      (Rew.fixitr 0 m (Semiterm.fvar x) : Semiterm ℒₛₑₜ ℕ (0 + m))) =
      (fun x => if h : x < m then w ⟨x, by omega⟩ else ε (x - m)) := by
    funext x
    rw [fixitr_fvar]
    by_cases hx : x < m
    · simp only [dif_pos hx, tv_bvar]; congr 1; exact Fin.ext (by simp)
    · simp only [dif_neg hx, tv_fvar]
  exact (ev_rew φ (Rew.fixitr 0 m) w ε).trans (ev_congr φ (Subsingleton.elim _ _) h1)

private lemma sat_univCl (φ : Proposition ℒₛₑₜ)
    (h : ∀ ε : ℕ → ZFSet.{0}, exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) ε φ) :
    exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
      (Semiformula.univCl φ) := by
  unfold Semiformula.univCl
  rw [ev_toEmpty _ _ _ (fun _ => (∅ : ZFSet.{0}))]
  unfold Semiformula.univCl'
  apply ev_allClosure
  intro w
  rw [ev_fixitr]
  exact h _

private lemma sat_sep (φ : SetTheorySemiproposition 1) :
    exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
      (Axiom.separationSchema φ) := by
  unfold Axiom.separationSchema
  apply sat_univCl
  intro ε
  simp
  exact fun x => ⟨_, fun z => ZFSet.mem_sep⟩

private lemma sat_rep (φ : SetTheorySemiproposition 2) :
    exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
      (Axiom.replacementSchema φ) := by
  unfold Axiom.replacementSchema
  apply sat_univCl
  intro ε
  have key : ∀ (a b : ZFSet.{0}) (f : Fin 2 → ZFSet.{0}), f 0 = a → f 1 = b →
      (exEv.choose f ε φ ↔ exEv.choose ![a, b] ε φ) := by
    intro a b f h0 h1
    have : f = ![a, b] := by
      funext i; refine Fin.cases h0 (fun j => ?_) i
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj; exact h1
    rw [this]
  simp only [ev_imp', ev_all', ev_exs', ev_iff', ev_bexsMem, ev_mem', ev_subst', tval_bvar,
    Semiformula.existsUnique, ev_and', ev_eq']
  intro hfun X
  have hfun' : ∀ x, ∃ y, exEv.choose ![x, y] ε φ ∧ ∀ z, exEv.choose ![x, z] ε φ → z = y := by
    intro x
    obtain ⟨y, hy, huniq⟩ := hfun x
    exact ⟨y, (key x y _ (by simp) (by simp)).1 hy,
      fun z hz => huniq z ((key x z _ (by simp) (by simp)).2 hz)⟩
  let F : ZFSet.{0} → ZFSet.{0} := fun x => Classical.choose (hfun' x)
  let _ : ZFSet.Definable₁ F := Classical.allZFSetDefinable _
  refine ⟨ZFSet.image F X, fun y => ?_⟩
  show y ∈ ZFSet.image F X ↔ ∃ d ∈ X, _
  rw [ZFSet.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (key x (F x) _ (by simp) (by simp)).2 (Classical.choose_spec (hfun' x)).1⟩
  · rintro ⟨x, hx, hP⟩
    refine ⟨x, hx, ?_⟩
    exact ((Classical.choose_spec (hfun' x)).2 y ((key x y _ (by simp) (by simp)).1 hP)).symm

private lemma zfsetModel : ∀ ψ ∈ 𝗭𝗙𝗖,
    exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0}) ψ := by
  intro ψ h
  rcases h with h | h
  · cases h with
    | axiom_of_equality _ hφ => exact sat_eqAxiom _ hφ
    | axiom_of_empty_set => exact sat_empty
    | axiom_of_extentionality => exact sat_ext
    | axiom_of_pairing => exact sat_pairing
    | axiom_of_union => exact sat_union
    | axiom_of_power_set => exact sat_power
    | axiom_of_infinity => exact sat_infinity
    | axiom_of_foundation => exact sat_foundation
    | axiom_of_separation φ => exact sat_sep φ
    | axiom_of_replacement φ => exact sat_rep φ
  · have h' : ψ = Axiom.choice := h
    subst h'
    exact sat_choice

/- ## Part 2: Formula-as-Function Combinators on Closed Formulas -/

private lemma ev_e1 (y : ZFSet.{0}) (e : Fin 0 → ZFSet.{0}) (φ : SetTheorySemisentence 1) :
    exEv.choose (y :> e) Empty.elim φ ↔ exEv.choose ![y] Empty.elim φ := by
  rw [Subsingleton.elim e ![]]

private lemma ev_subst1_c {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : SetTheorySemisentence 1)
    (i₀ : Fin m) :
    exEv.choose e Empty.elim (φ ⇜ ![#i₀]) ↔ exEv.choose ![e i₀] Empty.elim φ := by
  rw [ev_subst']
  refine ev_congr φ ?_ rfl
  funext k; fin_cases k; simp

private lemma ev_subst2_c {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : SetTheorySemisentence 2)
    (i₀ i₁ : Fin m) :
    exEv.choose e Empty.elim (φ ⇜ ![#i₀, #i₁]) ↔ exEv.choose ![e i₀, e i₁] Empty.elim φ := by
  rw [ev_subst']
  refine ev_congr φ ?_ rfl
  funext k; fin_cases k <;> simp

private lemma ev_subst3_c {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : SetTheorySemisentence 3)
    (i₀ i₁ i₂ : Fin m) :
    exEv.choose e Empty.elim (φ ⇜ ![#i₀, #i₁, #i₂]) ↔
      exEv.choose ![e i₀, e i₁, e i₂] Empty.elim φ := by
  rw [ev_subst']
  refine ev_congr φ ?_ rfl
  funext k; fin_cases k <;> simp

private lemma et_bvar_succ {m : ℕ} (e : Fin m → ZFSet.{0}) (i : Fin m) :
    ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim (op(=).operator (#0 :> #(i.succ) :> ![])) ↔
      y = e i := by
  intro y; rw [ev_eq']; simp

private lemma et_bvar1 {m : ℕ} (a : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    ∀ y : ZFSet.{0}, exEv.choose (y :> a :> e) Empty.elim (op(=).operator (#0 :> #1 :> ![])) ↔
      y = a := et_bvar_succ (a :> e) 0

private lemma et_bvar2 {m : ℕ} (a b : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    ∀ y : ZFSet.{0}, exEv.choose (y :> a :> b :> e) Empty.elim (op(=).operator (#0 :> #2 :> ![])) ↔
      y = b := et_bvar_succ (a :> b :> e) 1

private lemma et_bvar3 {m : ℕ} (a b c : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    ∀ y : ZFSet.{0},
      exEv.choose (y :> a :> b :> c :> e) Empty.elim (op(=).operator (#0 :> #3 :> ![])) ↔ y = c :=
  et_bvar_succ (a :> b :> c :> e) 2

private lemma et_bvar4 {m : ℕ} (a b c d : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    ∀ y : ZFSet.{0},
      exEv.choose (y :> a :> b :> c :> d :> e) Empty.elim (op(=).operator (#0 :> #4 :> ![])) ↔
        y = d := et_bvar_succ (a :> b :> c :> d :> e) 3

private lemma et_bvar5 {m : ℕ} (a b c d f : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    ∀ y : ZFSet.{0},
      exEv.choose (y :> a :> b :> c :> d :> f :> e) Empty.elim (op(=).operator (#0 :> #5 :> ![])) ↔
        y = f := et_bvar_succ (a :> b :> c :> d :> f :> e) 4

private lemma et_bvar6 {m : ℕ} (a b c d f g : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    ∀ y : ZFSet.{0},
      exEv.choose (y :> a :> b :> c :> d :> f :> g :> e) Empty.elim
        (op(=).operator (#0 :> #6 :> ![])) ↔ y = g :=
  et_bvar_succ (a :> b :> c :> d :> f :> g :> e) 5

private lemma ev_nestFunc0_raw {m : ℕ} (φ : SetTheorySemisentence 1) (y : ZFSet.{0})
    (e : Fin m → ZFSet.{0}) :
    exEv.choose (y :> e) Empty.elim (Semiformula.nestFormulaeFunc φ ![]) ↔
      exEv.choose ![y] Empty.elim φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj]
  rw [ev_imp', ev_top', ev_subst']
  simp only [true_imp_iff]
  refine ev_congr φ ?_ rfl
  funext i; fin_cases i; simp [Fin.addNat]

private lemma et_const0 {m : ℕ} {Ψ : SetTheorySemisentence 1} {c : ZFSet.{0}}
    (hΨ : ∀ y : ZFSet.{0}, exEv.choose ![y] Empty.elim Ψ ↔ y = c) (e : Fin m → ZFSet.{0}) :
    ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim (Semiformula.nestFormulaeFunc Ψ ![]) ↔
      y = c := by
  intro y; rw [ev_nestFunc0_raw]; exact hΨ y

private lemma ev_nestFunc1_raw {m : ℕ} (φ : SetTheorySemisentence 2)
    {e : Fin m → ZFSet.{0}} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : ZFSet.{0}}
    (h₀ : ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim Ψ₀ ↔ y = v₀) (y : ZFSet.{0}) :
    exEv.choose (y :> e) Empty.elim (Semiformula.nestFormulaeFunc φ ![Ψ₀]) ↔
      exEv.choose ![y, v₀] Empty.elim φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj]
  rw [ev_all']
  refine (?_ : _ ↔ ∀ d₀ : ZFSet.{0}, d₀ = v₀ → exEv.choose ![y, d₀] Empty.elim φ).trans
    ⟨fun h => h v₀ rfl, fun h d₀ hd => hd ▸ h⟩
  refine forall_congr' fun d₀ => ?_
  rw [ev_imp', ev_and', ev_top', and_true, ev_subst', ev_subst']
  have he0 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> y :> e) Empty.elim
        ((#((0 : Fin 1).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 1)) k)) =
      (d₀ :> e) := by
    funext k; refine Fin.cases ?_ (fun j => ?_) k
    · simp [Fin.addCast]
    · simp [Fin.addNat]
  have he1 : (fun k : Fin 2 =>
      exTv.choose (d₀ :> y :> e) Empty.elim
        ((#((0 : Fin (m + 1)).addNat 1) :> fun i : Fin 1 => #(i.addCast m.succ)) k)) =
      ![y, d₀] := by
    funext k; fin_cases k <;> simp [Fin.addNat, Fin.addCast]
  rw [he0, he1]
  exact imp_congr (h₀ d₀) Iff.rfl

private lemma et_comp1 {m : ℕ} {φ : SetTheorySemisentence 2} {G : ZFSet.{0} → ZFSet.{0}}
    (hφ : ∀ y x₀, exEv.choose ![y, x₀] Empty.elim φ ↔ y = G x₀)
    {e : Fin m → ZFSet.{0}} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : ZFSet.{0}}
    (h₀ : ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim Ψ₀ ↔ y = v₀) :
    ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim (Semiformula.nestFormulaeFunc φ ![Ψ₀]) ↔
      y = G v₀ := by
  intro y; rw [ev_nestFunc1_raw φ h₀ y, hφ y v₀]

private lemma ev_nestFunc2_raw {m : ℕ} (φ : SetTheorySemisentence 3)
    {e : Fin m → ZFSet.{0}}
    {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : ZFSet.{0}}
    (h₀ : ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim Ψ₀ ↔ y = v₀)
    (h₁ : ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim Ψ₁ ↔ y = v₁) (y : ZFSet.{0}) :
    exEv.choose (y :> e) Empty.elim (Semiformula.nestFormulaeFunc φ ![Ψ₀, Ψ₁]) ↔
      exEv.choose ![y, v₀, v₁] Empty.elim φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj]
  rw [ev_all']
  refine (?_ : _ ↔ ∀ d₁ d₀ : ZFSet.{0}, (d₀ = v₀ ∧ d₁ = v₁) →
      exEv.choose ![y, d₀, d₁] Empty.elim φ).trans
    ⟨fun h => h v₁ v₀ ⟨rfl, rfl⟩, fun h d₁ d₀ ⟨hd0, hd1⟩ => by subst hd0 hd1; exact h⟩
  refine forall_congr' fun d₁ => ?_
  rw [ev_all']
  refine forall_congr' fun d₀ => ?_
  dsimp only [Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  rw [ev_imp', ev_and', ev_and', ev_top', and_true, ev_subst', ev_subst', ev_subst']
  have he_psi0 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((0 : Fin 2).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 2)) k)) =
      (d₀ :> e) := by
    funext k; refine Fin.cases ?_ (fun j => ?_) k
    · simp [Fin.addCast]
    · simp [Fin.addNat]
  have he_psi1 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((1 : Fin 2).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 2)) k)) =
      (d₁ :> e) := by
    have h1 : ((1 : Fin 2).addCast m.succ) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k; refine Fin.cases ?_ (fun j => ?_) k
    · simp [h1]
    · simp [Fin.addNat]
  have he_phi : (fun k : Fin 3 =>
      exTv.choose (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((0 : Fin (m + 1)).addNat 2) :> fun i : Fin 2 => #(i.addCast m.succ)) k)) =
      ![y, d₀, d₁] := by
    have h1 : ((1 : Fin 2).addCast m.succ) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k; fin_cases k
    · simp [Fin.addNat]
    · simp [Fin.addCast]
    · change exTv.choose (d₀ :> d₁ :> y :> e) Empty.elim (#((1 : Fin 2).addCast m.succ)) = d₁
      simp [h1]
  rw [he_psi0, he_psi1, he_phi]
  exact imp_congr (and_congr (h₀ d₀) (h₁ d₁)) Iff.rfl

private lemma et_comp2 {m : ℕ} {φ : SetTheorySemisentence 3}
    {G : ZFSet.{0} → ZFSet.{0} → ZFSet.{0}}
    (hφ : ∀ y x₀ x₁, exEv.choose ![y, x₀, x₁] Empty.elim φ ↔ y = G x₀ x₁)
    {e : Fin m → ZFSet.{0}} {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : ZFSet.{0}}
    (h₀ : ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim Ψ₀ ↔ y = v₀)
    (h₁ : ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim Ψ₁ ↔ y = v₁) :
    ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim (Semiformula.nestFormulaeFunc φ ![Ψ₀, Ψ₁]) ↔
      y = G v₀ v₁ := by
  intro y; rw [ev_nestFunc2_raw φ h₀ h₁ y, hφ y v₀ v₁]

private lemma ev_nest1 {m : ℕ} (φ : SetTheorySemisentence 1)
    {e : Fin m → ZFSet.{0}} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : ZFSet.{0}}
    (h₀ : ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim Ψ₀ ↔ y = v₀) :
    exEv.choose e Empty.elim (Semiformula.nestFormulae φ ![Ψ₀]) ↔
      exEv.choose ![v₀] Empty.elim φ := by
  dsimp only [Semiformula.nestFormulae, FFL.FirstOrder.allItr, Matrix.conj]
  rw [ev_all']
  refine (?_ : _ ↔ ∀ d₀ : ZFSet.{0}, d₀ = v₀ → exEv.choose ![d₀] Empty.elim φ).trans
    ⟨fun h => h v₀ rfl, fun h d₀ hd => hd ▸ h⟩
  refine forall_congr' fun d₀ => ?_
  rw [ev_imp', ev_and', ev_top', and_true, ev_subst', ev_subst']
  have he0 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> e) Empty.elim
        ((#((0 : Fin 1).addCast m) :> fun j : Fin m => #(j.addNat 1)) k)) =
      (d₀ :> e) := by
    funext k; refine Fin.cases ?_ (fun j => ?_) k
    · simp [Fin.addCast]
    · simp [Fin.addNat]
  have he1 : (fun k : Fin 1 =>
      exTv.choose (d₀ :> e) Empty.elim (#(k.addCast m))) = ![d₀] := by
    funext k; fin_cases k; simp [Fin.addCast]
  rw [he0, he1]
  exact imp_congr (h₀ d₀) Iff.rfl

private lemma ev_nest2 {m : ℕ} (φ : SetTheorySemisentence 2)
    {e : Fin m → ZFSet.{0}} {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : ZFSet.{0}}
    (h₀ : ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim Ψ₀ ↔ y = v₀)
    (h₁ : ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim Ψ₁ ↔ y = v₁) :
    exEv.choose e Empty.elim (Semiformula.nestFormulae φ ![Ψ₀, Ψ₁]) ↔
      exEv.choose ![v₀, v₁] Empty.elim φ := by
  dsimp only [Semiformula.nestFormulae, FFL.FirstOrder.allItr, Matrix.conj]
  rw [ev_all']
  refine (?_ : _ ↔ ∀ d₁ d₀ : ZFSet.{0}, (d₀ = v₀ ∧ d₁ = v₁) →
      exEv.choose ![d₀, d₁] Empty.elim φ).trans
    ⟨fun h => h v₁ v₀ ⟨rfl, rfl⟩, fun h d₁ d₀ ⟨hd0, hd1⟩ => by subst hd0 hd1; exact h⟩
  refine forall_congr' fun d₁ => ?_
  rw [ev_all']
  refine forall_congr' fun d₀ => ?_
  dsimp only [Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  rw [ev_imp', ev_and', ev_and', ev_top', and_true, ev_subst', ev_subst', ev_subst']
  have he0 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> d₁ :> e) Empty.elim
        ((#((0 : Fin 2).addCast m) :> fun j : Fin m => #(j.addNat 2)) k)) =
      (d₀ :> e) := by
    funext k; refine Fin.cases ?_ (fun j => ?_) k
    · simp [Fin.addCast]
    · simp [Fin.addNat]
  have he1 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> d₁ :> e) Empty.elim
        ((#((1 : Fin 2).addCast m) :> fun j : Fin m => #(j.addNat 2)) k)) =
      (d₁ :> e) := by
    have h1 : ((1 : Fin 2).addCast m) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k; refine Fin.cases ?_ (fun j => ?_) k
    · simp [h1]
    · simp [Fin.addNat]
  have he_phi : (fun k : Fin 2 =>
      exTv.choose (d₀ :> d₁ :> e) Empty.elim (#(k.addCast m))) = ![d₀, d₁] := by
    have h1 : ((1 : Fin 2).addCast m) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k; fin_cases k
    · simp [Fin.addCast]
    · change exTv.choose (d₀ :> d₁ :> e) Empty.elim (#((1 : Fin 2).addCast m)) = d₁
      simp [h1]
  rw [he0, he1, he_phi]
  exact imp_congr (and_congr (h₀ d₀) (h₁ d₁)) Iff.rfl

private lemma ev_faf_eq {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : ZFSet.{0}}
    (h₁ : ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim T₁ ↔ y = v₁)
    (h₂ : ∀ y : ZFSet.{0}, exEv.choose (y :> v₁ :> e) Empty.elim T₂ ↔ y = v₂) :
    exEv.choose e Empty.elim (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 op(=).operator (#1 :> #0 :> ![])))) ↔
      v₁ = v₂ := by
  rw [ev_all']
  constructor
  · intro h
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_all'] at hv1
    have hv2 := (ev_imp' _ _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rw [ev_eq'] at hv2
    simpa using hv2
  · intro heq d₁
    rw [ev_imp']; intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1; subst rfl1
    rw [ev_all']; intro d₂
    rw [ev_imp']; intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2; subst rfl2
    rw [ev_eq']; simpa using heq

private lemma ev_faf_ne {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : ZFSet.{0}}
    (h₁ : ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim T₁ ↔ y = v₁)
    (h₂ : ∀ y : ZFSet.{0}, exEv.choose (y :> v₁ :> e) Empty.elim T₂ ↔ y = v₂) :
    exEv.choose e Empty.elim (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 ∼op(=).operator (#1 :> #0 :> ![])))) ↔
      v₁ ≠ v₂ := by
  rw [ev_all']
  constructor
  · intro h
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_all'] at hv1
    have hv2 := (ev_imp' _ _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rw [ev_not', ev_eq'] at hv2
    simpa using hv2
  · intro hne d₁
    rw [ev_imp']; intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1; subst rfl1
    rw [ev_all']; intro d₂
    rw [ev_imp']; intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2; subst rfl2
    rw [ev_not', ev_eq']; simpa using hne

private lemma ev_faf_mem {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : ZFSet.{0}}
    (h₁ : ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim T₁ ↔ y = v₁)
    (h₂ : ∀ y : ZFSet.{0}, exEv.choose (y :> v₁ :> e) Empty.elim T₂ ↔ y = v₂) :
    exEv.choose e Empty.elim
        (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 Semiformula.Operator.Mem.mem.operator (#1 :> #0 :> ![])))) ↔
      v₁ ∈ v₂ := by
  rw [ev_all']
  constructor
  · intro h
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_all'] at hv1
    have hv2 := (ev_imp' _ _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rw [ev_mem'] at hv2
    simpa using hv2
  · intro hmem d₁
    rw [ev_imp']; intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1; subst rfl1
    rw [ev_all']; intro d₂
    rw [ev_imp']; intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2; subst rfl2
    rw [ev_mem']; simpa using hmem

private lemma ev_faf_notMem {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : ZFSet.{0}}
    (h₁ : ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim T₁ ↔ y = v₁)
    (h₂ : ∀ y : ZFSet.{0}, exEv.choose (y :> v₁ :> e) Empty.elim T₂ ↔ y = v₂) :
    exEv.choose e Empty.elim
        (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 ∼Semiformula.Operator.Mem.mem.operator (#1 :> #0 :> ![])))) ↔
      v₁ ∉ v₂ := by
  rw [ev_all']
  constructor
  · intro h
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_all'] at hv1
    have hv2 := (ev_imp' _ _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rw [ev_not', ev_mem'] at hv2
    simpa using hv2
  · intro hnm d₁
    rw [ev_imp']; intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1; subst rfl1
    rw [ev_all']; intro d₂
    rw [ev_imp']; intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2; subst rfl2
    rw [ev_not', ev_mem']; simpa using hnm

private lemma ev_faf_ball {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {v₁ : ZFSet.{0}}
    (h₁ : ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim T₁ ↔ y = v₁)
    (φ : SetTheorySemisentence (m + 2)) :
    exEv.choose e Empty.elim (∀¹ (T₁ 🡒 Semiformula.ballMem (#0) φ)) ↔
      ∀ x ∈ v₁, exEv.choose (x :> v₁ :> e) Empty.elim φ := by
  rw [ev_all']
  constructor
  · intro h x hx
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_ballMem, tval_bvar] at hv1
    exact hv1 x hx
  · intro h d₁
    rw [ev_imp']; intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1; subst rfl1
    rw [ev_ballMem, tval_bvar]
    exact h

private lemma ev_faf_bexs {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {v₁ : ZFSet.{0}}
    (h₁ : ∀ y : ZFSet.{0}, exEv.choose (y :> e) Empty.elim T₁ ↔ y = v₁)
    (φ : SetTheorySemisentence (m + 2)) :
    exEv.choose e Empty.elim (∀¹ (T₁ 🡒 Semiformula.bexsMem (#0) φ)) ↔
      ∃ x ∈ v₁, exEv.choose (x :> v₁ :> e) Empty.elim φ := by
  rw [ev_all']
  constructor
  · intro h
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_bexsMem, tval_bvar] at hv1
    exact hv1
  · intro h d₁
    rw [ev_imp']; intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1; subst rfl1
    rw [ev_bexsMem, tval_bvar]
    exact h

private lemma ev_existsUnique {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : SetTheorySemisentence (m + 1)) :
    exEv.choose e Empty.elim (∃¹! φ) ↔ ∃! y, exEv.choose (y :> e) Empty.elim φ := by
  unfold Semiformula.existsUnique ExistsUnique
  rw [ev_exs']
  refine exists_congr fun y => ?_
  rw [ev_and', ev_subst', ev_all']
  have he1 : (fun k : Fin (m + 1) =>
      exTv.choose (y :> e) Empty.elim
        ((#0 :> fun x : Fin m => #(BinderNotation.finSuccItr x 1)) k)) = (y :> e) := by
    funext k; refine Fin.cases ?_ (fun j => ?_) k
    · simp
    · simp [BinderNotation.finSuccItr]
  rw [he1]
  refine and_congr Iff.rfl (forall_congr' fun z => ?_)
  rw [ev_imp', ev_subst', ev_eq']
  have he2 : (fun k : Fin (m + 1) =>
      exTv.choose (z :> y :> e) Empty.elim
        ((#0 :> fun x : Fin m => #(BinderNotation.finSuccItr x 2)) k)) = (z :> e) := by
    funext k; refine Fin.cases ?_ (fun j => ?_) k
    · simp
    · simp [BinderNotation.finSuccItr]
  rw [he2]
  simp

/- ## Part 3: Set-Theoretic Encodings in `ZFSet.{0}` -/

private lemma exVnNat :
    ∃ f : ℕ → ZFSet.{0}, f 0 = ∅ ∧ ∀ k, f (k + 1) = insert (f k) (f k) :=
  ⟨Nat.rec ∅ (fun _ acc => insert acc acc), rfl, fun _ => rfl⟩

@[local simp] private lemma vnNat_zero : exVnNat.choose 0 = ∅ := exVnNat.choose_spec.1
@[local simp] private lemma vnNat_succ (k : ℕ) :
    exVnNat.choose (k + 1) = insert (exVnNat.choose k) (exVnNat.choose k) :=
  exVnNat.choose_spec.2 k

private lemma mem_vnNat_iff {x : ZFSet.{0}} {m : ℕ} :
    x ∈ exVnNat.choose m ↔ ∃ k < m, x = exVnNat.choose k := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [vnNat_succ, ZFSet.mem_insert_iff, ih]
    constructor
    · rintro (rfl | ⟨k, hk, rfl⟩)
      · exact ⟨m, Nat.lt_succ_self m, rfl⟩
      · exact ⟨k, Nat.lt_succ_of_lt hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hlt, rfl⟩

private lemma vnNat_lt_mem {a b : ℕ} (h : a < b) : exVnNat.choose a ∈ exVnNat.choose b :=
  mem_vnNat_iff.mpr ⟨a, h, rfl⟩

private lemma vnNat_injective : Function.Injective exVnNat.choose := by
  intro a b hab
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · have hm : exVnNat.choose a ∈ exVnNat.choose b := vnNat_lt_mem hlt
    rw [← hab] at hm
    exact False.elim (ZFSet.mem_irrefl _ hm)
  · rfl
  · have hm : exVnNat.choose b ∈ exVnNat.choose a := vnNat_lt_mem hgt
    rw [hab] at hm
    exact False.elim (ZFSet.mem_irrefl _ hm)

private lemma mem_vnOmega_iff_inductive (x : ZFSet.{0}) :
    x ∈ ZFSet.range exVnNat.choose ↔
      ∀ I : ZFSet.{0}, (∅ ∈ I ∧ ∀ y ∈ I, insert y y ∈ I) → x ∈ I := by
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨k, rfl⟩ I ⟨h0, hsucc⟩
    induction k with
    | zero => simpa using h0
    | succ k ih => simpa using hsucc (exVnNat.choose k) ih
  · intro h
    apply ZFSet.mem_range.mp
    refine h (ZFSet.range exVnNat.choose) ⟨ZFSet.mem_range.mpr ⟨0, vnNat_zero⟩, ?_⟩
    intro y hy
    obtain ⟨k, rfl⟩ := ZFSet.mem_range.mp hy
    exact ZFSet.mem_range.mpr ⟨k + 1, vnNat_succ k⟩

private lemma ev_isEmpty (x : ZFSet.{0}) :
    exEv.choose ![x] Empty.elim SetTheory.isEmpty ↔ x = ∅ := by
  unfold SetTheory.isEmpty; simp [ZFSet.eq_empty]

private lemma ev_isNonempty (x : ZFSet.{0}) :
    exEv.choose ![x] Empty.elim SetTheory.isNonempty ↔ x.Nonempty := by
  unfold SetTheory.isNonempty
  rw [ev_exs']
  refine exists_congr fun y => ?_
  rw [ev_mem']; simp

private lemma ev_isSubsetOf (x y : ZFSet.{0}) :
    exEv.choose ![x, y] Empty.elim SetTheory.isSubsetOf ↔ x ⊆ y := by
  unfold SetTheory.isSubsetOf; simp [ZFSet.subset_def]

private lemma ev_doubleton (p x y : ZFSet.{0}) :
    exEv.choose ![p, x, y] Empty.elim SetTheory.doubleton.dfn ↔ p = ({x, y} : ZFSet.{0}) := by
  unfold SetTheory.doubleton.dfn
  rw [ev_all']
  refine (?_ : _ ↔ ∀ z : ZFSet.{0}, z ∈ p ↔ z = x ∨ z = y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [ev_iff', ev_mem', ev_or', ev_eq', ev_eq']; simp
  · constructor
    · intro h; ext z; rw [h z, ZFSet.mem_insert_iff, ZFSet.mem_singleton]
    · rintro rfl z; rw [ZFSet.mem_insert_iff, ZFSet.mem_singleton]

private lemma ev_singleton (p x : ZFSet.{0}) :
    exEv.choose ![p, x] Empty.elim SetTheory.singleton.dfn ↔ p = ({x} : ZFSet.{0}) := by
  unfold SetTheory.singleton.dfn
  exact (ev_subst3_c _ _ _ _ _).trans
    ((ev_doubleton p x x).trans (by rw [ZFSet.pair_eq_singleton]))

private lemma ev_sUnion (u x : ZFSet.{0}) :
    exEv.choose ![u, x] Empty.elim SetTheory.sUnion.dfn ↔ u = ZFSet.sUnion x := by
  unfold SetTheory.sUnion.dfn
  rw [ev_all']
  refine (?_ : _ ↔ ∀ z : ZFSet.{0}, z ∈ u ↔ ∃ y ∈ x, z ∈ y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [ev_iff', ev_mem', ev_bexsMem]; simp only [tval_bvar]
    exact iff_congr Iff.rfl (exists_congr fun y => and_congr_right fun _ => by rw [ev_mem']; simp)
  · constructor
    · intro h; ext z; rw [h z, ZFSet.mem_sUnion]
    · rintro rfl z; rw [ZFSet.mem_sUnion]

private lemma ev_union (u x y : ZFSet.{0}) :
    exEv.choose ![u, x, y] Empty.elim SetTheory.union.dfn ↔ u = x ∪ y := by
  unfold SetTheory.union.dfn
  rw [ev_all']
  refine (?_ : _ ↔ ∀ d : ZFSet.{0}, d = ({x, y} : ZFSet.{0}) → u = ZFSet.sUnion d).trans ?_
  · refine forall_congr' fun d => ?_
    rw [ev_imp']
    exact imp_congr
      ((ev_subst3_c _ _ _ _ _).trans (ev_doubleton d x y))
      ((ev_subst2_c _ _ _ _).trans (ev_sUnion u d))
  · rw [← ZFSet.sUnion_pair]
    exact ⟨fun h => h ({x, y} : ZFSet.{0}) rfl, fun h d hd => hd ▸ h⟩

private lemma ev_insert (u x y : ZFSet.{0}) :
    exEv.choose ![u, x, y] Empty.elim SetTheory.insert.dfn ↔ u = insert x y := by
  unfold SetTheory.insert.dfn
  rw [ev_all']
  refine (?_ : _ ↔ ∀ s : ZFSet.{0}, s = ({x} : ZFSet.{0}) → u = s ∪ y).trans ?_
  · refine forall_congr' fun s => ?_
    rw [ev_imp']
    exact imp_congr
      ((ev_subst2_c _ _ _ _).trans (ev_singleton s x))
      ((ev_subst3_c _ _ _ _ _).trans (ev_union u s y))
  · rw [ZFSet.insert_eq]
    exact ⟨fun h => h ({x} : ZFSet.{0}) rfl, fun h s hs => hs ▸ h⟩

private lemma ev_sInter (u x : ZFSet.{0}) :
    exEv.choose ![u, x] Empty.elim SetTheory.sInter.dfn ↔ u = ZFSet.sInter x := by
  unfold SetTheory.sInter.dfn
  rw [ev_all']
  refine (?_ : _ ↔ ∀ z : ZFSet.{0}, z ∈ u ↔ x.Nonempty ∧ ∀ y ∈ x, z ∈ y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [ev_iff', ev_mem', ev_and', ev_ballMem]; simp only [tval_bvar]
    refine iff_congr Iff.rfl (and_congr ((ev_subst1_c _ _ _).trans (ev_isNonempty x)) ?_)
    exact forall₂_congr fun y _ => by rw [ev_mem']; simp
  · rcases ZFSet.eq_empty_or_nonempty x with rfl | hne
    · simp only [ZFSet.not_nonempty_empty, false_and, iff_false, ZFSet.sInter_empty, ZFSet.eq_empty]
    · constructor
      · intro h; ext z; rw [h z, ZFSet.mem_sInter hne]; exact ⟨And.right, fun hall => ⟨hne, hall⟩⟩
      · rintro rfl z; rw [ZFSet.mem_sInter hne]; exact ⟨fun hall => ⟨hne, hall⟩, And.right⟩

private lemma ev_kpair (k x y : ZFSet.{0}) :
    exEv.choose ![k, x, y] Empty.elim SetTheory.kpair.dfn ↔ k = ZFSet.pair x y := by
  unfold SetTheory.kpair.dfn
  rw [ev_all']
  refine (?_ : _ ↔ ∀ x' : ZFSet.{0}, x' = ({x} : ZFSet.{0}) →
      ∀ z : ZFSet.{0}, z = ({x, y} : ZFSet.{0}) → k = ({x', z} : ZFSet.{0})).trans ?_
  · refine forall_congr' fun x' => ?_
    rw [ev_imp', ev_all']
    refine imp_congr ((ev_subst2_c _ _ _ _).trans (ev_singleton x' x)) (forall_congr' fun z => ?_)
    rw [ev_imp']
    exact imp_congr
      ((ev_subst3_c _ _ _ _ _).trans (ev_doubleton z x y))
      ((ev_subst3_c _ _ _ _ _).trans (ev_doubleton k x' z))
  · unfold ZFSet.pair
    exact ⟨fun h => h ({x} : ZFSet.{0}) rfl ({x, y} : ZFSet.{0}) rfl,
      fun h x' hx' z hz => by subst hx' hz; exact h⟩

private lemma exPi :
    ∃ p : (ZFSet.{0} → ZFSet.{0}) × (ZFSet.{0} → ZFSet.{0}),
      (∀ w, p.1 w = ZFSet.sUnion (ZFSet.sInter w)) ∧
      (∀ w, p.2 w = ZFSet.sUnion
        ((ZFSet.sUnion w).sep (fun z => z ∈ ZFSet.sInter w → ZFSet.sUnion w = ZFSet.sInter w))) :=
  ⟨⟨fun w => ZFSet.sUnion (ZFSet.sInter w),
    fun w => ZFSet.sUnion
      ((ZFSet.sUnion w).sep (fun z => z ∈ ZFSet.sInter w → ZFSet.sUnion w = ZFSet.sInter w))⟩,
   fun _ => rfl, fun _ => rfl⟩

private lemma sInter_kpair (a b : ZFSet.{0}) :
    ZFSet.sInter (ZFSet.pair a b) = ({a} : ZFSet.{0}) := by
  have hne : (ZFSet.pair a b).Nonempty := ⟨({a} : ZFSet.{0}), by simp [ZFSet.pair]⟩
  ext z
  rw [ZFSet.mem_sInter hne, ZFSet.mem_singleton]
  constructor
  · intro h; exact ZFSet.mem_singleton.mp (h ({a} : ZFSet.{0}) (by simp [ZFSet.pair]))
  · intro hza y hy
    subst hza
    have hy' : y = ({z} : ZFSet.{0}) ∨ y = ({z, b} : ZFSet.{0}) := by simpa [ZFSet.pair] using hy
    rcases hy' with rfl | rfl <;> simp

private lemma sUnion_kpair (a b : ZFSet.{0}) :
    ZFSet.sUnion (ZFSet.pair a b) = ({a, b} : ZFSet.{0}) := by
  ext z
  simp only [ZFSet.pair, ZFSet.mem_sUnion, ZFSet.mem_insert_iff, ZFSet.mem_singleton]
  constructor
  · rintro ⟨w, (rfl | rfl), hz⟩
    · exact Or.inl (ZFSet.mem_singleton.mp hz)
    · simpa [ZFSet.mem_insert_iff, ZFSet.mem_singleton] using hz
  · rintro (hza | hzb)
    · subst hza; exact ⟨({z} : ZFSet.{0}), Or.inl rfl, ZFSet.mem_singleton.mpr rfl⟩
    · subst hzb; exact ⟨({a, z} : ZFSet.{0}), Or.inr rfl, by simp⟩

private lemma pi1Val_pair (a b : ZFSet.{0}) : exPi.choose.1 (ZFSet.pair a b) = a := by
  rw [exPi.choose_spec.1, sInter_kpair, ZFSet.sUnion_singleton]

private lemma pi2Val_pair (a b : ZFSet.{0}) : exPi.choose.2 (ZFSet.pair a b) = b := by
  rw [exPi.choose_spec.2, sUnion_kpair, sInter_kpair]
  by_cases hab : a = b
  · subst hab
    have hsep : ({a, a} : ZFSet.{0}).sep
        (fun z => z ∈ ({a} : ZFSet.{0}) → ({a, a} : ZFSet.{0}) = ({a} : ZFSet.{0})) =
        ({a} : ZFSet.{0}) := by
      ext z; simp [ZFSet.pair_eq_singleton]
    rw [hsep, ZFSet.sUnion_singleton]
  · have hne_ui : ({a, b} : ZFSet.{0}) ≠ ({a} : ZFSet.{0}) := by
      intro heq
      have hb : b ∈ ({a} : ZFSet.{0}) := heq ▸ (by simp : b ∈ ({a, b} : ZFSet.{0}))
      exact hab (ZFSet.mem_singleton.mp hb).symm
    have hsep : ({a, b} : ZFSet.{0}).sep
        (fun z => z ∈ ({a} : ZFSet.{0}) → ({a, b} : ZFSet.{0}) = ({a} : ZFSet.{0})) =
        ({b} : ZFSet.{0}) := by
      ext z
      simp only [ZFSet.mem_sep, ZFSet.mem_insert_iff, ZFSet.mem_singleton, hne_ui, imp_false]
      exact ⟨fun ⟨h1, h2⟩ => h1.resolve_left h2,
        fun hz => ⟨Or.inr hz, fun hza => hab (hza.symm.trans hz)⟩⟩
    rw [hsep, ZFSet.sUnion_singleton]

private lemma ev_pi1 (p w : ZFSet.{0}) :
    exEv.choose ![p, w] Empty.elim SetTheory.kpair.π₁.dfn ↔ p = exPi.choose.1 w := by
  unfold SetTheory.kpair.π₁.dfn
  rw [exPi.choose_spec.1, ev_all']
  refine (?_ : _ ↔ ∀ i : ZFSet.{0}, i = ZFSet.sInter w → p = ZFSet.sUnion i).trans
    ⟨fun h => h (ZFSet.sInter w) rfl, fun h i hi => hi ▸ h⟩
  refine forall_congr' fun i => ?_
  rw [ev_imp']
  exact imp_congr
    ((ev_subst2_c _ _ _ _).trans (ev_sInter i w))
    ((ev_subst2_c _ _ _ _).trans (ev_sUnion p i))

private lemma ev_pi2 (p w : ZFSet.{0}) :
    exEv.choose ![p, w] Empty.elim SetTheory.kpair.π₂.dfn ↔ p = exPi.choose.2 w := by
  unfold SetTheory.kpair.π₂.dfn
  rw [exPi.choose_spec.2, ev_all']
  let u0 := ZFSet.sUnion w
  let i0 := ZFSet.sInter w
  let s0 := u0.sep (fun z => z ∈ i0 → u0 = i0)
  refine (?_ : _ ↔ ∀ u : ZFSet.{0}, u = u0 → ∀ i : ZFSet.{0}, i = i0 →
      ∀ s : ZFSet.{0}, (∀ z : ZFSet.{0}, z ∈ s ↔ z ∈ u ∧ (z ∈ i → u = i)) →
        p = ZFSet.sUnion s).trans ?_
  · refine forall_congr' fun u => ?_
    rw [ev_imp', ev_all']
    refine imp_congr ((ev_subst2_c _ _ _ _).trans (ev_sUnion u w)) (forall_congr' fun i => ?_)
    rw [ev_imp', ev_all']
    refine imp_congr ((ev_subst2_c _ _ _ _).trans (ev_sInter i w)) (forall_congr' fun s => ?_)
    rw [ev_imp', ev_all']
    refine imp_congr (forall_congr' fun z => ?_) ((ev_subst2_c _ _ _ _).trans (ev_sUnion p s))
    rw [ev_iff', ev_mem', ev_and', ev_mem', ev_imp', ev_mem', ev_eq']; simp
  · constructor
    · intro h; exact h u0 rfl i0 rfl s0 (fun z => ZFSet.mem_sep)
    · intro hp u hu i hi s hs
      subst hu hi
      have hseq : s = s0 := by ext z; rw [hs z, ZFSet.mem_sep]
      rw [hseq, hp]

private lemma ev_prod (p X Y : ZFSet.{0}) :
    exEv.choose ![p, X, Y] Empty.elim SetTheory.prod.dfn ↔ p = ZFSet.prod X Y := by
  unfold SetTheory.prod.dfn
  rw [ev_all']
  refine (?_ : _ ↔ ∀ z : ZFSet.{0}, z ∈ p ↔ ∃ x ∈ X, ∃ y ∈ Y, z = ZFSet.pair x y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [ev_iff', ev_mem', ev_bexsMem]; simp only [tval_bvar]
    refine iff_congr Iff.rfl (exists_congr fun x => and_congr_right fun _ => ?_)
    rw [ev_bexsMem]; simp only [tval_bvar]
    refine exists_congr fun y => and_congr_right fun _ => ?_
    exact (ev_subst3_c _ _ _ _ _).trans (ev_kpair z x y)
  · simp_rw [← ZFSet.mem_prod]
    exact ⟨fun h => ZFSet.ext h, fun h z => by rw [h]⟩

private lemma ev_succ (y x : ZFSet.{0}) :
    exEv.choose ![y, x] Empty.elim SetTheory.succ.dfn ↔ y = insert x x := by
  unfold SetTheory.succ.dfn SetTheory.isSucc
  rw [ev_all']
  refine (?_ : _ ↔ ∀ z : ZFSet.{0}, z ∈ y ↔ z = x ∨ z ∈ x).trans ?_
  · refine forall_congr' fun z => ?_
    rw [ev_iff', ev_mem', ev_or', ev_eq', ev_mem']; simp
  · constructor
    · intro h; ext z; rw [h z, ZFSet.mem_insert_iff]
    · rintro rfl z; rw [ZFSet.mem_insert_iff]

private lemma ev_IsInductive (I : ZFSet.{0}) :
    exEv.choose ![I] Empty.elim SetTheory.IsInductive.dfn ↔ (∅ ∈ I ∧ ∀ y ∈ I, insert y y ∈ I) := by
  unfold SetTheory.IsInductive.dfn
  rw [ev_and', ev_all', ev_ballMem]; simp only [tval_bvar]
  refine and_congr ?_ ?_
  · refine (?_ : _ ↔ ∀ e : ZFSet.{0}, e = ∅ → e ∈ I).trans
      ⟨fun h => h ∅ rfl, fun h e he => he.symm ▸ h⟩
    refine forall_congr' fun e => ?_
    rw [ev_imp', ev_mem']; simp only [tval_bvar]
    exact imp_congr ((ev_subst1_c _ _ _).trans (ev_isEmpty e)) Iff.rfl
  · refine forall₂_congr fun y _ => ?_
    rw [ev_all']
    refine (?_ : _ ↔ ∀ y' : ZFSet.{0}, y' = insert y y → y' ∈ I).trans
      ⟨fun h => h (insert y y) rfl, fun h y' hy' => hy'.symm ▸ h⟩
    refine forall_congr' fun y' => ?_
    rw [ev_imp', ev_mem']; simp only [tval_bvar]
    exact imp_congr ((ev_subst2_c _ _ _ _).trans (ev_succ y' y)) Iff.rfl

private lemma dc_isω :
    ∀ w : ZFSet.{0}, exEv.choose ![w] Empty.elim SetTheory.isω ↔ w = ZFSet.range exVnNat.choose := by
  intro w
  unfold SetTheory.isω
  rw [ev_all']
  refine (?_ : _ ↔ ∀ x : ZFSet.{0},
      x ∈ w ↔ ∀ I : ZFSet.{0}, (∅ ∈ I ∧ ∀ y ∈ I, insert y y ∈ I) → x ∈ I).trans ?_
  · refine forall_congr' fun x => ?_
    rw [ev_iff', ev_mem', ev_all']; simp only [tval_bvar]
    refine iff_congr Iff.rfl (forall_congr' fun I => ?_)
    rw [ev_imp', ev_mem']; simp only [tval_bvar]
    exact imp_congr ((ev_subst1_c _ _ _).trans (ev_IsInductive I)) Iff.rfl
  · simp_rw [← mem_vnOmega_iff_inductive]
    exact ⟨fun h => ZFSet.ext h, fun h x => by rw [h]⟩

private lemma exApp :
    ∃ r : (ZFSet.{0} → ZFSet.{0}) × (ZFSet.{0} → ZFSet.{0} → ZFSet.{0}),
      (∀ R, r.1 R = (ZFSet.sUnion (ZFSet.sUnion R)).sep (fun y => ∃ x, ZFSet.pair x y ∈ R)) ∧
      (∀ f x, r.2 f x = (ZFSet.sUnion (r.1 f)).sep (fun z => ∃ y, z ∈ y ∧ ZFSet.pair x y ∈ f)) :=
  ⟨⟨fun R => (ZFSet.sUnion (ZFSet.sUnion R)).sep (fun y => ∃ x, ZFSet.pair x y ∈ R),
    fun f x => (ZFSet.sUnion ((ZFSet.sUnion (ZFSet.sUnion f)).sep
      (fun y => ∃ u, ZFSet.pair u y ∈ f))).sep (fun z => ∃ y, z ∈ y ∧ ZFSet.pair x y ∈ f)⟩,
   fun _ => rfl, fun _ _ => rfl⟩

private lemma mem_relRange {R y : ZFSet.{0}} :
    y ∈ exApp.choose.1 R ↔ ∃ x, ZFSet.pair x y ∈ R := by
  rw [exApp.choose_spec.1, ZFSet.mem_sep]
  refine ⟨And.right, fun ⟨x, hx⟩ => ⟨?_, x, hx⟩⟩
  rw [ZFSet.mem_sUnion]
  refine ⟨({x, y} : ZFSet.{0}), ?_, by simp⟩
  rw [ZFSet.mem_sUnion]
  exact ⟨ZFSet.pair x y, hx, by simp [ZFSet.pair]⟩

private lemma ev_range (r R : ZFSet.{0}) :
    exEv.choose ![r, R] Empty.elim SetTheory.range.dfn ↔ r = exApp.choose.1 R := by
  unfold SetTheory.range.dfn
  change exEv.choose ![r, R] Empty.elim (∀¹ _) ↔ _
  rw [ev_all']
  refine (?_ : _ ↔ ∀ y : ZFSet.{0}, y ∈ r ↔ ∃ x, ZFSet.pair x y ∈ R).trans ?_
  · refine forall_congr' fun y => ?_
    rw [ev_iff']
    refine iff_congr (ev_faf_mem (et_bvar1 y _) (et_bvar3 _ y r _)) ?_
    rw [ev_exs']
    refine exists_congr fun x => ?_
    exact ev_faf_mem
      (et_comp2 ev_kpair (et_bvar1 x _) (et_bvar2 x y _))
      (et_bvar5 _ x y r R _)
  · refine (forall_congr' fun y => iff_congr Iff.rfl mem_relRange.symm).trans
      ⟨fun h => ZFSet.ext h, fun h y => by rw [h]⟩

private lemma ev_function (F Y X : ZFSet.{0}) :
    exEv.choose ![F, Y, X] Empty.elim SetTheory.function.dfn ↔ F = ZFSet.funs X Y := by
  unfold SetTheory.function.dfn
  change exEv.choose ![F, Y, X] Empty.elim (∀¹ _) ↔ _
  rw [ev_all']
  refine (?_ : _ ↔ ∀ f : ZFSet.{0}, f ∈ F ↔ f ∈ ZFSet.funs X Y).trans
    ⟨fun h => ZFSet.ext h, fun h f => by rw [h]⟩
  refine forall_congr' fun f => ?_
  rw [ev_iff']
  refine iff_congr (ev_faf_mem (et_bvar1 f _) (et_bvar3 _ f F _)) ?_
  rw [ev_and', ZFSet.mem_funs, ZFSet.IsFunc]
  refine and_congr ?_ ?_
  · rw [ev_nest2 SetTheory.isSubsetOf (et_bvar1 f _)
      (et_comp2 ev_prod (et_bvar4 f F Y X _) (et_bvar3 f F Y _)), ev_isSubsetOf]
  · rw [ev_faf_ball (et_bvar4 f F Y X _)]
    refine forall₂_congr fun x _ => ?_
    rw [ev_existsUnique]
    refine existsUnique_congr fun y => ?_
    exact ev_faf_mem
      (et_comp2 ev_kpair (et_bvar2 y x _) (et_bvar1 y _))
      (et_bvar5 _ y x _ f _)

private lemma ev_IsFunction (f : ZFSet.{0}) :
    exEv.choose ![f] Empty.elim SetTheory.IsFunction.dfn ↔ ∃ X Y : ZFSet.{0}, f ∈ ZFSet.funs X Y := by
  unfold SetTheory.IsFunction.dfn
  change exEv.choose ![f] Empty.elim (∃¹ ∃¹ _) ↔ _
  rw [ev_exs']
  refine exists_congr fun X => ?_
  rw [ev_exs']
  refine exists_congr fun Y => ?_
  exact ev_faf_mem (et_bvar3 Y X f _)
    (et_comp2 ev_function (et_bvar2 _ Y _) (et_bvar3 _ Y X _))

private lemma ev_value (v f x : ZFSet.{0}) :
    exEv.choose ![v, f, x] Empty.elim SetTheory.value.dfn ↔ v = exApp.choose.2 f x := by
  unfold SetTheory.value.dfn
  change exEv.choose ![v, f, x] Empty.elim (∀¹ _) ↔ _
  rw [ev_all']
  refine (?_ : _ ↔ ∀ z : ZFSet.{0},
      z ∈ v ↔ z ∈ ZFSet.sUnion (exApp.choose.1 f) ∧ ∃ y, z ∈ y ∧ ZFSet.pair x y ∈ f).trans ?_
  · refine forall_congr' fun z => ?_
    rw [ev_iff']
    refine iff_congr (ev_faf_mem (et_bvar1 z _) (et_bvar3 _ z v _)) ?_
    rw [ev_and']
    refine and_congr ?_ ?_
    · exact ev_faf_mem (et_bvar1 z _)
        (et_comp1 ev_sUnion (et_comp1 ev_range (et_bvar4 _ z v f _)))
    · rw [ev_exs']
      refine exists_congr fun y => ?_
      rw [ev_and']
      refine and_congr
        (ev_faf_mem (et_bvar2 y z _) (et_bvar2 _ y _))
        (ev_faf_mem (et_comp2 ev_kpair (et_bvar5 y z v f x _) (et_bvar1 y _))
          (et_bvar5 _ y z v f _))
  · rw [exApp.choose_spec.2]
    constructor
    · intro h; ext z; rw [h z, ZFSet.mem_sep]
    · rintro rfl z; rw [ZFSet.mem_sep]

private lemma zfcApp_of_mem_funs {X Y f x y : ZFSet.{0}}
    (hf : f ∈ ZFSet.funs X Y) (hx : x ∈ X) (hpair : ZFSet.pair x y ∈ f) :
    exApp.choose.2 f x = y := by
  rw [ZFSet.mem_funs] at hf
  obtain ⟨_, huniq⟩ := hf
  obtain ⟨y0, hy0_mem, hy0_eq⟩ := huniq x hx
  have hy_eq : y = y0 := hy0_eq y hpair
  subst hy_eq
  ext z
  rw [exApp.choose_spec.2, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y', hz', hp'⟩
    have rfl' : y' = y := hy0_eq y' hp'
    rwa [← rfl']
  · intro hz
    refine ⟨?_, y, hz, hy0_mem⟩
    rw [ZFSet.mem_sUnion]
    exact ⟨y, mem_relRange.mpr ⟨x, hy0_mem⟩, hz⟩

private lemma zfcApp_mem_codomain {X Y f x : ZFSet.{0}}
    (hf : f ∈ ZFSet.funs X Y) (hx : x ∈ X) :
    exApp.choose.2 f x ∈ Y := by
  have hf' := ZFSet.mem_funs.mp hf
  obtain ⟨y, hy, _⟩ := hf'.2 x hx
  rw [zfcApp_of_mem_funs hf hx hy]
  exact (ZFSet.pair_mem_prod.mp (hf'.1 hy)).2

private lemma funs_ext {X Y f1 f2 : ZFSet.{0}}
    (hf1 : f1 ∈ ZFSet.funs X Y) (hf2 : f2 ∈ ZFSet.funs X Y)
    (heq : ∀ x ∈ X, exApp.choose.2 f1 x = exApp.choose.2 f2 x) : f1 = f2 := by
  obtain ⟨hsub1, huniq1⟩ := ZFSet.mem_funs.mp hf1
  obtain ⟨hsub2, huniq2⟩ := ZFSet.mem_funs.mp hf2
  ext p
  constructor
  · intro hp1
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.mp (hsub1 hp1)
    have ha1 := zfcApp_of_mem_funs hf1 hx hp1
    obtain ⟨y2, hy2, _⟩ := huniq2 x hx
    have ha2 := zfcApp_of_mem_funs hf2 hx hy2
    have hy_eq : y = y2 := by rw [← ha1, heq x hx, ha2]
    rwa [hy_eq]
  · intro hp2
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.mp (hsub2 hp2)
    have ha2 := zfcApp_of_mem_funs hf2 hx hp2
    obtain ⟨y1, hy1, _⟩ := huniq1 x hx
    have ha1 := zfcApp_of_mem_funs hf1 hx hy1
    have hy_eq : y = y1 := by rw [← ha2, ← heq x hx, ha1]
    rwa [hy_eq]

private lemma dc_zero :
    ∀ z : ZFSet.{0}, exEv.choose ![z] Empty.elim Constant14.zero ↔ z = ∅ := by
  intro z; unfold Constant14.zero; exact (ev_subst1_c _ _ _).trans (ev_isEmpty z)

private lemma dc_numeral (k : ℕ) :
    ∀ y : ZFSet.{0}, exEv.choose ![y] Empty.elim (Constant14.numeral k) ↔ y = exVnNat.choose k := by
  induction k with
  | zero =>
    intro y; rw [vnNat_zero]; exact dc_zero y
  | succ k ih =>
    intro y
    unfold Constant14.numeral
    rw [vnNat_succ]
    exact et_comp1 ev_succ ih y

private lemma dc_setPair {Ψ₁ Ψ₂ : SetTheorySemisentence 1} {v₁ v₂ : ZFSet.{0}}
    (h₁ : ∀ y : ZFSet.{0}, exEv.choose ![y] Empty.elim Ψ₁ ↔ y = v₁)
    (h₂ : ∀ y : ZFSet.{0}, exEv.choose ![y] Empty.elim Ψ₂ ↔ y = v₂) :
    ∀ y : ZFSet.{0}, exEv.choose ![y] Empty.elim (Constant14.setPair Ψ₁ Ψ₂) ↔
      y = ZFSet.pair v₁ v₂ := by
  intro y
  unfold Constant14.setPair
  have h := et_comp2 ev_kpair (fun z => (ev_e1 z ![] Ψ₁).trans (h₁ z))
    (fun z => (ev_e1 z ![] Ψ₂).trans (h₂ z)) y
  rwa [ev_e1] at h

private lemma dc_setTriple {Ψ₁ Ψ₂ Ψ₃ : SetTheorySemisentence 1} {v₁ v₂ v₃ : ZFSet.{0}}
    (h₁ : ∀ y : ZFSet.{0}, exEv.choose ![y] Empty.elim Ψ₁ ↔ y = v₁)
    (h₂ : ∀ y : ZFSet.{0}, exEv.choose ![y] Empty.elim Ψ₂ ↔ y = v₂)
    (h₃ : ∀ y : ZFSet.{0}, exEv.choose ![y] Empty.elim Ψ₃ ↔ y = v₃) :
    ∀ y : ZFSet.{0}, exEv.choose ![y] Empty.elim (Constant14.setTriple Ψ₁ Ψ₂ Ψ₃) ↔
      y = ZFSet.pair v₁ (ZFSet.pair v₂ v₃) :=
  dc_setPair h₁ (dc_setPair h₂ h₃)

private lemma exListSet :
    ∃ f : List ZFSet.{0} → ZFSet.{0}, f [] = ∅ ∧ ∀ x xs, f (x :: xs) = insert x (f xs) :=
  ⟨fun l => List.rec ∅ (fun x _ acc => insert x acc) l, rfl, fun _ _ => rfl⟩

@[local simp] private lemma listSet_nil : exListSet.choose [] = ∅ := exListSet.choose_spec.1
@[local simp] private lemma listSet_cons (x : ZFSet.{0}) (xs : List ZFSet.{0}) :
    exListSet.choose (x :: xs) = insert x (exListSet.choose xs) := exListSet.choose_spec.2 x xs

private lemma mem_listToZFSet {z : ZFSet.{0}} {xs : List ZFSet.{0}} :
    z ∈ exListSet.choose xs ↔ z ∈ xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

private lemma dc_finiteSet_map {α : Type*} (l : List α)
    (fForm : α → SetTheorySemisentence 1) (fVal : α → ZFSet.{0})
    (hf : ∀ a y, exEv.choose ![y] Empty.elim (fForm a) ↔ y = fVal a) :
    ∀ y : ZFSet.{0}, exEv.choose ![y] Empty.elim (Constant14.finiteSet (l.map fForm)) ↔
      y = exListSet.choose (l.map fVal) := by
  induction l with
  | nil =>
    intro y
    simp only [List.map_nil, Constant14.finiteSet, listSet_nil]
    exact dc_zero y
  | cons a as ih =>
    intro y
    simp only [List.map_cons, Constant14.finiteSet, listSet_cons]
    have h := et_comp2 ev_insert
      (fun z => (ev_e1 z ![] (fForm a)).trans (hf a z))
      (fun z => (ev_e1 z ![] (Constant14.finiteSet (as.map fForm))).trans (ih z)) y
    rwa [ev_e1] at h

private lemma dc_integers :
    ∀ y : ZFSet.{0}, exEv.choose ![y] Empty.elim Constant14.integers ↔
      y = ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose) := by
  intro y
  unfold Constant14.integers
  exact ev_faf_eq (et_bvar1 y _)
    (et_comp2 ev_prod (et_const0 (dc_numeral 2) _) (et_const0 dc_isω _))

private lemma exEncInt :
    ∃ f : ℤ → ZFSet.{0},
      (∀ k : ℕ, f (Int.ofNat k) = ZFSet.pair (exVnNat.choose 0) (exVnNat.choose k)) ∧
      (∀ k : ℕ, f (Int.negSucc k) = ZFSet.pair (exVnNat.choose 1) (exVnNat.choose k)) :=
  ⟨fun z => match z with
    | Int.ofNat k => ZFSet.pair (exVnNat.choose 0) (exVnNat.choose k)
    | Int.negSucc k => ZFSet.pair (exVnNat.choose 1) (exVnNat.choose k),
   fun _ => rfl, fun _ => rfl⟩

@[local simp] private lemma encInt_ofNat (k : ℕ) :
    exEncInt.choose (Int.ofNat k) = ZFSet.pair (exVnNat.choose 0) (exVnNat.choose k) :=
  exEncInt.choose_spec.1 k

@[local simp] private lemma encInt_negSucc (k : ℕ) :
    exEncInt.choose (Int.negSucc k) = ZFSet.pair (exVnNat.choose 1) (exVnNat.choose k) :=
  exEncInt.choose_spec.2 k

private lemma encodeInt_mem (z : ℤ) :
    exEncInt.choose z ∈ ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose) := by
  cases z with
  | ofNat k =>
    rw [encInt_ofNat]
    exact ZFSet.pair_mem_prod.mpr
      ⟨vnNat_lt_mem (by decide : 0 < 2), ZFSet.mem_range.mpr ⟨k, rfl⟩⟩
  | negSucc k =>
    rw [encInt_negSucc]
    exact ZFSet.pair_mem_prod.mpr
      ⟨vnNat_lt_mem (by decide : 1 < 2), ZFSet.mem_range.mpr ⟨k, rfl⟩⟩

private lemma mem_intSet_iff {w : ZFSet.{0}} :
    w ∈ ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose) ↔
      ∃ z : ℤ, w = exEncInt.choose z := by
  refine ⟨?_, fun ⟨z, hz⟩ => hz ▸ encodeInt_mem z⟩
  intro hw
  obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp hw
  obtain ⟨s, hs, rfl⟩ := mem_vnNat_iff.mp ha
  obtain ⟨k, rfl⟩ := ZFSet.mem_range.mp hb
  interval_cases s
  · exact ⟨Int.ofNat k, (encInt_ofNat k).symm⟩
  · exact ⟨Int.negSucc k, (encInt_negSucc k).symm⟩

private lemma encodeInt_injective : Function.Injective exEncInt.choose := by
  intro z1 z2 heq
  cases z1 <;> cases z2 <;> simp only [encInt_ofNat, encInt_negSucc, ZFSet.pair_inj] at heq
  · rw [vnNat_injective heq.2]
  · exfalso; exact absurd (vnNat_injective heq.1) (by decide)
  · exfalso; exact absurd (vnNat_injective heq.1) (by decide)
  · rw [vnNat_injective heq.2]

private lemma dc_integerZero :
    ∀ y : ZFSet.{0}, exEv.choose ![y] Empty.elim Constant14.integerZero ↔
      y = exEncInt.choose 0 := by
  intro y
  unfold Constant14.integerZero
  have h0 : exEncInt.choose 0 = ZFSet.pair (exVnNat.choose 0) (exVnNat.choose 0) := encInt_ofNat 0
  rw [h0]
  exact ev_faf_eq (et_bvar1 y _)
    (et_comp2 ev_kpair (et_const0 (dc_numeral 0) _) (et_const0 (dc_numeral 0) _))

private lemma ev_integerSucc_encode (z : ℤ) (w' : ZFSet.{0}) :
    exEv.choose ![w', exEncInt.choose z] Empty.elim Constant14.integerSucc.dfn ↔
      w' = exEncInt.choose (z + 1) := by
  unfold Constant14.integerSucc.dfn
  rw [ev_or', ev_and', ev_and']
  rw [ev_faf_mem (et_bvar2 w' (exEncInt.choose z) _) (et_const0 dc_integers _),
      ev_faf_notMem (et_bvar2 w' (exEncInt.choose z) _) (et_const0 dc_integers _)]
  simp only [encodeInt_mem z, not_true_eq_false, false_and, or_false, true_and]
  refine (?_ : _ ↔
      ((exPi.choose.1 (exEncInt.choose z) = exVnNat.choose 0 ∧
          w' = ZFSet.pair (exVnNat.choose 0)
            (insert (exPi.choose.2 (exEncInt.choose z)) (exPi.choose.2 (exEncInt.choose z)))) ∨
        (exPi.choose.1 (exEncInt.choose z) = exVnNat.choose 1 ∧
          ((exPi.choose.2 (exEncInt.choose z) = exVnNat.choose 0 ∧ w' = exEncInt.choose 0) ∨
            ∃ m ∈ ZFSet.range exVnNat.choose, exPi.choose.2 (exEncInt.choose z) = insert m m ∧
              w' = ZFSet.pair (exVnNat.choose 1) m)))).trans ?_
  · rw [ev_or', ev_and', ev_and', ev_or', ev_and']
    refine or_congr
      (and_congr
        (ev_faf_eq (et_comp1 ev_pi1 (et_bvar2 w' (exEncInt.choose z) _))
          (et_const0 (dc_numeral 0) _))
        (ev_faf_eq (et_bvar1 w' _)
          (et_comp2 ev_kpair (et_const0 (dc_numeral 0) _)
            (et_comp1 ev_succ (et_comp1 ev_pi2 (et_bvar3 _ w' (exEncInt.choose z) _))))))
      (and_congr
        (ev_faf_eq (et_comp1 ev_pi1 (et_bvar2 w' (exEncInt.choose z) _))
          (et_const0 (dc_numeral 1) _))
        (or_congr
          (and_congr
            (ev_faf_eq (et_comp1 ev_pi2 (et_bvar2 w' (exEncInt.choose z) _))
              (et_const0 (dc_numeral 0) _))
            (ev_faf_eq (et_bvar1 w' _) (et_const0 dc_integerZero _)))
          ?_))
    rw [ev_faf_bexs (et_const0 dc_isω _)]
    refine exists_congr fun m => and_congr_right fun _ => ?_
    rw [ev_and']
    exact and_congr
      (ev_faf_eq (et_comp1 ev_pi2 (et_bvar4 m (ZFSet.range exVnNat.choose) w' (exEncInt.choose z) _))
        (et_comp1 ev_succ (et_bvar2 _ m _)))
      (ev_faf_eq (et_bvar3 m (ZFSet.range exVnNat.choose) w' _)
        (et_comp2 ev_kpair (et_const0 (dc_numeral 1) _) (et_bvar2 _ m _)))
  · have h01 : exVnNat.choose 0 ≠ exVnNat.choose 1 :=
      fun h => absurd (vnNat_injective h) (by decide)
    have h10 : exVnNat.choose 1 ≠ exVnNat.choose 0 := h01.symm
    cases z with
    | ofNat k =>
      simp only [encInt_ofNat, pi1Val_pair, pi2Val_pair, h01, false_and, or_false, true_and]
      have hsucc : (Int.ofNat k : ℤ) + 1 = Int.ofNat (k + 1) := rfl
      rw [hsucc, encInt_ofNat, vnNat_succ]
    | negSucc k =>
      simp only [encInt_negSucc, pi1Val_pair, pi2Val_pair, h10, false_and, false_or, true_and]
      cases k with
      | zero =>
        have hno_pred : ¬ ∃ m ∈ ZFSet.range exVnNat.choose,
            exVnNat.choose 0 = insert m m ∧ w' = ZFSet.pair (exVnNat.choose 1) m := by
          rintro ⟨m, _, hm, _⟩
          have : m ∈ exVnNat.choose 0 := hm ▸ ZFSet.mem_insert m m
          rw [vnNat_zero] at this
          exact ZFSet.notMem_empty m this
        simp only [true_and, hno_pred, or_false]
        have hz0 : Int.negSucc 0 + 1 = (0 : ℤ) := by omega
        rw [hz0]
      | succ k =>
        have hne0 : exVnNat.choose (k + 1) ≠ exVnNat.choose 0 :=
          fun h => absurd (vnNat_injective h) (by omega)
        simp only [hne0, false_and, false_or]
        have hstep : Int.negSucc (k + 1) + 1 = Int.negSucc k := by omega
        rw [hstep, encInt_negSucc]
        constructor
        · rintro ⟨m, hm, hsucc, rfl⟩
          obtain ⟨r, rfl⟩ := ZFSet.mem_range.mp hm
          rw [← vnNat_succ] at hsucc
          have hr : k + 1 = r + 1 := vnNat_injective hsucc
          have hk : r = k := by omega
          subst hk; rfl
        · rintro rfl
          exact ⟨exVnNat.choose k, ZFSet.mem_range.mpr ⟨k, rfl⟩, vnNat_succ k, rfl⟩

private lemma ev_integerPred_encode (z : ℤ) (w' : ZFSet.{0}) :
    exEv.choose ![w', exEncInt.choose z] Empty.elim Constant14.integerPred.dfn ↔
      w' = exEncInt.choose (z - 1) := by
  unfold Constant14.integerPred.dfn
  rw [ev_or', ev_and', ev_and', ev_and']
  rw [ev_faf_mem (et_bvar2 w' (exEncInt.choose z) _) (et_const0 dc_integers _),
      ev_faf_mem (et_bvar1 w' _) (et_const0 dc_integers _),
      ev_nest2 Constant14.integerSucc.dfn (et_bvar2 w' (exEncInt.choose z) _) (et_bvar1 w' _),
      ev_faf_notMem (et_bvar2 w' (exEncInt.choose z) _) (et_const0 dc_integers _)]
  simp only [encodeInt_mem z, not_true_eq_false, false_and, or_false, true_and]
  constructor
  · rintro ⟨hw', hsucc⟩
    obtain ⟨u, rfl⟩ := mem_intSet_iff.mp hw'
    rw [ev_integerSucc_encode u (exEncInt.choose z)] at hsucc
    have hzu : z = u + 1 := encodeInt_injective hsucc
    have hu : u = z - 1 := by omega
    rw [hu]
  · rintro rfl
    refine ⟨encodeInt_mem (z - 1), ?_⟩
    rw [ev_integerSucc_encode (z - 1) (exEncInt.choose z)]
    exact congrArg exEncInt.choose (by omega)

/- ## Part 4: Semantic Faithfulness of `Constant14.halts M` in `ZFSet.{0}` -/

private lemma dc_configSet (N : ℕ) :
    ∀ y : ZFSet.{0}, exEv.choose ![y] Empty.elim (Constant14.configSet N) ↔
      y = ZFSet.prod (exVnNat.choose N)
        (ZFSet.prod (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
          (ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
            (exVnNat.choose 2))) := by
  intro y
  unfold Constant14.configSet
  exact ev_faf_eq (et_bvar1 y _)
    (et_comp2 ev_prod (et_const0 (dc_numeral N) _)
      (et_comp2 ev_prod (et_const0 dc_integers _)
        (et_comp2 ev_function (et_const0 (dc_numeral 2) _) (et_const0 dc_integers _))))

private lemma mem_cfgSetVal_iff {N : ℕ} {z : ZFSet.{0}} :
    z ∈ ZFSet.prod (exVnNat.choose N)
        (ZFSet.prod (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
          (ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
            (exVnNat.choose 2))) ↔
      ∃ (qCode : ℕ) (pos : ℤ) (g : ZFSet.{0}),
        qCode < N ∧
        g ∈ ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
          (exVnNat.choose 2) ∧
        z = ZFSet.pair (exVnNat.choose qCode) (ZFSet.pair (exEncInt.choose pos) g) := by
  constructor
  · intro hz
    obtain ⟨s, hs, p, hp, rfl⟩ := ZFSet.mem_prod.mp hz
    obtain ⟨qCode, hq, rfl⟩ := mem_vnNat_iff.mp hs
    obtain ⟨w, hw, g, hg, rfl⟩ := ZFSet.mem_prod.mp hp
    obtain ⟨pos, rfl⟩ := mem_intSet_iff.mp hw
    exact ⟨qCode, pos, g, hq, hg, rfl⟩
  · rintro ⟨qCode, pos, g, hq, hg, rfl⟩
    exact ZFSet.pair_mem_prod.mpr
      ⟨vnNat_lt_mem hq, ZFSet.pair_mem_prod.mpr ⟨encodeInt_mem pos, hg⟩⟩

private lemma transitionCode_bounds {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (q : Fin n) (sym : Fin 2) :
    let o := Constant14.transitionCode M q sym
    o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
  dsimp only [Constant14.transitionCode]
  cases M q sym with
  | none =>
    dsimp only [Constant14.directionCode]
    exact ⟨Nat.lt_succ_self n, sym.isLt, by decide⟩
  | some p =>
    rcases p with ⟨q', ⟨sym', d⟩⟩
    dsimp only
    refine ⟨?_, sym'.isLt, ?_⟩
    · cases q' with
      | none => exact Nat.lt_succ_self n
      | some qv => exact Nat.lt_succ_of_lt qv.isLt
    · cases d <;> decide

private lemma blank_tape_nth (i : ℤ) : (Tape.mk₁ ([] : List (Fin 2))).nth i = 0 := by
  cases i with
  | ofNat k =>
    cases k <;> simp [Tape.mk₁, Tape.mk₂, Tape.nth, Tape.mk', Fin.default_eq_zero]
  | negSucc k =>
    simp [Tape.mk₁, Tape.mk₂, Tape.nth, Tape.mk', Fin.default_eq_zero]

private lemma exTapeOps :
    ∃ ops : (ZFSet.{0} → ZFSet.{0} → ZFSet.{0} → ZFSet.{0}) × (ZFSet.{0} → ℤ) ×
            (Tape (Fin 2) → ℤ → ZFSet.{0}),
      (∀ g posSet valSet, ops.1 g posSet valSet =
        letI : ZFSet.Definable₁ (fun w => if w = posSet then valSet else exApp.choose.2 g w) :=
          Classical.allZFSetDefinable _
        ZFSet.map (fun w => if w = posSet then valSet else exApp.choose.2 g w)
          (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))) ∧
      (∀ w, ops.2.1 w =
        if hw : w ∈ ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose) then
          Classical.choose (mem_intSet_iff.mp hw) else 0) ∧
      (∀ T pos, ops.2.2 T pos =
        let fn : ZFSet.{0} → ZFSet.{0} := fun w => exVnNat.choose (T.nth (ops.2.1 w - pos)).val
        letI : ZFSet.Definable₁ fn := Classical.allZFSetDefinable _
        ZFSet.map fn (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))) := by
  let upd : ZFSet.{0} → ZFSet.{0} → ZFSet.{0} → ZFSet.{0} := fun g posSet valSet =>
    letI : ZFSet.Definable₁ (fun w => if w = posSet then valSet else exApp.choose.2 g w) :=
      Classical.allZFSetDefinable _
    ZFSet.map (fun w => if w = posSet then valSet else exApp.choose.2 g w)
      (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
  let dec : ZFSet.{0} → ℤ := fun w =>
    if hw : w ∈ ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose) then
      Classical.choose (mem_intSet_iff.mp hw) else 0
  let enc : Tape (Fin 2) → ℤ → ZFSet.{0} := fun T pos =>
    let fn : ZFSet.{0} → ZFSet.{0} := fun w => exVnNat.choose (T.nth (dec w - pos)).val
    letI : ZFSet.Definable₁ fn := Classical.allZFSetDefinable _
    ZFSet.map fn (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
  exact ⟨⟨upd, dec, enc⟩, fun _ _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

private lemma zfcUpdateTape_mem_funs {g posSet valSet : ZFSet.{0}}
    (hg : g ∈ ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
      (exVnNat.choose 2))
    (hval : valSet ∈ exVnNat.choose 2) :
    exTapeOps.choose.1 g posSet valSet ∈
      ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
        (exVnNat.choose 2) := by
  rw [exTapeOps.choose_spec.1]
  let fn : ZFSet.{0} → ZFSet.{0} := fun w => if w = posSet then valSet else exApp.choose.2 g w
  let _ : ZFSet.Definable₁ fn := Classical.allZFSetDefinable _
  change ZFSet.map fn _ ∈ ZFSet.funs _ (exVnNat.choose 2)
  rw [ZFSet.mem_funs, ZFSet.map_isFunc]
  intro w hw; dsimp [fn]; split_ifs
  · exact hval
  · exact zfcApp_mem_codomain hg hw

private lemma zfcUpdateTape_app {g posSet valSet w : ZFSet.{0}}
    (hg : g ∈ ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
      (exVnNat.choose 2))
    (hval : valSet ∈ exVnNat.choose 2)
    (hw : w ∈ ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose)) :
    exApp.choose.2 (exTapeOps.choose.1 g posSet valSet) w =
      if w = posSet then valSet else exApp.choose.2 g w := by
  let fn : ZFSet.{0} → ZFSet.{0} := fun u => if u = posSet then valSet else exApp.choose.2 g u
  let _ : ZFSet.Definable₁ fn := Classical.allZFSetDefinable _
  have hfuns := zfcUpdateTape_mem_funs (posSet := posSet) hg hval
  have hmem : ZFSet.pair w (fn w) ∈ exTapeOps.choose.1 g posSet valSet := by
    rw [exTapeOps.choose_spec.1]
    exact ZFSet.mem_map.mpr ⟨w, hw, rfl⟩
  exact zfcApp_of_mem_funs hfuns hw hmem

private lemma decodePos_encodeInt (p : ℤ) : exTapeOps.choose.2.1 (exEncInt.choose p) = p := by
  rw [exTapeOps.choose_spec.2.1, dif_pos (encodeInt_mem p)]
  exact encodeInt_injective (Classical.choose_spec (mem_intSet_iff.mp (encodeInt_mem p))).symm

private lemma encodeTape_funs_and_app (T : Tape (Fin 2)) (pos : ℤ) :
    exTapeOps.choose.2.2 T pos ∈
        ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
          (exVnNat.choose 2) ∧
      ∀ m : ℤ, exApp.choose.2 (exTapeOps.choose.2.2 T pos) (exEncInt.choose m) =
        exVnNat.choose (T.nth (m - pos)).val := by
  let fn : ZFSet.{0} → ZFSet.{0} :=
    fun w => exVnNat.choose (T.nth (exTapeOps.choose.2.1 w - pos)).val
  let _ : ZFSet.Definable₁ fn := Classical.allZFSetDefinable _
  have hfn_eq (m : ℤ) : fn (exEncInt.choose m) = exVnNat.choose (T.nth (m - pos)).val := by
    dsimp [fn]; rw [decodePos_encodeInt]
  have hfuns : exTapeOps.choose.2.2 T pos ∈
      ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
        (exVnNat.choose 2) := by
    rw [exTapeOps.choose_spec.2.2]
    change ZFSet.map fn _ ∈ ZFSet.funs _ (exVnNat.choose 2)
    rw [ZFSet.mem_funs, ZFSet.map_isFunc]
    intro w hw
    obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
    rw [hfn_eq m]
    exact vnNat_lt_mem (T.nth (m - pos)).isLt
  refine ⟨hfuns, fun m => ?_⟩
  have hmem : ZFSet.pair (exEncInt.choose m) (fn (exEncInt.choose m)) ∈
      exTapeOps.choose.2.2 T pos := by
    rw [exTapeOps.choose_spec.2.2]
    exact ZFSet.mem_map.mpr ⟨exEncInt.choose m, encodeInt_mem m, rfl⟩
  rw [zfcApp_of_mem_funs hfuns (encodeInt_mem m) hmem, hfn_eq m]

private lemma dc_emptyTape :
    ∀ f : ZFSet.{0}, exEv.choose ![f] Empty.elim Constant14.emptyTape ↔
      f = exTapeOps.choose.2.2 (Tape.mk₁ []) 0 := by
  intro f
  unfold Constant14.emptyTape
  rw [ev_and']
  rw [ev_faf_mem (et_bvar1 f _)
        (et_comp2 ev_function (et_const0 (dc_numeral 2) _) (et_const0 dc_integers _)),
      ev_faf_ball (et_const0 dc_integers _)]
  refine (and_congr Iff.rfl (forall₂_congr fun i _ =>
      (?_ : _ ↔ exApp.choose.2 f i = exVnNat.choose 0))).trans ?_
  · exact ev_faf_eq
      (et_comp2 ev_value
        (et_bvar3 i (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose)) f _)
        (et_bvar1 i _))
      (et_const0 (dc_numeral 0) _)
  · obtain ⟨he_funs, he_app⟩ := encodeTape_funs_and_app (Tape.mk₁ []) 0
    constructor
    · rintro ⟨hf, hall⟩
      refine funs_ext hf he_funs fun w hw => ?_
      obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
      rw [hall (exEncInt.choose m) hw, he_app m, blank_tape_nth]; rfl
    · rintro rfl
      refine ⟨he_funs, fun w hw => ?_⟩
      obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
      rw [he_app m, blank_tape_nth]; rfl

private lemma exInstr {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ∃ pair : ZFSet.{0} × (ℕ → ℕ → ℕ × ℕ × ℕ),
      pair.1 = exListSet.choose
        (((List.ofFn fun q : Fin n =>
            List.ofFn fun sym : Fin 2 =>
              let o := Constant14.transitionCode M q sym
              (q.val, sym.val, o.1, o.2.1, o.2.2)).flatten ++
          List.ofFn fun sym : Fin 2 =>
            (n, sym.val, n, sym.val, Constant14.directionCode none)).map
          (fun t => ZFSet.pair (ZFSet.pair (exVnNat.choose t.1) (exVnNat.choose t.2.1))
            (ZFSet.pair (exVnNat.choose t.2.2.1)
              (ZFSet.pair (exVnNat.choose t.2.2.2.1) (exVnNat.choose t.2.2.2.2))))) ∧
      ∀ qCode symCode, pair.2 qCode symCode =
        if hq : qCode < n then
          if hs : symCode < 2 then Constant14.transitionCode M ⟨qCode, hq⟩ ⟨symCode, hs⟩
          else (n, 0, 1)
        else (n, symCode, 1) :=
  ⟨⟨_, fun qCode symCode =>
      if hq : qCode < n then
        if hs : symCode < 2 then Constant14.transitionCode M ⟨qCode, hq⟩ ⟨symCode, hs⟩
        else (n, 0, 1)
      else (n, symCode, 1)⟩, rfl, fun _ _ => rfl⟩

private lemma dc_instructionTable {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ∀ y : ZFSet.{0}, exEv.choose ![y] Empty.elim (Constant14.instructionTable M) ↔
      y = (exInstr M).choose.1 := by
  let entryForm : ℕ × ℕ × ℕ × ℕ × ℕ → SetTheorySemisentence 1 :=
    fun t => Constant14.transitionEntry t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2
  let entryVal : ℕ × ℕ × ℕ × ℕ × ℕ → ZFSet.{0} :=
    fun t => ZFSet.pair (ZFSet.pair (exVnNat.choose t.1) (exVnNat.choose t.2.1))
      (ZFSet.pair (exVnNat.choose t.2.2.1)
        (ZFSet.pair (exVnNat.choose t.2.2.2.1) (exVnNat.choose t.2.2.2.2)))
  let tuples : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
    (List.ofFn fun q : Fin n =>
      List.ofFn fun sym : Fin 2 =>
        let o := Constant14.transitionCode M q sym
        (q.val, sym.val, o.1, o.2.1, o.2.2)).flatten ++
    List.ofFn fun sym : Fin 2 =>
      (n, sym.val, n, sym.val, Constant14.directionCode none)
  have dc_entry : ∀ t y, exEv.choose ![y] Empty.elim (entryForm t) ↔ y = entryVal t := fun t =>
    dc_setPair (dc_setPair (dc_numeral _) (dc_numeral _))
      (dc_setTriple (dc_numeral _) (dc_numeral _) (dc_numeral _))
  intro y
  rw [(exInstr M).choose_spec.1]
  unfold Constant14.instructionTable
  have hmap : tuples.map entryForm = Constant14.transitionEntries M := by
    simp [tuples, Constant14.transitionEntries, entryForm, List.map_flatten,
      List.map_ofFn, Function.comp_def]
  rw [← hmap]
  exact dc_finiteSet_map tuples entryForm entryVal dc_entry y

private lemma instrTableVal_funs_and_app {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    (exInstr M).choose.1 ∈ ZFSet.funs
        (ZFSet.prod (exVnNat.choose (n + 1)) (exVnNat.choose 2))
        (ZFSet.prod (exVnNat.choose (n + 1))
          (ZFSet.prod (exVnNat.choose 2) (exVnNat.choose 3))) ∧
      ∀ (qCode symCode : ℕ), qCode < n + 1 → symCode < 2 →
        exApp.choose.2 (exInstr M).choose.1
            (ZFSet.pair (exVnNat.choose qCode) (exVnNat.choose symCode)) =
          let o := (exInstr M).choose.2 qCode symCode
          ZFSet.pair (exVnNat.choose o.1)
            (ZFSet.pair (exVnNat.choose o.2.1) (exVnNat.choose o.2.2)) := by
  let entryVal : ℕ × ℕ × ℕ × ℕ × ℕ → ZFSet.{0} :=
    fun t => ZFSet.pair (ZFSet.pair (exVnNat.choose t.1) (exVnNat.choose t.2.1))
      (ZFSet.pair (exVnNat.choose t.2.2.1)
        (ZFSet.pair (exVnNat.choose t.2.2.2.1) (exVnNat.choose t.2.2.2.2)))
  have hmem_iff : ∀ p : ZFSet.{0}, p ∈ (exInstr M).choose.1 ↔
      (∃ (q : Fin n) (sym : Fin 2),
        let o := Constant14.transitionCode M q sym
        p = entryVal (q.val, sym.val, o.1, o.2.1, o.2.2)) ∨
      (∃ sym : Fin 2, p = entryVal (n, sym.val, n, sym.val, 1)) := by
    intro p
    rw [(exInstr M).choose_spec.1, mem_listToZFSet, List.mem_map]
    simp only [List.mem_append, List.mem_flatten, List.mem_ofFn, Constant14.directionCode]
    constructor
    · rintro ⟨t, (⟨l, ⟨q, rfl⟩, ht⟩ | ⟨sym, rfl⟩), rfl⟩
      · obtain ⟨sym, rfl⟩ := List.mem_ofFn.mp ht; exact Or.inl ⟨q, sym, rfl⟩
      · exact Or.inr ⟨sym, rfl⟩
    · rintro (⟨q, sym, rfl⟩ | ⟨sym, rfl⟩)
      · refine ⟨_, Or.inl ⟨_, ⟨q, rfl⟩, List.mem_ofFn.mpr ⟨sym, rfl⟩⟩, rfl⟩
      · exact ⟨_, Or.inr ⟨sym, rfl⟩, rfl⟩
  have hfuns : (exInstr M).choose.1 ∈ ZFSet.funs
      (ZFSet.prod (exVnNat.choose (n + 1)) (exVnNat.choose 2))
      (ZFSet.prod (exVnNat.choose (n + 1))
        (ZFSet.prod (exVnNat.choose 2) (exVnNat.choose 3))) := by
    rw [ZFSet.mem_funs, ZFSet.IsFunc]
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases (hmem_iff p).mp hp with ⟨q, sym, rfl⟩ | ⟨sym, rfl⟩
      · obtain ⟨hb1, hb2, hb3⟩ := transitionCode_bounds M q sym
        exact ZFSet.pair_mem_prod.mpr
          ⟨ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem (Nat.lt_succ_of_lt q.isLt), vnNat_lt_mem sym.isLt⟩,
           ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem hb1,
             ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem hb2, vnNat_lt_mem hb3⟩⟩⟩
      · exact ZFSet.pair_mem_prod.mpr
          ⟨ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem (Nat.lt_succ_self n), vnNat_lt_mem sym.isLt⟩,
           ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem (Nat.lt_succ_self n),
             ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem sym.isLt, vnNat_lt_mem (by decide : 1 < 3)⟩⟩⟩
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp hx
      obtain ⟨qCode, hq, rfl⟩ := mem_vnNat_iff.mp ha
      obtain ⟨symCode, hs, rfl⟩ := mem_vnNat_iff.mp hb
      let o := (exInstr M).choose.2 qCode symCode
      refine ⟨ZFSet.pair (exVnNat.choose o.1)
          (ZFSet.pair (exVnNat.choose o.2.1) (exVnNat.choose o.2.2)), ?_, ?_⟩
      · dsimp only
        rw [hmem_iff]
        by_cases hqn : qCode < n
        · left; refine ⟨⟨qCode, hqn⟩, ⟨symCode, hs⟩, ?_⟩
          dsimp only [o]; rw [(exInstr M).choose_spec.2, dif_pos hqn, dif_pos hs]
        · have hqe : qCode = n := by omega
          subst qCode
          right; refine ⟨⟨symCode, hs⟩, ?_⟩
          dsimp only [o]; rw [(exInstr M).choose_spec.2, dif_neg (Nat.lt_irrefl n)]
      · intro y hy
        rcases (hmem_iff _).mp hy with ⟨q, sym, heq⟩ | ⟨sym, heq⟩
        · obtain ⟨h1, rfl⟩ := ZFSet.pair_injective heq
          obtain ⟨hq1, hs1⟩ := ZFSet.pair_injective h1
          have hqc : qCode = q.val := vnNat_injective hq1
          have hsc : symCode = sym.val := vnNat_injective hs1
          subst qCode symCode
          dsimp only [o]; rw [(exInstr M).choose_spec.2, dif_pos q.isLt, dif_pos sym.isLt]
        · obtain ⟨h1, rfl⟩ := ZFSet.pair_injective heq
          obtain ⟨hq1, hs1⟩ := ZFSet.pair_injective h1
          have hqc : qCode = n := vnNat_injective hq1
          have hsc : symCode = sym.val := vnNat_injective hs1
          subst qCode symCode
          dsimp only [o]; rw [(exInstr M).choose_spec.2, dif_neg (Nat.lt_irrefl n)]
  refine ⟨hfuns, fun qCode symCode hq hs => ?_⟩
  have hx : ZFSet.pair (exVnNat.choose qCode) (exVnNat.choose symCode) ∈
      ZFSet.prod (exVnNat.choose (n + 1)) (exVnNat.choose 2) :=
    ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem hq, vnNat_lt_mem hs⟩
  let o := (exInstr M).choose.2 qCode symCode
  have hmem_pair : ZFSet.pair (ZFSet.pair (exVnNat.choose qCode) (exVnNat.choose symCode))
      (ZFSet.pair (exVnNat.choose o.1)
        (ZFSet.pair (exVnNat.choose o.2.1) (exVnNat.choose o.2.2))) ∈ (exInstr M).choose.1 := by
    rw [hmem_iff]
    by_cases hqn : qCode < n
    · left; refine ⟨⟨qCode, hqn⟩, ⟨symCode, hs⟩, ?_⟩
      dsimp only [o]; rw [(exInstr M).choose_spec.2, dif_pos hqn, dif_pos hs]
    · have hqe : qCode = n := by omega
      subst qCode
      right; refine ⟨⟨symCode, hs⟩, ?_⟩
      dsimp only [o]; rw [(exInstr M).choose_spec.2, dif_neg (Nat.lt_irrefl n)]
  exact zfcApp_of_mem_funs hfuns hx hmem_pair

private lemma exStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ∃ p : (ZFSet.{0} → ZFSet.{0}) × ZFSet.{0},
      (∀ z, p.1 z =
        if z ∈ ZFSet.prod (exVnNat.choose (n + 1))
            (ZFSet.prod (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
              (ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
                (exVnNat.choose 2))) then
          let qSet := exPi.choose.1 z
          let posSet := exPi.choose.1 (exPi.choose.2 z)
          let g := exPi.choose.2 (exPi.choose.2 z)
          let symSet := exApp.choose.2 g posSet
          let t := exApp.choose.2 (exInstr M).choose.1 (ZFSet.pair qSet symSet)
          let qNext := exPi.choose.1 t
          let wrSet := exPi.choose.1 (exPi.choose.2 t)
          let dirSet := exPi.choose.2 (exPi.choose.2 t)
          let posVal := exTapeOps.choose.2.1 posSet
          let posNext : ZFSet.{0} :=
            if dirSet = exVnNat.choose 0 then exEncInt.choose (posVal - 1)
            else if dirSet = exVnNat.choose 1 then exEncInt.choose posVal
            else exEncInt.choose (posVal + 1)
          let gNext := exTapeOps.choose.1 g posSet wrSet
          ZFSet.pair qNext (ZFSet.pair posNext gNext)
        else ∅) ∧
      p.2 =
        letI : ZFSet.Definable₁ p.1 := Classical.allZFSetDefinable _
        ZFSet.map p.1 (ZFSet.prod (exVnNat.choose (n + 1))
          (ZFSet.prod (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
            (ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
              (exVnNat.choose 2)))) := by
  let f : ZFSet.{0} → ZFSet.{0} := fun z =>
    if z ∈ ZFSet.prod (exVnNat.choose (n + 1))
        (ZFSet.prod (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
          (ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
            (exVnNat.choose 2))) then
      let qSet := exPi.choose.1 z
      let posSet := exPi.choose.1 (exPi.choose.2 z)
      let g := exPi.choose.2 (exPi.choose.2 z)
      let symSet := exApp.choose.2 g posSet
      let t := exApp.choose.2 (exInstr M).choose.1 (ZFSet.pair qSet symSet)
      let qNext := exPi.choose.1 t
      let wrSet := exPi.choose.1 (exPi.choose.2 t)
      let dirSet := exPi.choose.2 (exPi.choose.2 t)
      let posVal := exTapeOps.choose.2.1 posSet
      let posNext : ZFSet.{0} :=
        if dirSet = exVnNat.choose 0 then exEncInt.choose (posVal - 1)
        else if dirSet = exVnNat.choose 1 then exEncInt.choose posVal
        else exEncInt.choose (posVal + 1)
      let gNext := exTapeOps.choose.1 g posSet wrSet
      ZFSet.pair qNext (ZFSet.pair posNext gNext)
    else ∅
  let _ : ZFSet.Definable₁ f := Classical.allZFSetDefinable _
  exact ⟨⟨f, ZFSet.map f _⟩, fun _ => rfl, rfl⟩

private lemma zfcStepFn_of_cfg {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (qCode : ℕ) (pos : ℤ) (g : ZFSet.{0})
    (hq : qCode < n + 1)
    (hg : g ∈ ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
      (exVnNat.choose 2))
    (symCode : ℕ) (hs : symCode < 2)
    (hsym : exApp.choose.2 g (exEncInt.choose pos) = exVnNat.choose symCode) :
    let o := (exInstr M).choose.2 qCode symCode
    let pos' : ℤ := if o.2.2 = 0 then pos - 1 else if o.2.2 = 1 then pos else pos + 1
    (exStep M).choose.1 (ZFSet.pair (exVnNat.choose qCode) (ZFSet.pair (exEncInt.choose pos) g)) =
      ZFSet.pair (exVnNat.choose o.1)
        (ZFSet.pair (exEncInt.choose pos')
          (exTapeOps.choose.1 g (exEncInt.choose pos) (exVnNat.choose o.2.1))) := by
  let z := ZFSet.pair (exVnNat.choose qCode) (ZFSet.pair (exEncInt.choose pos) g)
  have hz : z ∈ ZFSet.prod (exVnNat.choose (n + 1))
      (ZFSet.prod (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
        (ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
          (exVnNat.choose 2))) :=
    mem_cfgSetVal_iff.mpr ⟨qCode, pos, g, hq, hg, rfl⟩
  rw [(exStep M).choose_spec.1, if_pos hz]
  dsimp only
  have hp1 : exPi.choose.1 z = exVnNat.choose qCode := pi1Val_pair _ _
  have hp2 : exPi.choose.2 z = ZFSet.pair (exEncInt.choose pos) g := pi2Val_pair _ _
  have hpos : exPi.choose.1 (exPi.choose.2 z) = exEncInt.choose pos := by rw [hp2, pi1Val_pair]
  have hgv : exPi.choose.2 (exPi.choose.2 z) = g := by rw [hp2, pi2Val_pair]
  obtain ⟨_, happ⟩ := instrTableVal_funs_and_app M
  let o := (exInstr M).choose.2 qCode symCode
  have ht : exApp.choose.2 (exInstr M).choose.1
      (ZFSet.pair (exPi.choose.1 z)
        (exApp.choose.2 (exPi.choose.2 (exPi.choose.2 z))
          (exPi.choose.1 (exPi.choose.2 z)))) =
      ZFSet.pair (exVnNat.choose o.1)
        (ZFSet.pair (exVnNat.choose o.2.1) (exVnNat.choose o.2.2)) := by
    rw [hp1, hgv, hpos, hsym]
    exact happ qCode symCode hq hs
  rw [ht, pi1Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, hpos, hgv, decodePos_encodeInt]
  congr 1; congr 1
  have hd0 : (exVnNat.choose o.2.2 = exVnNat.choose 0) ↔ (o.2.2 = 0) := vnNat_injective.eq_iff
  have hd1 : (exVnNat.choose o.2.2 = exVnNat.choose 1) ↔ (o.2.2 = 1) := vnNat_injective.eq_iff
  simp only [hd0, hd1]; dsimp only [o]; split_ifs <;> rfl

private lemma zfcStepFn_mem_cfg {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    {z : ZFSet.{0}}
    (hz : z ∈ ZFSet.prod (exVnNat.choose (n + 1))
      (ZFSet.prod (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
        (ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
          (exVnNat.choose 2)))) :
    (exStep M).choose.1 z ∈ ZFSet.prod (exVnNat.choose (n + 1))
      (ZFSet.prod (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
        (ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
          (exVnNat.choose 2))) := by
  obtain ⟨qCode, pos, g, hq, hg, rfl⟩ := mem_cfgSetVal_iff.mp hz
  have hsym_mem : exApp.choose.2 g (exEncInt.choose pos) ∈ exVnNat.choose 2 :=
    zfcApp_mem_codomain hg (encodeInt_mem pos)
  obtain ⟨symCode, hs, hsym⟩ := mem_vnNat_iff.mp hsym_mem
  rw [zfcStepFn_of_cfg M qCode pos g hq hg symCode hs hsym]
  let o := (exInstr M).choose.2 qCode symCode
  have hob : o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
    dsimp only [o]; rw [(exInstr M).choose_spec.2]
    by_cases hqn : qCode < n
    · rw [dif_pos hqn, dif_pos hs]
      exact transitionCode_bounds M ⟨qCode, hqn⟩ ⟨symCode, hs⟩
    · rw [dif_neg hqn]; dsimp only; exact ⟨Nat.lt_succ_self n, hs, by decide⟩
  exact mem_cfgSetVal_iff.mpr
    ⟨o.1, if o.2.2 = 0 then pos - 1 else if o.2.2 = 1 then pos else pos + 1,
     exTapeOps.choose.1 g (exEncInt.choose pos) (exVnNat.choose o.2.1),
     hob.1, zfcUpdateTape_mem_funs hg (vnNat_lt_mem hob.2.1), rfl⟩

private lemma ev_nextConfig_iff {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (z' z : ZFSet.{0}) :
    exEv.choose ![z', z] Empty.elim (Constant14.nextConfig (n + 1) (Constant14.instructionTable M)) ↔
      z ∈ ZFSet.prod (exVnNat.choose (n + 1))
          (ZFSet.prod (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
            (ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
              (exVnNat.choose 2))) ∧
        z' = (exStep M).choose.1 z := by
  let intSet := ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose)
  let cfgSet := ZFSet.prod (exVnNat.choose (n + 1))
    (ZFSet.prod intSet (ZFSet.funs intSet (exVnNat.choose 2)))
  unfold Constant14.nextConfig
  rw [ev_and', ev_and']
  rw [ev_faf_mem (et_bvar2 z' z _) (et_const0 (dc_configSet (n + 1)) _),
      ev_faf_mem (et_bvar1 z' _) (et_const0 (dc_configSet (n + 1)) _)]
  change (z ∈ cfgSet ∧ z' ∈ cfgSet ∧ _) ↔ (z ∈ cfgSet ∧ _)
  by_cases hz : z ∈ cfgSet
  · simp only [hz, true_and]
    obtain ⟨qCode, pos, g, hq, hg, rfl⟩ := mem_cfgSetVal_iff.mp hz
    let z0 := ZFSet.pair (exVnNat.choose qCode) (ZFSet.pair (exEncInt.choose pos) g)
    have hsym_mem : exApp.choose.2 g (exEncInt.choose pos) ∈ exVnNat.choose 2 :=
      zfcApp_mem_codomain hg (encodeInt_mem pos)
    obtain ⟨symCode, hs, hsym⟩ := mem_vnNat_iff.mp hsym_mem
    let o := (exInstr M).choose.2 qCode symCode
    have hob : o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
      dsimp only [o]; rw [(exInstr M).choose_spec.2]
      by_cases hqn : qCode < n
      · rw [dif_pos hqn, dif_pos hs]
        exact transitionCode_bounds M ⟨qCode, hqn⟩ ⟨symCode, hs⟩
      · rw [dif_neg hqn]; dsimp only; exact ⟨Nat.lt_succ_self n, hs, by decide⟩
    let tVal := ZFSet.pair (exVnNat.choose o.1)
      (ZFSet.pair (exVnNat.choose o.2.1) (exVnNat.choose o.2.2))
    let pos' : ℤ := if o.2.2 = 0 then pos - 1 else if o.2.2 = 1 then pos else pos + 1
    have hstep_val := zfcStepFn_of_cfg M qCode pos g hq hg symCode hs hsym
    change (exStep M).choose.1 z0 = ZFSet.pair (exVnNat.choose o.1)
      (ZFSet.pair (exEncInt.choose pos')
        (exTapeOps.choose.1 g (exEncInt.choose pos) (exVnNat.choose o.2.1))) at hstep_val
    obtain ⟨_, happ⟩ := instrTableVal_funs_and_app M
    have htVal_eq : exApp.choose.2 (exInstr M).choose.1
        (ZFSet.pair (exPi.choose.1 z0)
          (exApp.choose.2 (exPi.choose.2 (exPi.choose.2 z0))
            (exPi.choose.1 (exPi.choose.2 z0)))) = tVal := by
      dsimp [z0, tVal]
      rw [pi1Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, hsym]
      exact happ qCode symCode hq hs
    rw [ev_exs']
    refine (and_congr Iff.rfl (exists_congr fun t => (?_ : _ ↔
        (t = tVal ∧
         exPi.choose.1 z' = exPi.choose.1 t ∧
         ((exPi.choose.2 (exPi.choose.2 t) = exVnNat.choose 0 ∧
             exEv.choose ![exPi.choose.1 (exPi.choose.2 z'), exPi.choose.1 (exPi.choose.2 z0)]
               Empty.elim Constant14.integerPred.dfn) ∨
           (exPi.choose.2 (exPi.choose.2 t) = exVnNat.choose 1 ∧
             exPi.choose.1 (exPi.choose.2 z') = exPi.choose.1 (exPi.choose.2 z0)) ∨
           (exPi.choose.2 (exPi.choose.2 t) = exVnNat.choose 2 ∧
             exEv.choose ![exPi.choose.1 (exPi.choose.2 z'), exPi.choose.1 (exPi.choose.2 z0)]
               Empty.elim Constant14.integerSucc.dfn)) ∧
         exApp.choose.2 (exPi.choose.2 (exPi.choose.2 z')) (exPi.choose.1 (exPi.choose.2 z0)) =
           exPi.choose.1 (exPi.choose.2 t) ∧
         ∀ k ∈ intSet, k ≠ exPi.choose.1 (exPi.choose.2 z0) →
           exApp.choose.2 (exPi.choose.2 (exPi.choose.2 z')) k =
             exApp.choose.2 (exPi.choose.2 (exPi.choose.2 z0)) k)))).trans ?_
    · rw [ev_and', ev_and', ev_and', ev_and']
      refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
      · rw [ev_faf_eq (et_bvar1 t _)
          (et_comp2 ev_value (et_const0 (dc_instructionTable M) _)
            (et_comp2 ev_kpair
              (et_comp1 ev_pi1 (et_bvar4 _ t z' z0 _))
              (et_comp2 ev_value
                (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar4 _ t z' z0 _)))
                (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar4 _ t z' z0 _)))))),
          htVal_eq]
      · exact ev_faf_eq
          (et_comp1 ev_pi1 (et_bvar2 t z' _))
          (et_comp1 ev_pi1 (et_bvar2 _ t _))
      · rw [ev_or', ev_or', ev_and', ev_and', ev_and']
        refine or_congr
          (and_congr
            (ev_faf_eq (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar1 t _)))
              (et_const0 (dc_numeral 0) _))
            (ev_nest2 Constant14.integerPred.dfn
              (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar2 t z' _)))
              (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar3 t z' z0 _)))))
          (or_congr
            (and_congr
              (ev_faf_eq (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar1 t _)))
                (et_const0 (dc_numeral 1) _))
              (ev_faf_eq
                (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar2 t z' _)))
                (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar4 _ t z' z0 _)))))
            (and_congr
              (ev_faf_eq (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar1 t _)))
                (et_const0 (dc_numeral 2) _))
              (ev_nest2 Constant14.integerSucc.dfn
                (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar2 t z' _)))
                (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar3 t z' z0 _))))))
      · exact ev_faf_eq
          (et_comp2 ev_value
            (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar2 t z' _)))
            (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar3 t z' z0 _))))
          (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar2 _ t _)))
      · rw [ev_faf_ball (et_const0 dc_integers _)]
        refine forall₂_congr fun k _ => ?_
        rw [ev_imp']
        exact imp_congr
          (ev_faf_ne (et_bvar1 k _)
            (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar6 _ k intSet t z' z0 _))))
          (ev_faf_eq
            (et_comp2 ev_value
              (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar4 k intSet t z' _)))
              (et_bvar1 k _))
            (et_comp2 ev_value
              (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar6 _ k intSet t z' z0 _)))
              (et_bvar2 _ k _)))
    · constructor
      · rintro ⟨hz', t, rfl, hq_eq, hdir, hwr, hrest⟩
        obtain ⟨q2, pos2, g2, _, hg2, rfl⟩ := mem_cfgSetVal_iff.mp hz'
        dsimp [z0, tVal] at hq_eq hdir hwr hrest
        rw [pi1Val_pair, pi1Val_pair] at hq_eq
        rw [pi2Val_pair, pi2Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, pi1Val_pair] at hdir
        rw [pi2Val_pair, pi2Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, pi1Val_pair] at hwr
        simp only [pi2Val_pair, pi1Val_pair] at hrest
        rw [hstep_val, hq_eq]
        congr 1; congr 1
        · have hd2 := hob.2.2
          interval_cases hdv : o.2.2
          · have h01 : exVnNat.choose 0 ≠ exVnNat.choose 1 :=
              fun h => absurd (vnNat_injective h) (by decide)
            have h02 : exVnNat.choose 0 ≠ exVnNat.choose 2 :=
              fun h => absurd (vnNat_injective h) (by decide)
            simp only [true_and, h01, h02, false_and, or_false] at hdir
            rw [ev_integerPred_encode] at hdir
            dsimp [pos']; rw [hdv]; simpa using hdir
          · have h10 : exVnNat.choose 1 ≠ exVnNat.choose 0 :=
              fun h => absurd (vnNat_injective h) (by decide)
            have h12 : exVnNat.choose 1 ≠ exVnNat.choose 2 :=
              fun h => absurd (vnNat_injective h) (by decide)
            simp only [true_and, h10, h12, false_and, false_or, or_false] at hdir
            dsimp [pos']; rw [hdv]; simpa using hdir
          · have h20 : exVnNat.choose 2 ≠ exVnNat.choose 0 :=
              fun h => absurd (vnNat_injective h) (by decide)
            have h21 : exVnNat.choose 2 ≠ exVnNat.choose 1 :=
              fun h => absurd (vnNat_injective h) (by decide)
            simp only [true_and, h20, h21, false_and, false_or] at hdir
            rw [ev_integerSucc_encode] at hdir
            dsimp [pos']; rw [hdv]; simpa using hdir
        · refine funs_ext hg2 (zfcUpdateTape_mem_funs hg (vnNat_lt_mem hob.2.1)) fun k hk => ?_
          rw [zfcUpdateTape_app hg (vnNat_lt_mem hob.2.1) hk]
          by_cases hkp : k = exEncInt.choose pos
          · rw [if_pos hkp, hkp, hwr]
          · rw [if_neg hkp, hrest k hk hkp]
      · rintro rfl
        refine ⟨zfcStepFn_mem_cfg M hz, tVal, rfl, ?_, ?_, ?_, ?_⟩
        · rw [hstep_val]; dsimp [tVal]; rw [pi1Val_pair, pi1Val_pair]
        · rw [hstep_val]; dsimp [z0, tVal]
          rw [pi2Val_pair, pi2Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, pi1Val_pair]
          have hd2 := hob.2.2
          interval_cases hdv : o.2.2
          · left; refine ⟨rfl, ?_⟩
            rw [ev_integerPred_encode]; dsimp [pos']; rw [hdv]; rfl
          · right; left; refine ⟨rfl, ?_⟩
            dsimp [pos']; rw [hdv]; rfl
          · right; right; refine ⟨rfl, ?_⟩
            rw [ev_integerSucc_encode]; dsimp [pos']; rw [hdv]; rfl
        · rw [hstep_val]; dsimp [z0, tVal]
          rw [pi2Val_pair, pi2Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, pi1Val_pair]
          rw [zfcUpdateTape_app hg (vnNat_lt_mem hob.2.1) (encodeInt_mem pos), if_pos rfl]
        · intro k hk hne
          dsimp [z0] at hne
          rw [pi2Val_pair, pi1Val_pair] at hne
          rw [hstep_val]; dsimp [z0]
          rw [pi2Val_pair, pi2Val_pair, pi2Val_pair, pi2Val_pair]
          rw [zfcUpdateTape_app hg (vnNat_lt_mem hob.2.1) hk, if_neg hne]
  · simp [hz]

private lemma nextStepVal_funs_and_app {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    (exStep M).choose.2 ∈ ZFSet.funs
        (ZFSet.prod (exVnNat.choose (n + 1))
          (ZFSet.prod (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
            (ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
              (exVnNat.choose 2))))
        (ZFSet.prod (exVnNat.choose (n + 1))
          (ZFSet.prod (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
            (ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
              (exVnNat.choose 2)))) ∧
      ∀ z ∈ ZFSet.prod (exVnNat.choose (n + 1))
          (ZFSet.prod (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
            (ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
              (exVnNat.choose 2))),
        exApp.choose.2 (exStep M).choose.2 z = (exStep M).choose.1 z := by
  let _ : ZFSet.Definable₁ (exStep M).choose.1 := Classical.allZFSetDefinable _
  let cfgSet := ZFSet.prod (exVnNat.choose (n + 1))
    (ZFSet.prod (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
      (ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
        (exVnNat.choose 2)))
  have hfuns : (exStep M).choose.2 ∈ ZFSet.funs cfgSet cfgSet := by
    rw [(exStep M).choose_spec.2, ZFSet.mem_funs, ZFSet.map_isFunc]
    exact fun _ hz => zfcStepFn_mem_cfg M hz
  refine ⟨hfuns, fun z hz => ?_⟩
  have hmem : ZFSet.pair z ((exStep M).choose.1 z) ∈ (exStep M).choose.2 := by
    rw [(exStep M).choose_spec.2]
    exact ZFSet.mem_map.mpr ⟨z, hz, rfl⟩
  exact zfcApp_of_mem_funs hfuns hz hmem

private lemma dc_nextStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ∀ p : ZFSet.{0},
      exEv.choose ![p] Empty.elim (Constant14.nextStep (n + 1) (Constant14.instructionTable M)) ↔
        p = (exStep M).choose.2 := by
  let _ : ZFSet.Definable₁ (exStep M).choose.1 := Classical.allZFSetDefinable _
  intro p
  unfold Constant14.nextStep
  change exEv.choose ![p] Empty.elim (∀¹ _) ↔ _
  rw [ev_all']
  refine (?_ : _ ↔ ∀ e : ZFSet.{0}, e ∈ p ↔ e ∈ (exStep M).choose.2).trans
    ⟨fun h => ZFSet.ext h, fun h e => by rw [h]⟩
  refine forall_congr' fun e => ?_
  rw [ev_iff']
  refine iff_congr (ev_faf_mem (et_bvar1 e _) (et_bvar3 _ e p _)) ?_
  rw [ev_faf_bexs (et_const0 (dc_configSet (n + 1)) _)]
  refine (?_ : _ ↔ ∃ z ∈ ZFSet.prod (exVnNat.choose (n + 1))
        (ZFSet.prod (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
          (ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
            (exVnNat.choose 2))),
      ∃ z' ∈ ZFSet.prod (exVnNat.choose (n + 1))
        (ZFSet.prod (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
          (ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
            (exVnNat.choose 2))),
      e = ZFSet.pair z z' ∧ z' = (exStep M).choose.1 z).trans ?_
  · refine exists_congr fun z => and_congr_right fun hz => ?_
    rw [ev_faf_bexs (et_const0 (dc_configSet (n + 1)) _)]
    refine exists_congr fun z' => and_congr_right fun _ => ?_
    rw [ev_and']
    rw [ev_faf_eq (et_bvar5 z' _ z _ e _)
          (et_comp2 ev_kpair (et_bvar4 _ z' _ z _) (et_bvar2 _ z' _)),
        ev_nest2 (Constant14.nextConfig (n + 1) (Constant14.instructionTable M))
          (et_bvar1 z' _) (et_bvar3 z' _ z _),
        ev_nextConfig_iff M z' z]
    exact and_congr Iff.rfl ⟨And.right, fun h => ⟨hz, h⟩⟩
  · rw [(exStep M).choose_spec.2, ZFSet.mem_map]
    constructor
    · rintro ⟨z, hz, z', _, rfl, rfl⟩; exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, (exStep M).choose.1 z, zfcStepFn_mem_cfg M hz, rfl, rfl⟩

private lemma exExtSim {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ∃ s : ((Option (Fin n) × ℤ × Tape (Fin 2)) → (Option (Fin n) × ℤ × Tape (Fin 2))) ×
          ((Option (Fin n) × ℤ × Tape (Fin 2)) → ZFSet.{0}),
      (∀ pos T, s.1 (none, pos, T) = (none, pos, T)) ∧
      (∀ q pos T, s.1 (some q, pos, T) =
        match M q T.head with
        | none => (none, pos, T)
        | some (q', Stmt.write sym d) =>
          let pos' := match d with | Dir.left => pos - 1 | Dir.right => pos + 1
          (q', pos', (T.write sym).move d)) ∧
      (∀ c, s.2 c =
        ZFSet.pair (exVnNat.choose (Constant14.stateCode c.1))
          (ZFSet.pair (exEncInt.choose c.2.1) (exTapeOps.choose.2.2 c.2.2 c.2.1))) :=
  ⟨⟨fun c => match c with
      | (none, pos, T) => (none, pos, T)
      | (some q, pos, T) =>
        match M q T.head with
        | none => (none, pos, T)
        | some (q', Stmt.write sym d) =>
          let pos' := match d with | Dir.left => pos - 1 | Dir.right => pos + 1
          (q', pos', (T.write sym).move d),
    fun c => ZFSet.pair (exVnNat.choose (Constant14.stateCode c.1))
      (ZFSet.pair (exEncInt.choose c.2.1) (exTapeOps.choose.2.2 c.2.2 c.2.1))⟩,
   fun _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

private lemma encodeExtCfg_mem {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (c : Option (Fin n) × ℤ × Tape (Fin 2)) :
    (exExtSim M).choose.2 c ∈ ZFSet.prod (exVnNat.choose (n + 1))
      (ZFSet.prod (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
        (ZFSet.funs (ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose))
          (exVnNat.choose 2))) := by
  rw [(exExtSim M).choose_spec.2.2]
  refine mem_cfgSetVal_iff.mpr ⟨Constant14.stateCode c.1, c.2.1,
    exTapeOps.choose.2.2 c.2.2 c.2.1, ?_, (encodeTape_funs_and_app c.2.2 c.2.1).1, rfl⟩
  cases c.1 with
  | none => exact Nat.lt_succ_self n
  | some q => exact Nat.lt_succ_of_lt q.isLt

private lemma dc_initialConfig {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ∀ z : ZFSet.{0}, exEv.choose ![z] Empty.elim Constant14.initialConfig ↔
      z = (exExtSim M).choose.2 (some 0, 0, Tape.mk₁ []) := by
  intro z
  rw [(exExtSim M).choose_spec.2.2]
  unfold Constant14.initialConfig
  rw [ev_faf_eq (et_bvar1 z _)
    (et_comp2 ev_kpair (et_const0 (dc_numeral 0) _)
      (et_comp2 ev_kpair (et_const0 dc_integerZero _) (et_const0 dc_emptyTape _)))]
  rfl

private lemma zfcStepFn_encodeExtCfg {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (c : Option (Fin n) × ℤ × Tape (Fin 2)) :
    (exStep M).choose.1 ((exExtSim M).choose.2 c) =
      (exExtSim M).choose.2 ((exExtSim M).choose.1 c) := by
  rcases c with ⟨qOpt, pos, T⟩
  obtain ⟨hg, happ⟩ := encodeTape_funs_and_app T pos
  have hsym : exApp.choose.2 (exTapeOps.choose.2.2 T pos) (exEncInt.choose pos) =
      exVnNat.choose T.head.val := by
    have h := happ pos; rw [sub_self] at h; exact h
  cases qOpt with
  | none =>
    rw [(exExtSim M).choose_spec.2.2, (exExtSim M).choose_spec.1, (exExtSim M).choose_spec.2.2]
    dsimp only [Constant14.stateCode]
    rw [zfcStepFn_of_cfg M n pos (exTapeOps.choose.2.2 T pos) (Nat.lt_succ_self n) hg
      T.head.val T.head.isLt hsym]
    have hlu : (exInstr M).choose.2 n T.head.val = (n, T.head.val, 1) := by
      rw [(exInstr M).choose_spec.2, dif_neg (Nat.lt_irrefl n)]
    rw [hlu]
    have h10 : (1 : ℕ) ≠ 0 := by decide
    simp only [h10, ↓reduceIte]
    congr 1; congr 1
    refine funs_ext (zfcUpdateTape_mem_funs hg (vnNat_lt_mem T.head.isLt)) hg fun w hw => ?_
    obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
    rw [zfcUpdateTape_app hg (vnNat_lt_mem T.head.isLt) hw]
    by_cases hmp : m = pos
    · subst hmp; rw [if_pos rfl, happ m, sub_self]; rfl
    · have hne : exEncInt.choose m ≠ exEncInt.choose pos := fun h => hmp (encodeInt_injective h)
      rw [if_neg hne]
  | some q =>
    rw [(exExtSim M).choose_spec.2.2, (exExtSim M).choose_spec.2.1]
    dsimp only [Constant14.stateCode]
    rw [zfcStepFn_of_cfg M q.val pos (exTapeOps.choose.2.2 T pos) (Nat.lt_succ_of_lt q.isLt) hg
      T.head.val T.head.isLt hsym]
    have hlu : (exInstr M).choose.2 q.val T.head.val = Constant14.transitionCode M q T.head := by
      rw [(exInstr M).choose_spec.2, dif_pos q.isLt, dif_pos T.head.isLt]
    rw [hlu]
    unfold Constant14.transitionCode
    cases hM' : M q T.head with
    | none =>
      dsimp only
      refine Eq.trans ?_ ((exExtSim M).choose_spec.2.2 (none, pos, T)).symm
      dsimp only [Constant14.directionCode, Constant14.stateCode]
      refine congrArg (ZFSet.pair _) (congrArg₂ ZFSet.pair rfl ?_)
      refine funs_ext (zfcUpdateTape_mem_funs hg (vnNat_lt_mem T.head.isLt)) hg fun w hw => ?_
      obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
      rw [zfcUpdateTape_app hg (vnNat_lt_mem T.head.isLt) hw]
      by_cases hmp : m = pos
      · subst hmp; rw [if_pos rfl, happ m, sub_self]; rfl
      · have hne : exEncInt.choose m ≠ exEncInt.choose pos := fun h => hmp (encodeInt_injective h)
        rw [if_neg hne]
    | some pairOut =>
      rcases pairOut with ⟨q', ⟨sym, d⟩⟩
      cases d with
      | left =>
        dsimp only
        refine Eq.trans ?_
          ((exExtSim M).choose_spec.2.2 (q', pos - 1, (T.write sym).move Dir.left)).symm
        dsimp only [Constant14.directionCode]
        refine congrArg (ZFSet.pair _) (congrArg₂ ZFSet.pair rfl ?_)
        obtain ⟨hg', happ'⟩ := encodeTape_funs_and_app ((T.write sym).move Dir.left) (pos - 1)
        refine funs_ext (zfcUpdateTape_mem_funs hg (vnNat_lt_mem sym.isLt)) hg' fun w hw => ?_
        obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
        rw [zfcUpdateTape_app hg (vnNat_lt_mem sym.isLt) hw, happ' m, Tape.move_left_nth]
        have hidx : m - (pos - 1) - 1 = m - pos := by omega
        rw [hidx, Tape.write_nth]
        by_cases hmp : m = pos
        · subst hmp; rw [if_pos rfl, sub_self, if_pos rfl]
        · have hne1 : exEncInt.choose m ≠ exEncInt.choose pos :=
            fun h => hmp (encodeInt_injective h)
          have hne2 : m - pos ≠ 0 := by omega
          rw [if_neg hne1, if_neg hne2, happ m]
      | right =>
        dsimp only
        refine Eq.trans ?_
          ((exExtSim M).choose_spec.2.2 (q', pos + 1, (T.write sym).move Dir.right)).symm
        dsimp only [Constant14.directionCode]
        refine congrArg (ZFSet.pair _) (congrArg₂ ZFSet.pair rfl ?_)
        obtain ⟨hg', happ'⟩ := encodeTape_funs_and_app ((T.write sym).move Dir.right) (pos + 1)
        refine funs_ext (zfcUpdateTape_mem_funs hg (vnNat_lt_mem sym.isLt)) hg' fun w hw => ?_
        obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
        rw [zfcUpdateTape_app hg (vnNat_lt_mem sym.isLt) hw, happ' m, Tape.move_right_nth]
        have hidx : m - (pos + 1) + 1 = m - pos := by omega
        rw [hidx, Tape.write_nth]
        by_cases hmp : m = pos
        · subst hmp; rw [if_pos rfl, sub_self, if_pos rfl]
        · have hne1 : exEncInt.choose m ≠ exEncInt.choose pos :=
            fun h => hmp (encodeInt_injective h)
          have hne2 : m - pos ≠ 0 := by omega
          rw [if_neg hne1, if_neg hne2, happ m]

private lemma iterate_nextStepVal_eq {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (k : ℕ) :
    (exApp.choose.2 (exStep M).choose.2)^[k] ((exExtSim M).choose.2 (some 0, 0, Tape.mk₁ [])) =
      (exExtSim M).choose.2 ((exExtSim M).choose.1^[k] (some 0, 0, Tape.mk₁ [])) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    obtain ⟨_, happ⟩ := nextStepVal_funs_and_app M
    rw [happ _ (encodeExtCfg_mem M _), zfcStepFn_encodeExtCfg]

private lemma ev_orbit_range {f x0 : ZFSet.{0}} (hfunc : ∃ X Y : ZFSet.{0}, f ∈ ZFSet.funs X Y) :
    exEv.choose ![ZFSet.range (fun k : ℕ => (exApp.choose.2 f)^[k] x0), f, x0] Empty.elim
      Constant14.orbit := by
  let O := ZFSet.range (fun k : ℕ => (exApp.choose.2 f)^[k] x0)
  unfold Constant14.orbit
  rw [ev_and']
  refine ⟨?_, ?_⟩
  · rw [ev_nest1 SetTheory.IsFunction.dfn (et_bvar2 O f _), ev_IsFunction]; exact hfunc
  · rw [ev_all']; intro z
    rw [ev_iff', ev_faf_mem (et_bvar1 z _) (et_bvar3 _ z O _), ev_all']
    have hO_iff : z ∈ O ↔ ∀ A : ZFSet.{0}, (x0 ∈ A ∧ ∀ y ∈ A, exApp.choose.2 f y ∈ A) → z ∈ A := by
      constructor
      · intro hzO A ⟨hx0, hclosed⟩
        obtain ⟨k, rfl⟩ := ZFSet.mem_range.mp hzO
        clear hzO
        induction k with
        | zero => exact hx0
        | succ k ih => rw [Function.iterate_succ_apply']; exact hclosed _ ih
      · intro hall
        refine hall O ⟨ZFSet.mem_range.mpr ⟨0, rfl⟩, ?_⟩
        intro y hy
        obtain ⟨k, rfl⟩ := ZFSet.mem_range.mp hy
        exact ZFSet.mem_range.mpr ⟨k + 1, Function.iterate_succ_apply' _ k x0⟩
    rw [hO_iff]
    symm
    refine forall_congr' fun A => ?_
    rw [ev_imp', ev_and']
    refine imp_congr (and_congr ?_ ?_) (ev_faf_mem (et_bvar2 A z _) (et_bvar2 _ A _))
    · exact ev_faf_mem (et_bvar5 A z O f x0 _) (et_bvar2 _ A _)
    · rw [ev_faf_ball (et_bvar1 A _)]
      refine forall₂_congr fun y _ => ?_
      exact ev_faf_mem
        (et_comp2 ev_value (et_bvar6 y A A z O f _) (et_bvar1 y _))
        (et_bvar4 _ y A A _)

private lemma multiStep_agrees_with_extStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ∀ (k : ℕ) (qk : Fin n) (Tk : Tape (Fin 2)),
      M.multiStep (Machine.init []) k = some ⟨some qk, Tk⟩ →
        ((exExtSim M).choose.1^[k] (some 0, 0, Tape.mk₁ [])).1 = some qk ∧
          ((exExtSim M).choose.1^[k] (some 0, 0, Tape.mk₁ [])).2.2 = Tk := by
  intro k
  induction k with
  | zero =>
    intro qk Tk h0
    simp only [Machine.multiStep_zero, Machine.init, Fin.default_eq_zero, Option.some.injEq,
      Cfg.mk.injEq] at h0
    rcases h0 with ⟨hq, hT⟩; subst hq hT; exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro qk1 Tk1 hsucc
    rw [Machine.multiStep_succ] at hsucc
    cases hmk : M.multiStep (Machine.init []) k with
    | none => rw [hmk] at hsucc; simp at hsucc
    | some cfg =>
      rw [hmk, Option.bind_some] at hsucc
      rcases cfg with ⟨qOpt, Tk⟩
      cases qOpt with
      | none => simp [Machine.step] at hsucc
      | some qk =>
        obtain ⟨hq_ih, hT_ih⟩ := ih qk Tk hmk
        simp only [Machine.step] at hsucc
        cases hMq : M qk Tk.head with
        | none => rw [hMq] at hsucc; simp at hsucc
        | some out =>
          rw [hMq, Option.map_some, Option.some.injEq] at hsucc
          rcases out with ⟨qNext, ⟨sym, d⟩⟩
          injection hsucc with hqN hTN
          subst hqN hTN
          rw [Function.iterate_succ_apply']
          rcases hext : (exExtSim M).choose.1^[k] (some 0, 0, Tape.mk₁ []) with ⟨c1, posk, cT⟩
          rw [hext] at hq_ih hT_ih
          dsimp only at hq_ih hT_ih
          subst hq_ih hT_ih
          rw [(exExtSim M).choose_spec.2.1, hMq]
          exact ⟨rfl, rfl⟩

private lemma not_ev_halts {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (hM : ¬ M.IsHalting) :
    ¬ exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
        (Constant14.halts M) := by
  intro hhalts
  rw [ev_e0 (Fin.elim0 : Fin 0 → ZFSet.{0}) ![]] at hhalts
  unfold Constant14.halts at hhalts
  rw [ev_faf_bexs (et_const0 dc_integers ![])] at hhalts
  obtain ⟨m, _, hm_body⟩ := hhalts
  rw [ev_faf_bexs
    (et_comp2 ev_function (et_const0 (dc_numeral 2) _) (et_const0 dc_integers _))] at hm_body
  obtain ⟨g, _, hg_body⟩ := hm_body
  let intSet := ZFSet.prod (exVnNat.choose 2) (ZFSet.range exVnNat.choose)
  let target := ZFSet.pair (exVnNat.choose n) (ZFSet.pair m g)
  let x0 := (exExtSim M).choose.2 (some 0, 0, Tape.mk₁ [])
  let O := ZFSet.range (fun k : ℕ => (exApp.choose.2 (exStep M).choose.2)^[k] x0)
  have htarget : ∀ y : ZFSet.{0},
      exEv.choose (y :> g :> ZFSet.funs intSet (exVnNat.choose 2) :> m :> intSet :> ![]) Empty.elim
        (Semiformula.nestFormulaeFunc SetTheory.kpair.dfn
          (Semiformula.nestFormulaeFunc (Constant14.numeral n) ![] :>
            Semiformula.nestFormulaeFunc SetTheory.kpair.dfn
              (op(=).operator (#0 :> #3 :> ![]) :> op(=).operator (#0 :> #1 :> ![]) :> ![]) :> ![])) ↔
        y = target :=
    et_comp2 ev_kpair (et_const0 (dc_numeral n) _)
      (et_comp2 ev_kpair (et_bvar3 g _ m _) (et_bvar1 g _))
  rw [ev_all'] at hg_body
  have hv1 := (ev_imp' _ _ _ _).mp (hg_body target) ((htarget target).mpr rfl)
  rw [ev_all'] at hv1
  have horbit_nest :
      exEv.choose (O :> target :> g :> ZFSet.funs intSet (exVnNat.choose 2) :> m :> intSet :> ![])
        Empty.elim
        (Semiformula.nestFormulaeFunc Constant14.orbit
          (Semiformula.nestFormulaeFunc
            (Constant14.nextStep (n + 1) (Constant14.instructionTable M)) ![] :>
            Semiformula.nestFormulaeFunc Constant14.initialConfig ![] :> ![])) := by
    rw [ev_nestFunc2_raw Constant14.orbit
      (et_const0 (dc_nextStep M) _) (et_const0 (dc_initialConfig M) _) O]
    exact ev_orbit_range ⟨_, _, (nextStepVal_funs_and_app M).1⟩
  have hmem_O := (ev_imp' _ _ _ _).mp (hv1 O) horbit_nest
  rw [ev_mem'] at hmem_O
  have htarget_in_O : target ∈ O := by simpa using hmem_O
  obtain ⟨k, hk⟩ := ZFSet.mem_range.mp htarget_in_O
  rw [iterate_nextStepVal_eq M k, (exExtSim M).choose_spec.2.2] at hk
  dsimp [target] at hk
  obtain ⟨hq_eq, _⟩ := ZFSet.pair_injective hk
  have hcode_eq : Constant14.stateCode ((exExtSim M).choose.1^[k] (some 0, 0, Tape.mk₁ [])).1 = n :=
    vnNat_injective hq_eq
  have hnot_after : ¬ M.HaltsAfter (Machine.init []) k :=
    fun ha => hM ((Machine.isHalting_iff_exists_haltsAt M).mpr ⟨k, ha⟩)
  obtain ⟨qk, Tk, hms⟩ := Machine.exists_of_not_haltsAfter M (Machine.init []) k hnot_after
  obtain ⟨hstate, _⟩ := multiStep_agrees_with_extStep M k qk Tk hms
  rw [hstate] at hcode_eq
  dsimp [Constant14.stateCode] at hcode_eq
  exact absurd hcode_eq (Nat.ne_of_lt qk.isLt)

private lemma zfc_not_halts_of_not_isHalting {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (hM : ¬ M.IsHalting) :
    𝗭𝗙𝗖 ⊬ Constant14.halts M := fun hprov =>
  not_ev_halts M hM (sound_theory zfsetModel hprov)

end Simpset

end Helpers

theorem main : H1 → H2 → type_of% @Constant14.c14_le_20 := by
  intro h1 h2
  obtain ⟨n, hn, M, hle, hnh, hzf_not_nh⟩ := h2
  have hZFC_not_halts : 𝗭𝗙𝗖 ⊬ Constant14.halts M :=
    zfc_not_halts_of_not_isHalting M hnh
  have hZFC_not_nhalts : 𝗭𝗙𝗖 ⊬ ∼Constant14.halts M :=
    fun hprov => hzf_not_nh (h1 n M hprov)
  have hmem : n ∈ {k | ∃ _ : NeZero k, ∃ M' : Machine (Fin 2) (Fin k),
      𝗭𝗙𝗖 ⊬ Constant14.halts M' ∧ 𝗭𝗙𝗖 ⊬ ∼Constant14.halts M'} :=
    ⟨hn, M, hZFC_not_halts, hZFC_not_nhalts⟩
  exact le_trans (Nat.sInf_le hmem) hle

end OMA.R_Constant14_c14_le_20_R1
