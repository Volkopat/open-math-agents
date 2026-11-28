import OMAReductions.R_Constant14_c14_le_432_R1
import Mathlib.Tactic

/-!
# Reduction `Constant14.c14_le_432.R1.H1.R1`

Reduction of `Constant14.c14_le_432.R1.H1` (conservativity of the Axiom of Choice over `𝗭𝗙` for
Turing machine halting and non-halting:
`(Provable 𝗭𝗙𝗖 (halts M) → Provable 𝗭𝗙 (halts M)) ∧ (Provable 𝗭𝗙𝗖 (∼halts M) → Provable 𝗭𝗙 (∼halts M))`)
to two independent, purely model-theoretic theorems:

* `H1`: **Gödel's constructible inner model (`Con(ZF) → Con(ZFC)` in inner-model form)**:
  every normal model `(V, mem) ⊨ 𝗭𝗙` contains a transitive subclass `P : V → Prop` whose
  restriction `({x // P x}, mem|_P)` satisfies every axiom of `𝗭𝗙𝗖` (pure set theory, zero
  mention of Turing machines).
* `H2`: **Two-way absoluteness of `Constant14.halts M` to any transitive inner model of `𝗭𝗙`**:
  for every normal `(V, mem) ⊨ 𝗭𝗙` and transitive subclass `P` modeling `𝗭𝗙`,
  `Constant14.halts M` holds in `V` if and only if it holds in `{x // P x}` (provable in both
  directions even in arbitrary nonstandard `𝗭𝗙` models via `O^L` closure and `ω`-recursion inside `L`).

Inside `main`, we prove completely from scratch in Lean 4 (with zero extra top-level `def`s):
1. Full Gödel Completeness Theorem (`zf_complete`) for `FFL.FirstOrder.Derivation` over `𝗭𝗙`
   via Henkin maximal consistent witness extension and equality-quotienting (adapted to zero-def
   reduction form from `proofs/Constant14.c14_ge_4.R1.H1.lean`, credit `@KevinBigham`).
2. Full soundness (`zfc_sound`) of one-sided LK `FFL.FirstOrder.Derivation` in any normal model
   `(V, mem) ⊨ 𝗭𝗙𝗖` (credit `@mucoucah`, `@Narden91`).
3. Assembly of `H1 → H2 → OMA.R_Constant14_c14_le_432_R1.H1`.

Credit: @Narden91, @KevinBigham, @mucoucah
-/

namespace OMA.R_Constant14_c14_le_432_R1_H1_R1

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver
open scoped Classical

/-- Inner-model existence (Gödel's `L`): every normal model `(V, mem)` of `𝗭𝗙` contains a
transitive subclass `P : V → Prop` whose restriction models `𝗭𝗙𝗖`. -/
def H1 : Prop :=
  let sat (V : Type) (mem : V → V → Prop) (σ : SetTheorySentence) : Prop :=
    let tv {m : ℕ} (e : Fin m → V) : Semiterm ℒₛₑₜ Empty m → V :=
      @Semiterm.rec ℒₛₑₜ Empty m (fun _ => V) e Empty.elim (fun {_} f _ _ => f.elim)
    @Semiformula.rec ℒₛₑₜ Empty (fun m _ => (Fin m → V) → Prop)
      (fun _ => True) (fun _ => False)
      (fun r v e => @Language.Set.Rel.rec (fun k _ => (Fin k → Semiterm ℒₛₑₜ Empty _) → Prop)
        (fun w => tv e (w 0) = tv e (w 1)) (fun w => mem (tv e (w 0)) (tv e (w 1))) _ r v)
      (fun r v e => ¬ @Language.Set.Rel.rec (fun k _ => (Fin k → Semiterm ℒₛₑₜ Empty _) → Prop)
        (fun w => tv e (w 0) = tv e (w 1)) (fun w => mem (tv e (w 0)) (tv e (w 1))) _ r v)
      (fun _ _ a b e => a e ∧ b e) (fun _ _ a b e => a e ∨ b e)
      (fun _ a e => ∀ d, a (d :> e)) (fun _ a e => ∃ d, a (d :> e)) 0 σ Fin.elim0
  ∀ (V : Type) (mem : V → V → Prop), (∀ ψ ∈ 𝗭𝗙, sat V mem ψ) →
    ∃ P : V → Prop, (∀ x y, P y → mem x y → P x) ∧
      ∀ ψ ∈ 𝗭𝗙𝗖, sat {x // P x} (fun a b => mem a.1 b.1) ψ

/-- Two-way absoluteness of `Constant14.halts M` for any transitive inner model of `𝗭𝗙`. -/
def H2 : Prop :=
  let sat (V : Type) (mem : V → V → Prop) (σ : SetTheorySentence) : Prop :=
    let tv {m : ℕ} (e : Fin m → V) : Semiterm ℒₛₑₜ Empty m → V :=
      @Semiterm.rec ℒₛₑₜ Empty m (fun _ => V) e Empty.elim (fun {_} f _ _ => f.elim)
    @Semiformula.rec ℒₛₑₜ Empty (fun m _ => (Fin m → V) → Prop)
      (fun _ => True) (fun _ => False)
      (fun r v e => @Language.Set.Rel.rec (fun k _ => (Fin k → Semiterm ℒₛₑₜ Empty _) → Prop)
        (fun w => tv e (w 0) = tv e (w 1)) (fun w => mem (tv e (w 0)) (tv e (w 1))) _ r v)
      (fun r v e => ¬ @Language.Set.Rel.rec (fun k _ => (Fin k → Semiterm ℒₛₑₜ Empty _) → Prop)
        (fun w => tv e (w 0) = tv e (w 1)) (fun w => mem (tv e (w 0)) (tv e (w 1))) _ r v)
      (fun _ _ a b e => a e ∧ b e) (fun _ _ a b e => a e ∨ b e)
      (fun _ a e => ∀ d, a (d :> e)) (fun _ a e => ∃ d, a (d :> e)) 0 σ Fin.elim0
  ∀ (V : Type) (mem : V → V → Prop) (P : V → Prop),
    (∀ ψ ∈ 𝗭𝗙, sat V mem ψ) → (∀ x y, P y → mem x y → P x) →
    (∀ ψ ∈ 𝗭𝗙, sat {x // P x} (fun a b => mem a.1 b.1) ψ) →
    ∀ (n : ℕ) [NeZero n] (M : Machine (Fin 2) (Fin n)),
      sat V mem (Constant14.halts M) ↔ sat {x // P x} (fun a b => mem a.1 b.1) (Constant14.halts M)

section Helpers

/- ## 1. Zero-def Tarski Semantics on Arbitrary `(V, req, rmem)` -/

private lemma exTvRaw : ∃ tv : ∀ {V : Type} {ξ : Type} {n : ℕ}, (Fin n → V) → (ξ → V) →
      Semiterm ℒₛₑₜ ξ n → V,
    (∀ {V : Type} {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V) (i : Fin n),
      tv e ε (Semiterm.bvar i) = e i) ∧
    (∀ {V : Type} {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V) (x : ξ),
      tv e ε (Semiterm.fvar x) = ε x) :=
  ⟨fun {_} {_} {_} e ε t => match t with
      | Semiterm.bvar i => e i
      | Semiterm.fvar x => ε x
      | Semiterm.func f _ => (f : Empty).elim,
    fun _ _ _ => rfl, fun _ _ _ => rfl⟩

private lemma tvRaw_bvar {V : Type} {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V) (i : Fin n) :
    exTvRaw.choose e ε (Semiterm.bvar i) = e i := exTvRaw.choose_spec.1 e ε i

private lemma tvRaw_fvar {V : Type} {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V) (x : ξ) :
    exTvRaw.choose e ε (Semiterm.fvar x) = ε x := exTvRaw.choose_spec.2 e ε x

private lemma exEvalRaw : ∃ ev : ∀ {V : Type}, (V → V → Prop) → (V → V → Prop) →
      ∀ {ξ : Type} {n : ℕ}, (Fin n → V) → (ξ → V) → Semiformula ℒₛₑₜ ξ n → Prop,
    (∀ {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V),
      ev req rmem e ε (Semiformula.verum : Semiformula ℒₛₑₜ ξ n) ↔ True) ∧
    (∀ {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V),
      ev req rmem e ε (Semiformula.falsum : Semiformula ℒₛₑₜ ξ n) ↔ False) ∧
    (∀ {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V)
      (v : Fin 2 → Semiterm ℒₛₑₜ ξ n),
      ev req rmem e ε (Semiformula.rel Language.Set.Rel.eq v) ↔
        req (exTvRaw.choose e ε (v 0)) (exTvRaw.choose e ε (v 1))) ∧
    (∀ {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V)
      (v : Fin 2 → Semiterm ℒₛₑₜ ξ n),
      ev req rmem e ε (Semiformula.rel Language.Set.Rel.mem v) ↔
        rmem (exTvRaw.choose e ε (v 0)) (exTvRaw.choose e ε (v 1))) ∧
    (∀ {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V)
      (v : Fin 2 → Semiterm ℒₛₑₜ ξ n),
      ev req rmem e ε (Semiformula.nrel Language.Set.Rel.eq v) ↔
        ¬ req (exTvRaw.choose e ε (v 0)) (exTvRaw.choose e ε (v 1))) ∧
    (∀ {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V)
      (v : Fin 2 → Semiterm ℒₛₑₜ ξ n),
      ev req rmem e ε (Semiformula.nrel Language.Set.Rel.mem v) ↔
        ¬ rmem (exTvRaw.choose e ε (v 0)) (exTvRaw.choose e ε (v 1))) ∧
    (∀ {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V)
      (φ ψ : Semiformula ℒₛₑₜ ξ n),
      ev req rmem e ε (Semiformula.and φ ψ) ↔ ev req rmem e ε φ ∧ ev req rmem e ε ψ) ∧
    (∀ {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V)
      (φ ψ : Semiformula ℒₛₑₜ ξ n),
      ev req rmem e ε (Semiformula.or φ ψ) ↔ ev req rmem e ε φ ∨ ev req rmem e ε ψ) ∧
    (∀ {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V)
      (φ : Semiformula ℒₛₑₜ ξ (n + 1)),
      ev req rmem e ε (Semiformula.all φ) ↔ ∀ d : V, ev req rmem (d :> e) ε φ) ∧
    (∀ {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V)
      (φ : Semiformula ℒₛₑₜ ξ (n + 1)),
      ev req rmem e ε (Semiformula.exs φ) ↔ ∃ d : V, ev req rmem (d :> e) ε φ) :=
  ⟨fun {V} req rmem {ξ} {n} e ε φ =>
      @Semiformula.rec ℒₛₑₜ ξ (fun m _ => (Fin m → V) → Prop)
        (fun {_} _ => True)
        (fun {_} _ => False)
        (fun {m k} r v e' =>
          @Language.Set.Rel.rec (fun k' _ => (Fin k' → Semiterm ℒₛₑₜ ξ m) → Prop)
            (fun w => req (exTvRaw.choose e' ε (w 0)) (exTvRaw.choose e' ε (w 1)))
            (fun w => rmem (exTvRaw.choose e' ε (w 0)) (exTvRaw.choose e' ε (w 1))) k r v)
        (fun {m k} r v e' =>
          ¬ @Language.Set.Rel.rec (fun k' _ => (Fin k' → Semiterm ℒₛₑₜ ξ m) → Prop)
            (fun w => req (exTvRaw.choose e' ε (w 0)) (exTvRaw.choose e' ε (w 1)))
            (fun w => rmem (exTvRaw.choose e' ε (w 0)) (exTvRaw.choose e' ε (w 1))) k r v)
        (fun {_} _ _ ih1 ih2 e' => ih1 e' ∧ ih2 e')
        (fun {_} _ _ ih1 ih2 e' => ih1 e' ∨ ih2 e')
        (fun {_} _ ih e' => ∀ d : V, ih (d :> e'))
        (fun {_} _ ih e' => ∃ d : V, ih (d :> e'))
        n φ e,
    fun {_} _ _ {_} {_} _ _ => Iff.rfl, fun {_} _ _ {_} {_} _ _ => Iff.rfl,
    fun {_} _ _ {_} {_} _ _ _ => Iff.rfl, fun {_} _ _ {_} {_} _ _ _ => Iff.rfl,
    fun {_} _ _ {_} {_} _ _ _ => Iff.rfl, fun {_} _ _ {_} {_} _ _ _ => Iff.rfl,
    fun {_} _ _ {_} {_} _ _ _ _ => Iff.rfl, fun {_} _ _ {_} {_} _ _ _ _ => Iff.rfl,
    fun {_} _ _ {_} {_} _ _ _ => Iff.rfl, fun {_} _ _ {_} {_} _ _ _ => Iff.rfl⟩

private lemma ev_verum {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) :
    exEvalRaw.choose req rmem e ε (Semiformula.verum : Semiformula ℒₛₑₜ ξ n) ↔ True :=
  exEvalRaw.choose_spec.1 req rmem e ε

private lemma ev_falsum {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) :
    exEvalRaw.choose req rmem e ε (Semiformula.falsum : Semiformula ℒₛₑₜ ξ n) ↔ False :=
  exEvalRaw.choose_spec.2.1 req rmem e ε

private lemma ev_rel_eq {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    exEvalRaw.choose req rmem e ε (Semiformula.rel Language.Set.Rel.eq v) ↔
      req (exTvRaw.choose e ε (v 0)) (exTvRaw.choose e ε (v 1)) :=
  exEvalRaw.choose_spec.2.2.1 req rmem e ε v

private lemma ev_rel_mem {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    exEvalRaw.choose req rmem e ε (Semiformula.rel Language.Set.Rel.mem v) ↔
      rmem (exTvRaw.choose e ε (v 0)) (exTvRaw.choose e ε (v 1)) :=
  exEvalRaw.choose_spec.2.2.2.1 req rmem e ε v

private lemma ev_nrel_eq {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    exEvalRaw.choose req rmem e ε (Semiformula.nrel Language.Set.Rel.eq v) ↔
      ¬ req (exTvRaw.choose e ε (v 0)) (exTvRaw.choose e ε (v 1)) :=
  exEvalRaw.choose_spec.2.2.2.2.1 req rmem e ε v

private lemma ev_nrel_mem {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    exEvalRaw.choose req rmem e ε (Semiformula.nrel Language.Set.Rel.mem v) ↔
      ¬ rmem (exTvRaw.choose e ε (v 0)) (exTvRaw.choose e ε (v 1)) :=
  exEvalRaw.choose_spec.2.2.2.2.2.1 req rmem e ε v

private lemma ev_and {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEvalRaw.choose req rmem e ε (Semiformula.and φ ψ) ↔
      exEvalRaw.choose req rmem e ε φ ∧ exEvalRaw.choose req rmem e ε ψ :=
  exEvalRaw.choose_spec.2.2.2.2.2.2.1 req rmem e ε φ ψ

private lemma ev_or {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEvalRaw.choose req rmem e ε (Semiformula.or φ ψ) ↔
      exEvalRaw.choose req rmem e ε φ ∨ exEvalRaw.choose req rmem e ε ψ :=
  exEvalRaw.choose_spec.2.2.2.2.2.2.2.1 req rmem e ε φ ψ

private lemma ev_all {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEvalRaw.choose req rmem e ε (Semiformula.all φ) ↔
      ∀ d : V, exEvalRaw.choose req rmem (d :> e) ε φ :=
  exEvalRaw.choose_spec.2.2.2.2.2.2.2.2.1 req rmem e ε φ

private lemma ev_exs {V : Type} (req rmem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEvalRaw.choose req rmem e ε (Semiformula.exs φ) ↔
      ∃ d : V, exEvalRaw.choose req rmem (d :> e) ε φ :=
  exEvalRaw.choose_spec.2.2.2.2.2.2.2.2.2 req rmem e ε φ

private lemma evalRaw_eq_sat {V : Type} (mem : V → V → Prop) :
    ∀ {m : ℕ} (φ : Semiformula ℒₛₑₜ Empty m) (e : Fin m → V),
      exEvalRaw.choose Eq mem e Empty.elim φ ↔
        let tv {k : ℕ} (e' : Fin k → V) : Semiterm ℒₛₑₜ Empty k → V :=
          @Semiterm.rec ℒₛₑₜ Empty k (fun _ => V) e' Empty.elim (fun {_} f _ _ => f.elim)
        @Semiformula.rec ℒₛₑₜ Empty (fun k _ => (Fin k → V) → Prop)
          (fun _ => True) (fun _ => False)
          (fun r v e' => @Language.Set.Rel.rec (fun k _ => (Fin k → Semiterm ℒₛₑₜ Empty _) → Prop)
            (fun w => tv e' (w 0) = tv e' (w 1)) (fun w => mem (tv e' (w 0)) (tv e' (w 1))) _ r v)
          (fun r v e' => ¬ @Language.Set.Rel.rec (fun k _ => (Fin k → Semiterm ℒₛₑₜ Empty _) → Prop)
            (fun w => tv e' (w 0) = tv e' (w 1)) (fun w => mem (tv e' (w 0)) (tv e' (w 1))) _ r v)
          (fun _ _ a b e' => a e' ∧ b e') (fun _ _ a b e' => a e' ∨ b e')
          (fun _ a e' => ∀ d, a (d :> e')) (fun _ a e' => ∃ d, a (d :> e')) m φ e := by
  have htv : ∀ {k : ℕ} (e' : Fin k → V) (t : Semiterm ℒₛₑₜ Empty k),
      exTvRaw.choose e' Empty.elim t =
        @Semiterm.rec ℒₛₑₜ Empty k (fun _ => V) e' Empty.elim (fun {_} f _ _ => f.elim) t := by
    intro k e' t
    cases t with
    | bvar i => exact tvRaw_bvar e' Empty.elim i
    | fvar x => exact x.elim
    | func f _ => exact f.elim
  intro m φ
  induction φ with
  | verum => intro e; exact ev_verum Eq mem e Empty.elim
  | falsum => intro e; exact ev_falsum Eq mem e Empty.elim
  | rel r v =>
    intro e
    cases r with
    | eq => simp only [ev_rel_eq, htv]
    | mem => simp only [ev_rel_mem, htv]
  | nrel r v =>
    intro e
    cases r with
    | eq => simp only [ev_nrel_eq, htv]
    | mem => simp only [ev_nrel_mem, htv]
  | and φ ψ ih1 ih2 =>
    intro e
    exact (ev_and Eq mem e Empty.elim φ ψ).trans (and_congr (ih1 e) (ih2 e))
  | or φ ψ ih1 ih2 =>
    intro e
    exact (ev_or Eq mem e Empty.elim φ ψ).trans (or_congr (ih1 e) (ih2 e))
  | all φ ih =>
    intro e
    exact (ev_all Eq mem e Empty.elim φ).trans (forall_congr' fun d => ih (d :> e))
  | exs φ ih =>
    intro e
    exact (ev_exs Eq mem e Empty.elim φ).trans (exists_congr fun d => ih (d :> e))

private lemma evalRaw_neg {V : Type} (req rmem : V → V → Prop) {ξ : Type} :
    ∀ {n : ℕ} (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ n),
      exEvalRaw.choose req rmem e ε (∼φ) ↔ ¬ exEvalRaw.choose req rmem e ε φ
  | _, e, ε, Semiformula.verum => by
      change exEvalRaw.choose req rmem e ε Semiformula.falsum ↔ _
      rw [ev_falsum, ev_verum]; simp
  | _, e, ε, Semiformula.falsum => by
      change exEvalRaw.choose req rmem e ε Semiformula.verum ↔ _
      rw [ev_verum, ev_falsum]; simp
  | _, e, ε, Semiformula.rel Language.Set.Rel.eq v => by
      change exEvalRaw.choose req rmem e ε (Semiformula.nrel Language.Set.Rel.eq v) ↔ _
      rw [ev_nrel_eq, ev_rel_eq]
  | _, e, ε, Semiformula.rel Language.Set.Rel.mem v => by
      change exEvalRaw.choose req rmem e ε (Semiformula.nrel Language.Set.Rel.mem v) ↔ _
      rw [ev_nrel_mem, ev_rel_mem]
  | _, e, ε, Semiformula.nrel Language.Set.Rel.eq v => by
      change exEvalRaw.choose req rmem e ε (Semiformula.rel Language.Set.Rel.eq v) ↔ _
      rw [ev_rel_eq, ev_nrel_eq]; exact not_not.symm
  | _, e, ε, Semiformula.nrel Language.Set.Rel.mem v => by
      change exEvalRaw.choose req rmem e ε (Semiformula.rel Language.Set.Rel.mem v) ↔ _
      rw [ev_rel_mem, ev_nrel_mem]; exact not_not.symm
  | _, e, ε, Semiformula.and φ ψ => by
      change exEvalRaw.choose req rmem e ε (Semiformula.or (∼φ) (∼ψ)) ↔ _
      rw [ev_or, ev_and, evalRaw_neg req rmem e ε φ, evalRaw_neg req rmem e ε ψ, not_and_or]
  | _, e, ε, Semiformula.or φ ψ => by
      change exEvalRaw.choose req rmem e ε (Semiformula.and (∼φ) (∼ψ)) ↔ _
      rw [ev_and, ev_or, evalRaw_neg req rmem e ε φ, evalRaw_neg req rmem e ε ψ, not_or]
  | _, e, ε, Semiformula.all φ => by
      change exEvalRaw.choose req rmem e ε (Semiformula.exs (∼φ)) ↔ _
      rw [ev_exs, ev_all]
      simp_rw [evalRaw_neg req rmem _ ε φ]
      exact not_forall.symm
  | _, e, ε, Semiformula.exs φ => by
      change exEvalRaw.choose req rmem e ε (Semiformula.all (∼φ)) ↔ _
      rw [ev_all, ev_exs]
      simp_rw [evalRaw_neg req rmem _ ε φ]
      exact not_exists.symm

private lemma tvRaw_rew {V : Type} {ξ₁ ξ₂ : Type} {n₁ n₂ : ℕ}
    (e : Fin n₂ → V) (ε : ξ₂ → V) (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (t : Semiterm ℒₛₑₜ ξ₁ n₁) :
    exTvRaw.choose e ε (ω t) =
      exTvRaw.choose (fun i => exTvRaw.choose e ε (ω #i)) (fun x => exTvRaw.choose e ε (ω &x)) t := by
  cases t with
  | bvar i => rw [tvRaw_bvar]
  | fvar x => rw [tvRaw_fvar]
  | func f _ => exact (f : Empty).elim

private lemma tvRaw_bShift {V : Type} {ξ : Type} {n : ℕ} (d : V) (e : Fin n → V) (ε : ξ → V)
    (t : Semiterm ℒₛₑₜ ξ n) :
    exTvRaw.choose (d :> e) ε (Rew.bShift t) = exTvRaw.choose e ε t := by
  cases t with
  | bvar i => exact (tvRaw_bvar (d :> e) ε i.succ).trans (tvRaw_bvar e ε i).symm
  | fvar x => exact (tvRaw_fvar (d :> e) ε x).trans (tvRaw_fvar e ε x).symm
  | func f _ => exact (f : Empty).elim

private lemma evalRaw_congr {V : Type} (req rmem : V → V → Prop) {ξ : Type} :
    ∀ {n : ℕ} {e₁ e₂ : Fin n → V} {ε₁ ε₂ : ξ → V} (φ : Semiformula ℒₛₑₜ ξ n),
      e₁ = e₂ → ε₁ = ε₂ →
      (exEvalRaw.choose req rmem e₁ ε₁ φ ↔ exEvalRaw.choose req rmem e₂ ε₂ φ) := by
  intro n e₁ e₂ ε₁ ε₂ φ he hε
  subst he hε; rfl

private lemma evalRaw_rew {V : Type} (req rmem : V → V → Prop) {ξ₁ ξ₂ : Type} :
    ∀ {n₁ n₂ : ℕ} (e : Fin n₂ → V) (ε : ξ₂ → V) (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
      (φ : Semiformula ℒₛₑₜ ξ₁ n₁),
      exEvalRaw.choose req rmem e ε (ω ▹ φ) ↔
        exEvalRaw.choose req rmem (fun i => exTvRaw.choose e ε (ω #i))
          (fun x => exTvRaw.choose e ε (ω &x)) φ
  | _, _, e, ε, _, Semiformula.verum => by
      change exEvalRaw.choose req rmem e ε Semiformula.verum ↔ _
      rw [ev_verum, ev_verum]
  | _, _, e, ε, _, Semiformula.falsum => by
      change exEvalRaw.choose req rmem e ε Semiformula.falsum ↔ _
      rw [ev_falsum, ev_falsum]
  | _, _, e, ε, ω, Semiformula.rel Language.Set.Rel.eq v => by
      change exEvalRaw.choose req rmem e ε (Semiformula.rel Language.Set.Rel.eq (ω ∘ v)) ↔ _
      rw [ev_rel_eq, ev_rel_eq, Function.comp_apply, Function.comp_apply,
        tvRaw_rew e ε ω (v 0), tvRaw_rew e ε ω (v 1)]
  | _, _, e, ε, ω, Semiformula.rel Language.Set.Rel.mem v => by
      change exEvalRaw.choose req rmem e ε (Semiformula.rel Language.Set.Rel.mem (ω ∘ v)) ↔ _
      rw [ev_rel_mem, ev_rel_mem, Function.comp_apply, Function.comp_apply,
        tvRaw_rew e ε ω (v 0), tvRaw_rew e ε ω (v 1)]
  | _, _, e, ε, ω, Semiformula.nrel Language.Set.Rel.eq v => by
      change exEvalRaw.choose req rmem e ε (Semiformula.nrel Language.Set.Rel.eq (ω ∘ v)) ↔ _
      rw [ev_nrel_eq, ev_nrel_eq, Function.comp_apply, Function.comp_apply,
        tvRaw_rew e ε ω (v 0), tvRaw_rew e ε ω (v 1)]
  | _, _, e, ε, ω, Semiformula.nrel Language.Set.Rel.mem v => by
      change exEvalRaw.choose req rmem e ε (Semiformula.nrel Language.Set.Rel.mem (ω ∘ v)) ↔ _
      rw [ev_nrel_mem, ev_nrel_mem, Function.comp_apply, Function.comp_apply,
        tvRaw_rew e ε ω (v 0), tvRaw_rew e ε ω (v 1)]
  | _, _, e, ε, ω, Semiformula.and φ ψ => by
      change exEvalRaw.choose req rmem e ε (Semiformula.and (ω ▹ φ) (ω ▹ ψ)) ↔ _
      rw [ev_and, ev_and]
      exact and_congr (evalRaw_rew req rmem e ε ω φ) (evalRaw_rew req rmem e ε ω ψ)
  | _, _, e, ε, ω, Semiformula.or φ ψ => by
      change exEvalRaw.choose req rmem e ε (Semiformula.or (ω ▹ φ) (ω ▹ ψ)) ↔ _
      rw [ev_or, ev_or]
      exact or_congr (evalRaw_rew req rmem e ε ω φ) (evalRaw_rew req rmem e ε ω ψ)
  | _, _, e, ε, ω, Semiformula.all φ => by
      change exEvalRaw.choose req rmem e ε (Semiformula.all (ω.q ▹ φ)) ↔ _
      rw [ev_all, ev_all]
      refine forall_congr' fun d => (evalRaw_rew req rmem (d :> e) ε ω.q φ).trans ?_
      refine evalRaw_congr req rmem φ ?_ ?_
      · funext i
        cases i using Fin.cases with
        | zero => exact tvRaw_bvar (d :> e) ε 0
        | succ i =>
          change exTvRaw.choose (d :> e) ε (Rew.bShift (ω #i)) = exTvRaw.choose e ε (ω #i)
          exact tvRaw_bShift d e ε _
      · funext x
        change exTvRaw.choose (d :> e) ε (Rew.bShift (ω &x)) = exTvRaw.choose e ε (ω &x)
        exact tvRaw_bShift d e ε _
  | _, _, e, ε, ω, Semiformula.exs φ => by
      change exEvalRaw.choose req rmem e ε (Semiformula.exs (ω.q ▹ φ)) ↔ _
      rw [ev_exs, ev_exs]
      refine exists_congr fun d => (evalRaw_rew req rmem (d :> e) ε ω.q φ).trans ?_
      refine evalRaw_congr req rmem φ ?_ ?_
      · funext i
        cases i using Fin.cases with
        | zero => exact tvRaw_bvar (d :> e) ε 0
        | succ i =>
          change exTvRaw.choose (d :> e) ε (Rew.bShift (ω #i)) = exTvRaw.choose e ε (ω #i)
          exact tvRaw_bShift d e ε _
      · funext x
        change exTvRaw.choose (d :> e) ε (Rew.bShift (ω &x)) = exTvRaw.choose e ε (ω &x)
        exact tvRaw_bShift d e ε _

/- ## 2. Basic syntactic properties of `Semiformula` and `Rew` -/

private lemma neg_neg_formula {ξ : Type*} : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n), ∼(∼φ) = φ
  | _, Semiformula.verum => rfl
  | _, Semiformula.falsum => rfl
  | _, Semiformula.rel _ _ => rfl
  | _, Semiformula.nrel _ _ => rfl
  | _, Semiformula.and φ ψ => by
      change Semiformula.and (∼(∼φ)) (∼(∼ψ)) = Semiformula.and φ ψ
      rw [neg_neg_formula φ, neg_neg_formula ψ]
  | _, Semiformula.or φ ψ => by
      change Semiformula.or (∼(∼φ)) (∼(∼ψ)) = Semiformula.or φ ψ
      rw [neg_neg_formula φ, neg_neg_formula ψ]
  | _, Semiformula.all φ => by
      change Semiformula.all (∼(∼φ)) = Semiformula.all φ
      rw [neg_neg_formula φ]
  | _, Semiformula.exs φ => by
      change Semiformula.exs (∼(∼φ)) = Semiformula.exs φ
      rw [neg_neg_formula φ]

private lemma rew_ext {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} {ω₁ ω₂ : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂}
    (hb : ∀ i : Fin n₁, ω₁ #i = ω₂ #i) (hf : ∀ x : ξ₁, ω₁ &x = ω₂ &x) : ω₁ = ω₂ := by
  rcases ω₁ with ⟨f₁, _⟩
  rcases ω₂ with ⟨f₂, _⟩
  congr 1
  funext t
  cases t with
  | bvar i => exact hb i
  | fvar x => exact hf x
  | func f _ => exact (f : Empty).elim

private lemma rew_q_comp {ξ₁ ξ₂ ξ₃ : Type*} {n₁ n₂ n₃ : ℕ}
    (ω₂ : Rew ℒₛₑₜ ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) :
    (ω₂.comp ω₁).q = ω₂.q.comp ω₁.q := by
  apply rew_ext
  · intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change Rew.bShift (ω₂ (ω₁ #i)) = ω₂.q (Rew.bShift (ω₁ #i))
      cases ω₁ #i with
      | bvar j => rfl
      | fvar x => rfl
      | func f _ => exact (f : Empty).elim
  · intro x
    change Rew.bShift (ω₂ (ω₁ &x)) = ω₂.q (Rew.bShift (ω₁ &x))
    cases ω₁ &x with
    | bvar j => rfl
    | fvar y => rfl
    | func f _ => exact (f : Empty).elim

private lemma rew_comp {ξ₁ ξ₂ ξ₃ : Type*} :
    ∀ {n₁ n₂ n₃ : ℕ} (ω₂ : Rew ℒₛₑₜ ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
      (φ : Semiformula ℒₛₑₜ ξ₁ n₁),
      ω₂ ▹ (ω₁ ▹ φ) = (ω₂.comp ω₁) ▹ φ
  | _, _, _, _, _, Semiformula.verum => rfl
  | _, _, _, _, _, Semiformula.falsum => rfl
  | _, _, _, _, _, Semiformula.rel _ _ => rfl
  | _, _, _, _, _, Semiformula.nrel _ _ => rfl
  | _, _, _, ω₂, ω₁, Semiformula.and φ ψ => by
      change (ω₂ ▹ (ω₁ ▹ φ)) ⋏ (ω₂ ▹ (ω₁ ▹ ψ)) = _
      rw [rew_comp ω₂ ω₁ φ, rew_comp ω₂ ω₁ ψ]; rfl
  | _, _, _, ω₂, ω₁, Semiformula.or φ ψ => by
      change (ω₂ ▹ (ω₁ ▹ φ)) ⋎ (ω₂ ▹ (ω₁ ▹ ψ)) = _
      rw [rew_comp ω₂ ω₁ φ, rew_comp ω₂ ω₁ ψ]; rfl
  | _, _, _, ω₂, ω₁, Semiformula.all φ => by
      change ∀¹ (ω₂.q ▹ (ω₁.q ▹ φ)) = ∀¹ ((ω₂.comp ω₁).q ▹ φ)
      rw [rew_comp ω₂.q ω₁.q φ, rew_q_comp]
  | _, _, _, ω₂, ω₁, Semiformula.exs φ => by
      change ∃¹ (ω₂.q ▹ (ω₁.q ▹ φ)) = ∃¹ ((ω₂.comp ω₁).q ▹ φ)
      rw [rew_comp ω₂.q ω₁.q φ, rew_q_comp]

private lemma rew_id_q {ξ : Type*} (n : ℕ) :
    (Rew.id (L := ℒₛₑₜ) (ξ := ξ) (n := n)).q = Rew.id := by
  apply rew_ext
  · intro i; cases i using Fin.cases <;> rfl
  · intro x; rfl

private lemma rew_id_eq {ξ : Type*} : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n), Rew.id ▹ φ = φ
  | _, Semiformula.verum => rfl
  | _, Semiformula.falsum => rfl
  | _, Semiformula.rel _ _ => rfl
  | _, Semiformula.nrel _ _ => rfl
  | _, Semiformula.and φ ψ => by
      change (Rew.id ▹ φ) ⋏ (Rew.id ▹ ψ) = φ ⋏ ψ
      rw [rew_id_eq φ, rew_id_eq ψ]
  | _, Semiformula.or φ ψ => by
      change (Rew.id ▹ φ) ⋎ (Rew.id ▹ ψ) = φ ⋎ ψ
      rw [rew_id_eq φ, rew_id_eq ψ]
  | n, Semiformula.all φ => by
      change ∀¹ ((Rew.id (L := ℒₛₑₜ) (ξ := ξ) (n := n)).q ▹ φ) = ∀¹ φ
      rw [rew_id_q n, rew_id_eq φ]
  | n, Semiformula.exs φ => by
      change ∃¹ ((Rew.id (L := ℒₛₑₜ) (ξ := ξ) (n := n)).q ▹ φ) = ∃¹ φ
      rw [rew_id_q n, rew_id_eq φ]

private lemma rew_term_congr_fv {ξ₁ ξ₂ : Type*} [DecidableEq ξ₁] {n₁ n₂ : ℕ}
    {ω₁ ω₂ : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂} (t : Semiterm ℒₛₑₜ ξ₁ n₁)
    (hb : ∀ i : Fin n₁, ω₁ #i = ω₂ #i)
    (hf : ∀ x ∈ t.freeVariables, ω₁ &x = ω₂ &x) : ω₁ t = ω₂ t := by
  cases t with
  | bvar i => exact hb i
  | fvar x => exact hf x (by simp [Semiterm.freeVariables])
  | func f _ => exact (f : Empty).elim

private lemma rew_congr_fv {ξ₁ ξ₂ : Type*} [DecidableEq ξ₁] :
    ∀ {n₁ n₂ : ℕ} {ω₁ ω₂ : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂} (φ : Semiformula ℒₛₑₜ ξ₁ n₁),
      (∀ i : Fin n₁, ω₁ #i = ω₂ #i) →
      (∀ x ∈ φ.freeVariables, ω₁ &x = ω₂ &x) →
      ω₁ ▹ φ = ω₂ ▹ φ
  | _, _, _, _, Semiformula.verum, _, _ => rfl
  | _, _, _, _, Semiformula.falsum, _, _ => rfl
  | _, _, _, _, Semiformula.rel r v, hb, hf => by
      change Semiformula.rel r _ = Semiformula.rel r _
      congr 1; funext j
      exact rew_term_congr_fv (v j) hb fun x hx =>
        hf x (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hx⟩)
  | _, _, _, _, Semiformula.nrel r v, hb, hf => by
      change Semiformula.nrel r _ = Semiformula.nrel r _
      congr 1; funext j
      exact rew_term_congr_fv (v j) hb fun x hx =>
        hf x (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hx⟩)
  | _, _, _, _, Semiformula.and φ ψ, hb, hf => by
      change (_ ▹ φ) ⋏ (_ ▹ ψ) = (_ ▹ φ) ⋏ (_ ▹ ψ)
      rw [rew_congr_fv φ hb (fun x hx => hf x (Finset.mem_union_left _ hx)),
          rew_congr_fv ψ hb (fun x hx => hf x (Finset.mem_union_right _ hx))]
  | _, _, _, _, Semiformula.or φ ψ, hb, hf => by
      change (_ ▹ φ) ⋎ (_ ▹ ψ) = (_ ▹ φ) ⋎ (_ ▹ ψ)
      rw [rew_congr_fv φ hb (fun x hx => hf x (Finset.mem_union_left _ hx)),
          rew_congr_fv ψ hb (fun x hx => hf x (Finset.mem_union_right _ hx))]
  | _, _, ω₁, ω₂, Semiformula.all φ, hb, hf => by
      change ∀¹ (ω₁.q ▹ φ) = ∀¹ (ω₂.q ▹ φ)
      congr 1
      refine rew_congr_fv φ ?_ ?_
      · intro i
        cases i using Fin.cases with
        | zero => rfl
        | succ i => change Rew.bShift (ω₁ #i) = Rew.bShift (ω₂ #i); rw [hb i]
      · intro x hx
        change Rew.bShift (ω₁ &x) = Rew.bShift (ω₂ &x); rw [hf x hx]
  | _, _, ω₁, ω₂, Semiformula.exs φ, hb, hf => by
      change ∃¹ (ω₁.q ▹ φ) = ∃¹ (ω₂.q ▹ φ)
      congr 1
      refine rew_congr_fv φ ?_ ?_
      · intro i
        cases i using Fin.cases with
        | zero => rfl
        | succ i => change Rew.bShift (ω₁ #i) = Rew.bShift (ω₂ #i); rw [hb i]
      · intro x hx
        change Rew.bShift (ω₁ &x) = Rew.bShift (ω₂ &x); rw [hf x hx]



private lemma exComp : ∃ c : ∀ {ξ : Type} {n : ℕ}, Semiformula ℒₛₑₜ ξ n → ℕ,
    (∀ {ξ : Type} {n : ℕ}, c (Semiformula.verum : Semiformula ℒₛₑₜ ξ n) = 0) ∧
    (∀ {ξ : Type} {n : ℕ}, c (Semiformula.falsum : Semiformula ℒₛₑₜ ξ n) = 0) ∧
    (∀ {ξ : Type} {n k : ℕ} (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ξ n),
      c (Semiformula.rel r v) = 0) ∧
    (∀ {ξ : Type} {n k : ℕ} (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ξ n),
      c (Semiformula.nrel r v) = 0) ∧
    (∀ {ξ : Type} {n : ℕ} (φ ψ : Semiformula ℒₛₑₜ ξ n),
      c (Semiformula.and φ ψ) = c φ + c ψ + 1) ∧
    (∀ {ξ : Type} {n : ℕ} (φ ψ : Semiformula ℒₛₑₜ ξ n),
      c (Semiformula.or φ ψ) = c φ + c ψ + 1) ∧
    (∀ {ξ : Type} {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ (n + 1)),
      c (Semiformula.all φ) = c φ + 1) ∧
    (∀ {ξ : Type} {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ (n + 1)),
      c (Semiformula.exs φ) = c φ + 1) :=
  ⟨fun {ξ} {n} φ => @Semiformula.rec ℒₛₑₜ ξ (fun _ _ => ℕ)
      0 0 (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ a b => a + b + 1) (fun _ _ a b => a + b + 1)
      (fun _ a => a + 1) (fun _ a => a + 1) n φ,
    rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ => rfl⟩

private lemma comp_verum {ξ : Type} {n : ℕ} :
    exComp.choose (Semiformula.verum : Semiformula ℒₛₑₜ ξ n) = 0 := exComp.choose_spec.1
private lemma comp_falsum {ξ : Type} {n : ℕ} :
    exComp.choose (Semiformula.falsum : Semiformula ℒₛₑₜ ξ n) = 0 := exComp.choose_spec.2.1
private lemma comp_rel {ξ : Type} {n k : ℕ} (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ξ n) :
    exComp.choose (Semiformula.rel r v) = 0 := exComp.choose_spec.2.2.1 r v
private lemma comp_nrel {ξ : Type} {n k : ℕ} (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ξ n) :
    exComp.choose (Semiformula.nrel r v) = 0 := exComp.choose_spec.2.2.2.1 r v
private lemma comp_and {ξ : Type} {n : ℕ} (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exComp.choose (Semiformula.and φ ψ) = exComp.choose φ + exComp.choose ψ + 1 :=
  exComp.choose_spec.2.2.2.2.1 φ ψ
private lemma comp_or {ξ : Type} {n : ℕ} (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exComp.choose (Semiformula.or φ ψ) = exComp.choose φ + exComp.choose ψ + 1 :=
  exComp.choose_spec.2.2.2.2.2.1 φ ψ
private lemma comp_all {ξ : Type} {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exComp.choose (Semiformula.all φ) = exComp.choose φ + 1 :=
  exComp.choose_spec.2.2.2.2.2.2.1 φ
private lemma comp_exs {ξ : Type} {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exComp.choose (Semiformula.exs φ) = exComp.choose φ + 1 :=
  exComp.choose_spec.2.2.2.2.2.2.2 φ

private lemma complexity_neg {ξ : Type} : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n),
    exComp.choose (∼φ) = exComp.choose φ
  | _, Semiformula.verum => by
      change exComp.choose (Semiformula.falsum : Semiformula ℒₛₑₜ ξ _) = _
      rw [comp_falsum, comp_verum]
  | _, Semiformula.falsum => by
      change exComp.choose (Semiformula.verum : Semiformula ℒₛₑₜ ξ _) = _
      rw [comp_verum, comp_falsum]
  | _, Semiformula.rel r v => by
      change exComp.choose (Semiformula.nrel r v) = _
      rw [comp_nrel, comp_rel]
  | _, Semiformula.nrel r v => by
      change exComp.choose (Semiformula.rel r v) = _
      rw [comp_rel, comp_nrel]
  | _, Semiformula.and φ ψ => by
      change exComp.choose (Semiformula.or (∼φ) (∼ψ)) = _
      rw [comp_or, comp_and, complexity_neg φ, complexity_neg ψ]
  | _, Semiformula.or φ ψ => by
      change exComp.choose (Semiformula.and (∼φ) (∼ψ)) = _
      rw [comp_and, comp_or, complexity_neg φ, complexity_neg ψ]
  | _, Semiformula.all φ => by
      change exComp.choose (Semiformula.exs (∼φ)) = _
      rw [comp_exs, comp_all, complexity_neg φ]
  | _, Semiformula.exs φ => by
      change exComp.choose (Semiformula.all (∼φ)) = _
      rw [comp_all, comp_exs, complexity_neg φ]

private lemma complexity_rew {ξ₁ ξ₂ : Type} :
    ∀ {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (φ : Semiformula ℒₛₑₜ ξ₁ n₁),
      exComp.choose (ω ▹ φ) = exComp.choose φ
  | _, _, _, Semiformula.verum => by
      change exComp.choose (Semiformula.verum : Semiformula ℒₛₑₜ ξ₂ _) = _
      rw [comp_verum, comp_verum]
  | _, _, _, Semiformula.falsum => by
      change exComp.choose (Semiformula.falsum : Semiformula ℒₛₑₜ ξ₂ _) = _
      rw [comp_falsum, comp_falsum]
  | _, _, ω, Semiformula.rel r v => by
      change exComp.choose (Semiformula.rel r (ω ∘ v)) = _
      rw [comp_rel, comp_rel]
  | _, _, ω, Semiformula.nrel r v => by
      change exComp.choose (Semiformula.nrel r (ω ∘ v)) = _
      rw [comp_nrel, comp_nrel]
  | _, _, ω, Semiformula.and φ ψ => by
      change exComp.choose (Semiformula.and (ω ▹ φ) (ω ▹ ψ)) = _
      rw [comp_and, comp_and, complexity_rew ω φ, complexity_rew ω ψ]
  | _, _, ω, Semiformula.or φ ψ => by
      change exComp.choose (Semiformula.or (ω ▹ φ) (ω ▹ ψ)) = _
      rw [comp_or, comp_or, complexity_rew ω φ, complexity_rew ω ψ]
  | _, _, ω, Semiformula.all φ => by
      change exComp.choose (Semiformula.all (ω.q ▹ φ)) = _
      rw [comp_all, comp_all, complexity_rew ω.q φ]
  | _, _, ω, Semiformula.exs φ => by
      change exComp.choose (Semiformula.exs (ω.q ▹ φ)) = _
      rw [comp_exs, comp_exs, complexity_rew ω.q φ]

private lemma fv_lt_fvSup {n : ℕ} (φ : Semiproposition ℒₛₑₜ n) {x : ℕ} (hx : x ∈ φ.freeVariables) :
    x < φ.fvSup := by
  unfold Semiformula.fvSup
  have hne : φ.freeVariables.Nonempty := ⟨x, hx⟩
  obtain ⟨m, hm⟩ := Finset.max_of_nonempty hne
  rw [hm]
  exact Nat.lt_succ_of_le (Finset.le_max_of_eq hx hm)

private lemma rew_emb_q (m : ℕ) :
    (Rew.emb (L := ℒₛₑₜ) (o := Empty) (ξ := ℕ) (n := m)).q = Rew.emb := by
  apply rew_ext
  · intro i; cases i using Fin.cases <;> rfl
  · intro x; exact x.elim

private lemma freeVariables_emb {n : ℕ} (φ : Semisentence ℒₛₑₜ n) :
    (Rewriting.emb φ : Semiproposition ℒₛₑₜ n).freeVariables = ∅ := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r v =>
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    cases hvi : v i with
    | bvar j =>
      simp only [Function.comp_apply, hvi] at hi
      exact Finset.notMem_empty x hi
    | fvar y => exact y.elim
    | func f _ => exact (f : Empty).elim
  | nrel r v =>
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    cases hvi : v i with
    | bvar j =>
      simp only [Function.comp_apply, hvi] at hi
      exact Finset.notMem_empty x hi
    | fvar y => exact y.elim
    | func f _ => exact (f : Empty).elim
  | and φ ψ ih1 ih2 =>
    change (Rewriting.emb φ).freeVariables ∪ (Rewriting.emb ψ).freeVariables = ∅
    rw [ih1, ih2]; rfl
  | or φ ψ ih1 ih2 =>
    change (Rewriting.emb φ).freeVariables ∪ (Rewriting.emb ψ).freeVariables = ∅
    rw [ih1, ih2]; rfl
  | @all m φ ih =>
    change ((Rew.emb (L := ℒₛₑₜ) (o := Empty) (ξ := ℕ) (n := m)).q ▹ φ).freeVariables = ∅
    rw [rew_emb_q m]; exact ih
  | @exs m φ ih =>
    change ((Rew.emb (L := ℒₛₑₜ) (o := Empty) (ξ := ℕ) (n := m)).q ▹ φ).freeVariables = ∅
    rw [rew_emb_q m]; exact ih

private lemma freeVariables_neg {n : ℕ} (φ : Semiproposition ℒₛₑₜ n) :
    (∼φ).freeVariables = φ.freeVariables := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel _ _ => rfl
  | nrel _ _ => rfl
  | and φ ψ ih1 ih2 =>
    change (∼φ).freeVariables ∪ (∼ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables
    rw [ih1, ih2]
  | or φ ψ ih1 ih2 =>
    change (∼φ).freeVariables ∪ (∼ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables
    rw [ih1, ih2]
  | all φ ih => exact ih
  | exs φ ih => exact ih

private lemma neg_map {α : Type*} [Tilde α] (A : Multiset α) : ∼A = A.map (∼·) := rfl
private lemma atom_eq {α : Type*} (a : α) : ⦃a⦄ = {a} := rfl
private lemma neg_exs (ψ : Semiproposition ℒₛₑₜ 1) : ∼(∃¹ ψ) = ∀¹ (∼ψ) := rfl
private lemma neg_all (ψ : Semiproposition ℒₛₑₜ 1) : ∼(∀¹ ψ) = ∃¹ (∼ψ) := rfl
private lemma neg_and (φ ψ : Proposition ℒₛₑₜ) : ∼(φ ⋏ ψ) = ∼φ ⋎ ∼ψ := rfl
private lemma neg_or (φ ψ : Proposition ℒₛₑₜ) : ∼(φ ⋎ ψ) = ∼φ ⋏ ∼ψ := rfl



/- ## 3. Derivation constructors: renaming, fresh universal generalization, excluded middle -/

private lemma fvarMap_q (f : ℕ → ℕ) (n : ℕ) :
    (Rew.map id f : SyntacticRew ℒₛₑₜ n n).q = (Rew.map id f : SyntacticRew ℒₛₑₜ (n + 1) (n + 1)) := by
  apply rew_ext
  · intro i; cases i using Fin.cases <;> rfl
  · intro x; rfl

private lemma deriv_fvarMap (f : ℕ → ℕ) {Γ : Sequent ℒₛₑₜ} (d : Derivation Γ) :
    Nonempty (Derivation (Γ.map ((Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) ▹ ·))) := by
  induction d generalizing f with
  | identity r v =>
    have heq : (⦃Semiformula.rel r v, Semiformula.nrel r v⦄ : Sequent ℒₛₑₜ).map
        ((Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) ▹ ·) =
        ⦃Semiformula.rel r ((Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) ∘ v),
         Semiformula.nrel r ((Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) ∘ v)⦄ := by
      simp [atom_eq]; rfl
    rw [heq]
    exact ⟨Derivation.identity r ((Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) ∘ v)⟩
  | @cut Γ φ Δ _ _ ih1 ih2 =>
    obtain ⟨h1⟩ := ih1 f
    obtain ⟨h2⟩ := ih2 f
    simp only [Multiset.map_add, atom_eq, Multiset.map_singleton] at h1 h2 ⊢
    have hneg : (Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) ▹ (∼φ) =
        ∼((Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) ▹ φ) :=
      (Semiformula.rew (Rew.map id f : SyntacticRew ℒₛₑₜ 0 0)).map_neg' φ
    rw [hneg] at h2
    exact ⟨Derivation.cut h1 h2⟩
  | contraction _ hsub ih =>
    obtain ⟨h⟩ := ih f
    exact ⟨Derivation.contraction h (Multiset.map_subset_map hsub)⟩
  | verum =>
    have heq : (⦃⊤⦄ : Sequent ℒₛₑₜ).map ((Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) ▹ ·) = ⦃⊤⦄ := by
      simp [atom_eq]; rfl
    rw [heq]
    exact ⟨Derivation.verum⟩
  | or _ ih =>
    obtain ⟨h⟩ := ih f
    simp only [Multiset.map_add, atom_eq, Multiset.map_singleton] at h ⊢
    exact ⟨Derivation.or h⟩
  | and _ _ ih1 ih2 =>
    obtain ⟨h1⟩ := ih1 f
    obtain ⟨h2⟩ := ih2 f
    simp only [Multiset.map_add, atom_eq, Multiset.map_singleton] at h1 h2 ⊢
    exact ⟨Derivation.and h1 h2⟩
  | @all Γ φ _ ih =>
    let f' : ℕ → ℕ := Nat.cases 0 (fun k => f k + 1)
    obtain ⟨h⟩ := ih f'
    simp only [Multiset.map_add, atom_eq, Multiset.map_singleton] at h ⊢
    have hshift : Γ⁺.map ((Rew.map id f' : SyntacticRew ℒₛₑₜ 0 0) ▹ ·) =
        Rewriting.shifts (Γ.map ((Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) ▹ ·)) := by
      simp only [Rewriting.shifts, Multiset.map_map]
      congr 1; funext ψ
      change (Rew.map id f' : SyntacticRew ℒₛₑₜ 0 0) ▹ (Rew.shift ▹ ψ) =
        Rew.shift ▹ ((Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) ▹ ψ)
      rw [rew_comp, rew_comp]
      exact congrArg (fun ω : SyntacticRew ℒₛₑₜ 0 0 => ω ▹ ψ)
        (rew_ext (fun i => Fin.elim0 i) (fun _ => rfl))
    have hfree : (Rew.map id f' : SyntacticRew ℒₛₑₜ 0 0) ▹ φ.free =
        ((Rew.map id f : SyntacticRew ℒₛₑₜ 1 1) ▹ φ).free := by
      change (Rew.map id f' : SyntacticRew ℒₛₑₜ 0 0) ▹ (Rew.free ▹ φ) =
        Rew.free ▹ ((Rew.map id f : SyntacticRew ℒₛₑₜ 1 1) ▹ φ)
      rw [rew_comp, rew_comp]
      exact congrArg (fun ω : SyntacticRew ℒₛₑₜ 1 0 => ω ▹ φ) (rew_ext (fun i => by
        have hi : i = 0 := Fin.ext (by omega); subst hi; rfl) (fun _ => rfl))
    rw [hshift, hfree] at h
    have hall : (Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) ▹ (∀¹ φ) =
        ∀¹ ((Rew.map id f : SyntacticRew ℒₛₑₜ 1 1) ▹ φ) := by
      change ∀¹ ((Rew.map id f : SyntacticRew ℒₛₑₜ 0 0).q ▹ φ) = _
      rw [fvarMap_q]
    rw [hall]
    exact ⟨Derivation.all h⟩
  | @exs Γ φ t _ ih =>
    obtain ⟨h⟩ := ih f
    simp only [Multiset.map_add, atom_eq, Multiset.map_singleton] at h ⊢
    have hsubst : (Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) ▹ (φ/[t]) =
        ((Rew.map id f : SyntacticRew ℒₛₑₜ 1 1) ▹ φ)/[(Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) t] := by
      change (Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) ▹ (Rew.subst ![t] ▹ φ) =
        Rew.subst ![(Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) t] ▹
          ((Rew.map id f : SyntacticRew ℒₛₑₜ 1 1) ▹ φ)
      rw [rew_comp, rew_comp]
      exact congrArg (fun ω : SyntacticRew ℒₛₑₜ 1 0 => ω ▹ φ) (rew_ext (fun i => by
        have hi : i = 0 := Subsingleton.elim i 0; subst hi; rfl) (fun _ => rfl))
    rw [hsubst] at h
    have hexs : (Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) ▹ (∃¹ φ) =
        ∃¹ ((Rew.map id f : SyntacticRew ℒₛₑₜ 1 1) ▹ φ) := by
      change ∃¹ ((Rew.map id f : SyntacticRew ℒₛₑₜ 0 0).q ▹ φ) = _
      rw [fvarMap_q]
    rw [hexs]
    exact ⟨Derivation.exs h⟩

private lemma deriv_all_of_fresh {Γ : Sequent ℒₛₑₜ} {φ : Semiproposition ℒₛₑₜ 1} {c : ℕ}
    (hΓ : ∀ ψ ∈ Γ, c ∉ ψ.freeVariables) (hφ : c ∉ φ.freeVariables)
    (d : Derivation (Γ + ⦃φ/[&c]⦄)) : Nonempty (Derivation (Γ + ⦃∀¹ φ⦄)) := by
  let f : ℕ → ℕ := fun k => if k = c then 0 else k + 1
  obtain ⟨hd⟩ := deriv_fvarMap f d
  simp only [Multiset.map_add, atom_eq, Multiset.map_singleton] at hd
  have hΓ' : Γ.map ((Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) ▹ ·) = Γ⁺ := by
    unfold Rewriting.shifts
    apply Multiset.map_congr rfl
    intro ψ hψ
    refine rew_congr_fv ψ (fun i => Fin.elim0 i) ?_
    intro x hx
    have hxc : x ≠ c := fun h => hΓ ψ hψ (h ▸ hx)
    change &(if x = c then 0 else x + 1) = &(x + 1)
    rw [if_neg hxc]
  have hφ' : (Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) ▹ (φ/[&c]) = φ.free := by
    change (Rew.map id f : SyntacticRew ℒₛₑₜ 0 0) ▹ (Rew.subst ![&c] ▹ φ) = Rew.free ▹ φ
    rw [rew_comp]
    refine rew_congr_fv φ ?_ ?_
    · intro i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      change &(if c = c then 0 else c + 1) = &0
      rw [if_pos rfl]
    · intro x hx
      have hxc : x ≠ c := fun h => hφ (h ▸ hx)
      change &(if x = c then 0 else x + 1) = &(x + 1)
      rw [if_neg hxc]
  rw [hΓ', hφ'] at hd
  exact ⟨Derivation.all hd⟩

private lemma deriv_em : ∀ (φ : Proposition ℒₛₑₜ), Nonempty (Derivation ⦃∼φ, φ⦄) := by
  intro φ
  suffices h : ∀ k : ℕ, ∀ φ : Proposition ℒₛₑₜ, exComp.choose φ ≤ k → Nonempty (Derivation ⦃∼φ, φ⦄) from
    h (exComp.choose φ) φ le_rfl
  intro k
  induction k with
  | zero =>
    intro φ hk
    cases φ with
    | verum =>
      exact ⟨Derivation.contraction Derivation.verum (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        exact Or.inr hx)⟩
    | falsum =>
      exact ⟨Derivation.contraction Derivation.verum (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        exact Or.inl hx)⟩
    | rel r v =>
      exact ⟨Derivation.contraction (Derivation.identity r v) (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl rfl)⟩
    | nrel r v =>
      exact ⟨Derivation.identity r v⟩
    | and φ₁ φ₂ => rw [comp_and] at hk; omega
    | or φ₁ φ₂ => rw [comp_or] at hk; omega
    | all φ₁ => rw [comp_all] at hk; omega
    | exs φ₁ => rw [comp_exs] at hk; omega
  | succ k ih =>
    intro φ hk
    cases φ with
    | verum =>
      exact ⟨Derivation.contraction Derivation.verum (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        exact Or.inr hx)⟩
    | falsum =>
      exact ⟨Derivation.contraction Derivation.verum (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        exact Or.inl hx)⟩
    | rel r v =>
      exact ⟨Derivation.contraction (Derivation.identity r v) (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl rfl)⟩
    | nrel r v => exact ⟨Derivation.identity r v⟩
    | and ψ₁ ψ₂ =>
      rw [comp_and] at hk
      obtain ⟨ih1⟩ := ih ψ₁ (by omega)
      obtain ⟨ih2⟩ := ih ψ₂ (by omega)
      have d1 : Derivation (⦃∼ψ₁, ∼ψ₂⦄ + ⦃ψ₁⦄) :=
        Derivation.contraction ih1 (by
          intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr rfl)
      have d2 : Derivation (⦃∼ψ₁, ∼ψ₂⦄ + ⦃ψ₂⦄) :=
        Derivation.contraction ih2 (by
          intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr rfl)
      have dand : Derivation (⦃ψ₁ ⋏ ψ₂⦄ + ⦃∼ψ₁, ∼ψ₂⦄) :=
        Derivation.contraction (Derivation.and d1 d2) (by
          intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          rcases hx with (rfl | rfl) | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact Or.inl rfl)
      have dor := Derivation.or dand
      exact ⟨Derivation.contraction dor (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl rfl)⟩
    | or ψ₁ ψ₂ =>
      rw [comp_or] at hk
      obtain ⟨ih1⟩ := ih ψ₁ (by omega)
      obtain ⟨ih2⟩ := ih ψ₂ (by omega)
      have d1 : Derivation (⦃ψ₁, ψ₂⦄ + ⦃∼ψ₁⦄) :=
        Derivation.contraction ih1 (by
          intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl (Or.inl rfl))
      have d2 : Derivation (⦃ψ₁, ψ₂⦄ + ⦃∼ψ₂⦄) :=
        Derivation.contraction ih2 (by
          intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl (Or.inr rfl))
      have dand : Derivation (⦃∼ψ₁ ⋏ ∼ψ₂⦄ + ⦃ψ₁, ψ₂⦄) :=
        Derivation.contraction (Derivation.and d1 d2) (by
          intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          rcases hx with (rfl | rfl) | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact Or.inl rfl)
      exact ⟨Derivation.or dand⟩
    | all ψ =>
      rw [comp_all] at hk
      have hcomp : exComp.choose ψ.free ≤ k := by
        change exComp.choose (Rew.free ▹ ψ) ≤ k
        rw [complexity_rew]; omega
      obtain ⟨d0⟩ := ih ψ.free hcomp
      have hshift_subst : (Rew.shift.q ▹ (∼ψ))/[&0] = ∼ψ.free := by
        have h1 : ∼ψ.free = (∼ψ).free := ((Semiformula.rew Rew.free).map_neg' ψ).symm
        rw [h1]
        change Rew.subst ![&0] ▹ (Rew.shift.q ▹ (∼ψ)) = Rew.free ▹ (∼ψ)
        rw [rew_comp]
        exact congrArg (fun ω : SyntacticRew ℒₛₑₜ 1 0 => ω ▹ (∼ψ)) (rew_ext (fun i => by
          have hi : i = 0 := Fin.ext (by omega); subst hi; rfl) (fun _ => rfl))
      have d1 : Derivation (⦃ψ.free⦄ + ⦃(Rew.shift.q ▹ (∼ψ))/[&0]⦄) :=
        Derivation.contraction d0 (by
          rw [hshift_subst]
          intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl rfl)
      have d2 : Derivation (⦃ψ.free⦄ + ⦃∃¹ (Rew.shift.q ▹ (∼ψ))⦄) := Derivation.exs d1
      have hshift_eq : ⦃∃¹ (∼ψ)⦄⁺ = ⦃∃¹ (Rew.shift.q ▹ (∼ψ))⦄ := rfl
      have d3 : Derivation (⦃∃¹ (∼ψ)⦄⁺ + ⦃ψ.free⦄) :=
        Derivation.contraction d2 (by
          rw [hshift_eq]
          intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl rfl)
      exact ⟨Derivation.all d3⟩
    | exs ψ =>
      rw [comp_exs] at hk
      have hcomp : exComp.choose (∼ψ).free ≤ k := by
        change exComp.choose (Rew.free ▹ (∼ψ)) ≤ k
        rw [complexity_rew, complexity_neg]; omega
      obtain ⟨d0⟩ := ih (∼ψ).free hcomp
      have hneg_free : ∼(∼ψ).free = ψ.free := by
        have h1 : ∼(∼ψ).free = (∼(∼ψ)).free := ((Semiformula.rew Rew.free).map_neg' (∼ψ)).symm
        rw [h1, neg_neg_formula]
      have hshift_subst : (Rew.shift.q ▹ ψ)/[&0] = ψ.free := by
        change Rew.subst ![&0] ▹ (Rew.shift.q ▹ ψ) = Rew.free ▹ ψ
        rw [rew_comp]
        exact congrArg (fun ω : SyntacticRew ℒₛₑₜ 1 0 => ω ▹ ψ) (rew_ext (fun i => by
          have hi : i = 0 := Fin.ext (by omega); subst hi; rfl) (fun _ => rfl))
      have d1 : Derivation (⦃(∼ψ).free⦄ + ⦃(Rew.shift.q ▹ ψ)/[&0]⦄) :=
        Derivation.contraction d0 (by
          rw [hneg_free, hshift_subst]
          intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl rfl)
      have d2 : Derivation (⦃(∼ψ).free⦄ + ⦃∃¹ (Rew.shift.q ▹ ψ)⦄) := Derivation.exs d1
      have hshift_eq : ⦃∃¹ ψ⦄⁺ = ⦃∃¹ (Rew.shift.q ▹ ψ)⦄ := rfl
      have d3 : Derivation (⦃∃¹ ψ⦄⁺ + ⦃(∼ψ).free⦄) :=
        Derivation.contraction d2 (by
          rw [hshift_eq]
          intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl rfl)
      have d4 : Derivation (⦃∃¹ ψ⦄ + ⦃∀¹ (∼ψ)⦄) := Derivation.all d3
      exact ⟨Derivation.contraction d4 (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl rfl)⟩


/- ## 4. Countability of `Proposition ℒₛₑₜ` (zero top-level `def`s) -/

private lemma exists_enum_prop : ∃ enum : ℕ → Proposition ℒₛₑₜ, Function.Surjective enum := by
  let encodeTerm : ∀ {n : ℕ}, Semiterm ℒₛₑₜ ℕ n → ℕ
    | _, Semiterm.bvar i => Nat.pair 0 i.val
    | _, Semiterm.fvar x => Nat.pair 1 x
    | _, Semiterm.func f _ => (f : Empty).elim
  have encodeTerm_injective : ∀ {n : ℕ}, Function.Injective (encodeTerm (n := n)) := by
    intro n t₁ t₂ h
    cases t₁ with
    | func f _ => exact (f : Empty).elim
    | bvar i =>
      cases t₂ with
      | func f _ => exact (f : Empty).elim
      | bvar j =>
        have h1 := congrArg (fun k => (Nat.unpair k).2) h
        simp only [encodeTerm, Nat.unpair_pair] at h1
        exact congrArg Semiterm.bvar (Fin.ext h1)
      | fvar y =>
        have h1 := congrArg (fun k => (Nat.unpair k).1) h
        simp only [encodeTerm, Nat.unpair_pair] at h1
        omega
    | fvar x =>
      cases t₂ with
      | func f _ => exact (f : Empty).elim
      | bvar j =>
        have h1 := congrArg (fun k => (Nat.unpair k).1) h
        simp only [encodeTerm, Nat.unpair_pair] at h1
        omega
      | fvar y =>
        have h1 := congrArg (fun k => (Nat.unpair k).2) h
        simp only [encodeTerm, Nat.unpair_pair] at h1
        exact congrArg Semiterm.fvar h1
  let encodeFormula : ∀ {n : ℕ}, Semiformula ℒₛₑₜ ℕ n → ℕ := fun {n} φ =>
    @Semiformula.rec ℒₛₑₜ ℕ (fun _ _ => ℕ)
      (Nat.pair 0 0)
      (Nat.pair 1 0)
      (fun {m k} r v => @Language.Set.Rel.rec (fun k' _ => (Fin k' → Semiterm ℒₛₑₜ ℕ m) → ℕ)
        (fun w => Nat.pair 2 (Nat.pair (encodeTerm (w 0)) (encodeTerm (w 1))))
        (fun w => Nat.pair 3 (Nat.pair (encodeTerm (w 0)) (encodeTerm (w 1)))) k r v)
      (fun {m k} r v => @Language.Set.Rel.rec (fun k' _ => (Fin k' → Semiterm ℒₛₑₜ ℕ m) → ℕ)
        (fun w => Nat.pair 4 (Nat.pair (encodeTerm (w 0)) (encodeTerm (w 1))))
        (fun w => Nat.pair 5 (Nat.pair (encodeTerm (w 0)) (encodeTerm (w 1)))) k r v)
      (fun _ _ a b => Nat.pair 6 (Nat.pair a b))
      (fun _ _ a b => Nat.pair 7 (Nat.pair a b))
      (fun _ a => Nat.pair 8 a)
      (fun _ a => Nat.pair 9 a) n φ
  have vec2_eq_of_encode : ∀ {n : ℕ} {v₁ v₂ : Fin 2 → Semiterm ℒₛₑₜ ℕ n},
      Nat.pair (encodeTerm (v₁ 0)) (encodeTerm (v₁ 1)) =
        Nat.pair (encodeTerm (v₂ 0)) (encodeTerm (v₂ 1)) → v₁ = v₂ := by
    intro n v₁ v₂ h
    have h0 : encodeTerm (v₁ 0) = encodeTerm (v₂ 0) := by
      have := congrArg (fun k => (Nat.unpair k).1) h; simpa [Nat.unpair_pair] using this
    have h1 : encodeTerm (v₁ 1) = encodeTerm (v₂ 1) := by
      have := congrArg (fun k => (Nat.unpair k).2) h; simpa [Nat.unpair_pair] using this
    funext i; fin_cases i
    · exact encodeTerm_injective h0
    · exact encodeTerm_injective h1
  let formulaTag : ∀ {n : ℕ}, Semiformula ℒₛₑₜ ℕ n → ℕ
    | _, Semiformula.verum => 0
    | _, Semiformula.falsum => 1
    | _, Semiformula.rel Language.Set.Rel.eq _ => 2
    | _, Semiformula.rel Language.Set.Rel.mem _ => 3
    | _, Semiformula.nrel Language.Set.Rel.eq _ => 4
    | _, Semiformula.nrel Language.Set.Rel.mem _ => 5
    | _, Semiformula.and _ _ => 6
    | _, Semiformula.or _ _ => 7
    | _, Semiformula.all _ => 8
    | _, Semiformula.exs _ => 9
  have unpair_fst_encodeFormula : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n),
      (Nat.unpair (encodeFormula φ)).1 = formulaTag φ := by
    intro n φ
    cases φ with
    | verum => exact congrArg Prod.fst (Nat.unpair_pair 0 0)
    | falsum => exact congrArg Prod.fst (Nat.unpair_pair 1 0)
    | rel r _ => cases r <;> exact congrArg Prod.fst (Nat.unpair_pair _ _)
    | nrel r _ => cases r <;> exact congrArg Prod.fst (Nat.unpair_pair _ _)
    | and _ _ => exact congrArg Prod.fst (Nat.unpair_pair 6 _)
    | or _ _ => exact congrArg Prod.fst (Nat.unpair_pair 7 _)
    | all _ => exact congrArg Prod.fst (Nat.unpair_pair 8 _)
    | exs _ => exact congrArg Prod.fst (Nat.unpair_pair 9 _)
  have tag_eq : ∀ {n : ℕ} (φ₁ φ₂ : Semiformula ℒₛₑₜ ℕ n),
      encodeFormula φ₁ = encodeFormula φ₂ → formulaTag φ₁ = formulaTag φ₂ :=
    fun {_} φ₁ φ₂ h => (unpair_fst_encodeFormula φ₁).symm.trans
      ((congrArg (fun k => (Nat.unpair k).1) h).trans (unpair_fst_encodeFormula φ₂))
  have encodeFormula_injective : ∀ {n : ℕ}, Function.Injective (encodeFormula (n := n)) := by
    intro n φ₁ φ₂ h
    induction φ₁ with
    | verum =>
      have ht := tag_eq Semiformula.verum φ₂ h
      cases φ₂ with
      | verum => rfl
      | rel r _ => cases r <;> simp [formulaTag] at ht
      | nrel r _ => cases r <;> simp [formulaTag] at ht
      | _ => simp [formulaTag] at ht
    | falsum =>
      have ht := tag_eq Semiformula.falsum φ₂ h
      cases φ₂ with
      | falsum => rfl
      | rel r _ => cases r <;> simp [formulaTag] at ht
      | nrel r _ => cases r <;> simp [formulaTag] at ht
      | _ => simp [formulaTag] at ht
    | rel r₁ v₁ =>
      have ht := tag_eq (Semiformula.rel r₁ v₁) φ₂ h
      cases r₁ with
      | eq =>
        cases φ₂ with
        | rel r₂ v₂ =>
          cases r₂ with
          | eq =>
            have h2 := congrArg (fun k => (Nat.unpair k).2) h
            change (Nat.unpair (Nat.pair 2 (Nat.pair (encodeTerm (v₁ 0)) (encodeTerm (v₁ 1))))).2 =
              (Nat.unpair (Nat.pair 2 (Nat.pair (encodeTerm (v₂ 0)) (encodeTerm (v₂ 1))))).2 at h2
            rw [Nat.unpair_pair, Nat.unpair_pair] at h2
            rw [vec2_eq_of_encode h2]
          | mem => simp [formulaTag] at ht
        | nrel r₂ _ => cases r₂ <;> simp [formulaTag] at ht
        | _ => simp [formulaTag] at ht
      | mem =>
        cases φ₂ with
        | rel r₂ v₂ =>
          cases r₂ with
          | eq => simp [formulaTag] at ht
          | mem =>
            have h2 := congrArg (fun k => (Nat.unpair k).2) h
            change (Nat.unpair (Nat.pair 3 (Nat.pair (encodeTerm (v₁ 0)) (encodeTerm (v₁ 1))))).2 =
              (Nat.unpair (Nat.pair 3 (Nat.pair (encodeTerm (v₂ 0)) (encodeTerm (v₂ 1))))).2 at h2
            rw [Nat.unpair_pair, Nat.unpair_pair] at h2
            rw [vec2_eq_of_encode h2]
        | nrel r₂ _ => cases r₂ <;> simp [formulaTag] at ht
        | _ => simp [formulaTag] at ht
    | nrel r₁ v₁ =>
      have ht := tag_eq (Semiformula.nrel r₁ v₁) φ₂ h
      cases r₁ with
      | eq =>
        cases φ₂ with
        | nrel r₂ v₂ =>
          cases r₂ with
          | eq =>
            have h2 := congrArg (fun k => (Nat.unpair k).2) h
            change (Nat.unpair (Nat.pair 4 (Nat.pair (encodeTerm (v₁ 0)) (encodeTerm (v₁ 1))))).2 =
              (Nat.unpair (Nat.pair 4 (Nat.pair (encodeTerm (v₂ 0)) (encodeTerm (v₂ 1))))).2 at h2
            rw [Nat.unpair_pair, Nat.unpair_pair] at h2
            rw [vec2_eq_of_encode h2]
          | mem => simp [formulaTag] at ht
        | rel r₂ _ => cases r₂ <;> simp [formulaTag] at ht
        | _ => simp [formulaTag] at ht
      | mem =>
        cases φ₂ with
        | nrel r₂ v₂ =>
          cases r₂ with
          | eq => simp [formulaTag] at ht
          | mem =>
            have h2 := congrArg (fun k => (Nat.unpair k).2) h
            change (Nat.unpair (Nat.pair 5 (Nat.pair (encodeTerm (v₁ 0)) (encodeTerm (v₁ 1))))).2 =
              (Nat.unpair (Nat.pair 5 (Nat.pair (encodeTerm (v₂ 0)) (encodeTerm (v₂ 1))))).2 at h2
            rw [Nat.unpair_pair, Nat.unpair_pair] at h2
            rw [vec2_eq_of_encode h2]
        | rel r₂ _ => cases r₂ <;> simp [formulaTag] at ht
        | _ => simp [formulaTag] at ht
    | and φ₁ ψ₁ ih1 ih2 =>
      have ht := tag_eq (φ₁.and ψ₁) φ₂ h
      cases φ₂ with
      | and φ₂ ψ₂ =>
        have h2 := congrArg (fun k => (Nat.unpair k).2) h
        change (Nat.unpair (Nat.pair 6 (Nat.pair (encodeFormula φ₁) (encodeFormula ψ₁)))).2 =
          (Nat.unpair (Nat.pair 6 (Nat.pair (encodeFormula φ₂) (encodeFormula ψ₂)))).2 at h2
        rw [Nat.unpair_pair, Nat.unpair_pair] at h2
        have ha : encodeFormula φ₁ = encodeFormula φ₂ := by
          have := congrArg (fun k => (Nat.unpair k).1) h2; simpa [Nat.unpair_pair] using this
        have hb : encodeFormula ψ₁ = encodeFormula ψ₂ := by
          have := congrArg (fun k => (Nat.unpair k).2) h2; simpa [Nat.unpair_pair] using this
        rw [ih1 ha, ih2 hb]
      | rel r _ => cases r <;> simp [formulaTag] at ht
      | nrel r _ => cases r <;> simp [formulaTag] at ht
      | _ => simp [formulaTag] at ht
    | or φ₁ ψ₁ ih1 ih2 =>
      have ht := tag_eq (φ₁.or ψ₁) φ₂ h
      cases φ₂ with
      | or φ₂ ψ₂ =>
        have h2 := congrArg (fun k => (Nat.unpair k).2) h
        change (Nat.unpair (Nat.pair 7 (Nat.pair (encodeFormula φ₁) (encodeFormula ψ₁)))).2 =
          (Nat.unpair (Nat.pair 7 (Nat.pair (encodeFormula φ₂) (encodeFormula ψ₂)))).2 at h2
        rw [Nat.unpair_pair, Nat.unpair_pair] at h2
        have ha : encodeFormula φ₁ = encodeFormula φ₂ := by
          have := congrArg (fun k => (Nat.unpair k).1) h2; simpa [Nat.unpair_pair] using this
        have hb : encodeFormula ψ₁ = encodeFormula ψ₂ := by
          have := congrArg (fun k => (Nat.unpair k).2) h2; simpa [Nat.unpair_pair] using this
        rw [ih1 ha, ih2 hb]
      | rel r _ => cases r <;> simp [formulaTag] at ht
      | nrel r _ => cases r <;> simp [formulaTag] at ht
      | _ => simp [formulaTag] at ht
    | all φ₁ ih =>
      have ht := tag_eq φ₁.all φ₂ h
      cases φ₂ with
      | all φ₂ =>
        have h2 := congrArg (fun k => (Nat.unpair k).2) h
        change (Nat.unpair (Nat.pair 8 (encodeFormula φ₁))).2 =
          (Nat.unpair (Nat.pair 8 (encodeFormula φ₂))).2 at h2
        rw [Nat.unpair_pair, Nat.unpair_pair] at h2
        rw [ih h2]
      | rel r _ => cases r <;> simp [formulaTag] at ht
      | nrel r _ => cases r <;> simp [formulaTag] at ht
      | _ => simp [formulaTag] at ht
    | exs φ₁ ih =>
      have ht := tag_eq φ₁.exs φ₂ h
      cases φ₂ with
      | exs φ₂ =>
        have h2 := congrArg (fun k => (Nat.unpair k).2) h
        change (Nat.unpair (Nat.pair 9 (encodeFormula φ₁))).2 =
          (Nat.unpair (Nat.pair 9 (encodeFormula φ₂))).2 at h2
        rw [Nat.unpair_pair, Nat.unpair_pair] at h2
        rw [ih h2]
      | rel r _ => cases r <;> simp [formulaTag] at ht
      | nrel r _ => cases r <;> simp [formulaTag] at ht
      | _ => simp [formulaTag] at ht
  have : Countable (Proposition ℒₛₑₜ) := Function.Injective.countable encodeFormula_injective
  have : Nonempty (Proposition ℒₛₑₜ) := ⟨Semiformula.verum⟩
  exact exists_surjective_nat (Proposition ℒₛₑₜ)


/- ## 5. Henkin maximal consistent set construction & `zf_complete` -/

private lemma exConsistent : ∃ con : Set (Proposition ℒₛₑₜ) → Prop,
    ∀ S, con S ↔ ∀ A : Multiset (Proposition ℒₛₑₜ), (∀ φ ∈ A, φ ∈ S) → ¬ Nonempty (Derivation (∼A)) :=
  ⟨fun S => ∀ A : Multiset (Proposition ℒₛₑₜ), (∀ φ ∈ A, φ ∈ S) → ¬ Nonempty (Derivation (∼A)),
    fun _ => Iff.rfl⟩

private lemma consistent_iff {S : Set (Proposition ℒₛₑₜ)} :
    exConsistent.choose S ↔
      ∀ A : Multiset (Proposition ℒₛₑₜ), (∀ φ ∈ A, φ ∈ S) → ¬ Nonempty (Derivation (∼A)) :=
  exConsistent.choose_spec S

private lemma consistent_mono {S₁ S₂ : Set (Proposition ℒₛₑₜ)} (h : S₁ ⊆ S₂)
    (h2 : exConsistent.choose S₂) : exConsistent.choose S₁ :=
  consistent_iff.mpr fun A hA => (consistent_iff.mp h2) A (fun φ hφ => h (hA φ hφ))

private lemma consistent_base {T : Theory ℒₛₑₜ} {σ : Sentence ℒₛₑₜ}
    (hnp : ¬ FFL.Entailment.Provable T σ) :
    exConsistent.choose ({∼(Rewriting.emb σ)} ∪ {p | ∃ ψ ∈ T, p = Rewriting.emb ψ}) := by
  rw [consistent_iff]
  intro A hA ⟨d⟩
  have hsplit : ∃ axms : Multiset (Sentence ℒₛₑₜ),
      (∀ ψ ∈ axms, ψ ∈ T) ∧ ∼A ⊆ (⦃σ⦄ + ∼axms).map Rewriting.emb := by
    clear d
    induction A using Multiset.induction_on with
    | empty => refine ⟨0, by simp, by simp [neg_map]⟩
    | cons a s ih =>
      obtain ⟨axms, hax, hsub⟩ := ih (fun φ hφ => hA φ (Multiset.mem_cons_of_mem hφ))
      have ha := hA a (Multiset.mem_cons_self a s)
      rcases ha with rfl | ⟨ψ, hψT, rfl⟩
      · refine ⟨axms, hax, ?_⟩
        intro x hx
        rw [neg_map, Multiset.map_cons, Multiset.mem_cons] at hx
        rcases hx with rfl | hxs
        · rw [neg_neg_formula, Multiset.map_add, atom_eq, Multiset.map_singleton, Multiset.mem_add]
          exact Or.inl (Multiset.mem_singleton_self _)
        · exact hsub hxs
      · refine ⟨ψ ::ₘ axms, ?_, ?_⟩
        · intro x hx
          rcases Multiset.mem_cons.mp hx with rfl | hx'
          · exact hψT
          · exact hax x hx'
        · intro x hx
          rw [neg_map, Multiset.map_cons, Multiset.mem_cons] at hx
          rcases hx with rfl | hxs
          · have hneg : ∼(Rewriting.emb ψ : Proposition ℒₛₑₜ) = Rewriting.emb (∼ψ) :=
              ((Semiformula.rew Rew.emb).map_neg' ψ).symm
            rw [hneg, Multiset.map_add, Multiset.mem_add]
            right
            rw [neg_map, Multiset.map_cons, Multiset.map_cons, Multiset.mem_cons]
            exact Or.inl rfl
          · have hmem := hsub hxs
            simp only [Multiset.map_add, Multiset.mem_add] at hmem ⊢
            rcases hmem with h1 | h2
            · exact Or.inl h1
            · right
              rw [neg_map, Multiset.map_cons, Multiset.map_cons, Multiset.mem_cons]
              exact Or.inr h2
  obtain ⟨axms, hax, hsub⟩ := hsplit
  exact hnp ⟨⟨axms, hax, Derivation.contraction d hsub⟩⟩

private lemma consistent_union_witness {S : Set (Proposition ℒₛₑₜ)}
    {ψ : Semiproposition ℒₛₑₜ 1} {c : ℕ}
    (hcon : exConsistent.choose (S ∪ {∃¹ ψ}))
    (hfreshS : ∀ φ ∈ S, c ∉ φ.freeVariables)
    (hfreshψ : c ∉ ψ.freeVariables) :
    exConsistent.choose (S ∪ {∃¹ ψ, ψ/[&c]}) := by
  rw [consistent_iff]
  intro A hA ⟨d⟩
  let B := A.filter (fun φ => φ ∈ S)
  have hB_mem : ∀ φ ∈ B, φ ∈ S := fun φ hφ => (Multiset.mem_filter.mp hφ).2
  have hsub : ∼A ⊆ (∼B + ⦃∀¹ (∼ψ)⦄) + ⦃(∼ψ)/[&c]⦄ := by
    intro x hx
    obtain ⟨a, haA, rfl⟩ := Multiset.mem_map.mp hx
    have ha := hA a haA
    by_cases haS : a ∈ S
    · have haB : a ∈ B := Multiset.mem_filter.mpr ⟨haA, haS⟩
      have hnaB : ∼a ∈ ∼B := Multiset.mem_map.mpr ⟨a, haB, rfl⟩
      simp [atom_eq, hnaB]
    · rcases ha with h1 | (rfl | rfl)
      · exact (haS h1).elim
      · rw [neg_exs]; simp [atom_eq]
      · have hneg : ∼(ψ/[&c]) = (∼ψ)/[&c] :=
          ((Semiformula.rew (Rew.subst (![&c] : Fin 1 → Semiterm ℒₛₑₜ ℕ 0))).map_neg' ψ).symm
        rw [hneg]; simp [atom_eq]
  have d1 : Derivation ((∼B + ⦃∀¹ (∼ψ)⦄) + ⦃(∼ψ)/[&c]⦄) := Derivation.contraction d hsub
  have hfresh_ctx : ∀ φ ∈ ∼B + ⦃∀¹ (∼ψ)⦄, c ∉ φ.freeVariables := by
    intro φ hφ
    simp only [Multiset.mem_add, atom_eq, Multiset.mem_singleton] at hφ
    rcases hφ with h1 | rfl
    · obtain ⟨b, hbB, rfl⟩ := Multiset.mem_map.mp h1
      rw [freeVariables_neg]
      exact hfreshS b (hB_mem b hbB)
    · exact (freeVariables_neg ψ) ▸ hfreshψ
  have hfresh_negψ : c ∉ (∼ψ).freeVariables := (freeVariables_neg ψ) ▸ hfreshψ
  obtain ⟨d2⟩ := deriv_all_of_fresh hfresh_ctx hfresh_negψ d1
  have d3 : Derivation (∼((∃¹ ψ) ::ₘ B)) := by
    refine Derivation.contraction d2 ?_
    intro x hx
    simp only [Multiset.mem_add, atom_eq, Multiset.mem_singleton] at hx
    rw [neg_map, Multiset.map_cons, Multiset.mem_cons]
    rcases hx with (h1 | rfl) | rfl
    · exact Or.inr h1
    · exact Or.inl (neg_exs ψ).symm
    · exact Or.inl (neg_exs ψ).symm
  refine (consistent_iff.mp hcon) ((∃¹ ψ) ::ₘ B) ?_ ⟨d3⟩
  intro x hx
  rcases Multiset.mem_cons.mp hx with rfl | hxB
  · exact Or.inr rfl
  · exact Or.inl (hB_mem x hxB)

private lemma exHenkin : ∃ he : Set (Proposition ℒₛₑₜ) → (ℕ → Proposition ℒₛₑₜ) →
      ℕ → Finset (Proposition ℒₛₑₜ),
    (∀ S₀ enum, he S₀ enum 0 = ∅) ∧
    (∀ S₀ enum k, he S₀ enum (k + 1) =
      let E := he S₀ enum k
      let φ := enum k
      if exConsistent.choose (S₀ ∪ (E : Set (Proposition ℒₛₑₜ)) ∪ {φ}) then
        match φ with
        | Semiformula.exs ψ =>
          let c := max ψ.fvSup (E.sup Semiformula.fvSup)
          insert (ψ/[&c]) (insert (Semiformula.exs ψ) E)
        | _ => insert φ E
      else E) := by
  refine ⟨fun S₀ enum => Nat.rec ∅ (fun k E =>
    let φ := enum k
    if exConsistent.choose (S₀ ∪ (E : Set (Proposition ℒₛₑₜ)) ∪ {φ}) then
      match φ with
      | Semiformula.exs ψ =>
        let c := max ψ.fvSup (E.sup Semiformula.fvSup)
        insert (ψ/[&c]) (insert (Semiformula.exs ψ) E)
      | _ => insert φ E
    else E), fun _ _ => rfl, fun _ _ _ => rfl⟩

private lemma henkinExtra_mono (S₀ : Set (Proposition ℒₛₑₜ)) (enum : ℕ → Proposition ℒₛₑₜ) (k : ℕ) :
    exHenkin.choose S₀ enum k ⊆ exHenkin.choose S₀ enum (k + 1) := by
  rw [exHenkin.choose_spec.2]
  dsimp only
  split_ifs
  · intro x hx
    cases enum k <;> simp [hx]
  · exact Finset.Subset.refl _

private lemma henkinExtra_mono_le (S₀ : Set (Proposition ℒₛₑₜ)) (enum : ℕ → Proposition ℒₛₑₜ)
    {j k : ℕ} (h : j ≤ k) :
    exHenkin.choose S₀ enum j ⊆ exHenkin.choose S₀ enum k := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (henkinExtra_mono S₀ enum _)

private lemma henkin_consistent (S₀ : Set (Proposition ℒₛₑₜ)) (enum : ℕ → Proposition ℒₛₑₜ)
    (hS₀_con : exConsistent.choose S₀) (hS₀_closed : ∀ φ ∈ S₀, φ.freeVariables = ∅) :
    ∀ k : ℕ, exConsistent.choose (S₀ ∪ (exHenkin.choose S₀ enum k : Set (Proposition ℒₛₑₜ))) := by
  intro k
  induction k with
  | zero =>
    rw [exHenkin.choose_spec.1]
    simpa using hS₀_con
  | succ k ih =>
    rw [exHenkin.choose_spec.2]
    dsimp only
    split_ifs with hcon
    · cases hφ : enum k with
      | exs ψ =>
        rw [hφ] at hcon
        set E := exHenkin.choose S₀ enum k
        set c := max ψ.fvSup (E.sup Semiformula.fvSup)
        have hfreshS : ∀ χ ∈ S₀ ∪ (E : Set (Proposition ℒₛₑₜ)), c ∉ χ.freeVariables := by
          intro χ hχ hc
          rcases hχ with h1 | h2
          · rw [hS₀_closed χ h1] at hc; exact Finset.notMem_empty c hc
          · have hlt := fv_lt_fvSup χ hc
            have hle : χ.fvSup ≤ E.sup Semiformula.fvSup :=
              Finset.le_sup (f := Semiformula.fvSup) h2
            omega
        have hfreshψ : c ∉ ψ.freeVariables := by
          intro hc
          have hlt := fv_lt_fvSup ψ hc
          omega
        have hcon' := consistent_union_witness hcon hfreshS hfreshψ
        refine consistent_mono ?_ hcon'
        intro x hx
        rcases hx with h1 | h2
        · exact Or.inl (Or.inl h1)
        · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at h2
          rcases h2 with rfl | rfl | hE
          · exact Or.inr (Or.inr rfl)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl (Or.inr hE)
      | _ =>
        refine consistent_mono ?_ hcon
        intro x hx
        rcases hx with h1 | h2
        · exact Or.inl (Or.inl h1)
        · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at h2
          rcases h2 with rfl | hE
          · rw [← hφ]; exact Or.inr rfl
          · exact Or.inl (Or.inr hE)
    · exact ih

private lemma deriv_neg_elim {S : Set (Proposition ℒₛₑₜ)} (hcon : exConsistent.choose S)
    {φ : Proposition ℒₛₑₜ} (hmax : ∀ ψ, exConsistent.choose (S ∪ {ψ}) → ψ ∈ S) :
    φ ∈ S ↔ ∼φ ∉ S := by
  constructor
  · intro hφ hnφ
    obtain ⟨dem⟩ := deriv_em φ
    exact (consistent_iff.mp hcon) ⦃∼φ, φ⦄ (by
      intro x hx
      simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
      ⟨Derivation.contraction dem (by
        intro x hx
        simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton,
          neg_map, Multiset.map_add, Multiset.map_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (neg_neg_formula _).symm)⟩
  · intro hnφ
    by_contra hφ
    have h1 : ¬ exConsistent.choose (S ∪ {φ}) := fun hc => hφ (hmax φ hc)
    have h2 : ¬ exConsistent.choose (S ∪ {∼φ}) := fun hc => hnφ (hmax (∼φ) hc)
    rw [consistent_iff] at h1 h2
    push Not at h1 h2
    obtain ⟨A₁, hA₁, ⟨d₁⟩⟩ := h1
    obtain ⟨A₂, hA₂, ⟨d₂⟩⟩ := h2
    let B₁ := A₁.filter (· ∈ S)
    let B₂ := A₂.filter (· ∈ S)
    have hsub₁ : ∼A₁ ⊆ ∼B₁ + ⦃∼φ⦄ := by
      intro x hx
      obtain ⟨a, haA, rfl⟩ := Multiset.mem_map.mp hx
      simp only [Multiset.mem_add, atom_eq, Multiset.mem_singleton]
      by_cases haS : a ∈ S
      · exact Or.inl (Multiset.mem_map.mpr ⟨a, Multiset.mem_filter.mpr ⟨haA, haS⟩, rfl⟩)
      · rcases hA₁ a haA with h | rfl
        · exact (haS h).elim
        · exact Or.inr rfl
    have hsub₂ : ∼A₂ ⊆ ∼B₂ + ⦃φ⦄ := by
      intro x hx
      obtain ⟨a, haA, rfl⟩ := Multiset.mem_map.mp hx
      simp only [Multiset.mem_add, atom_eq, Multiset.mem_singleton]
      by_cases haS : a ∈ S
      · exact Or.inl (Multiset.mem_map.mpr ⟨a, Multiset.mem_filter.mpr ⟨haA, haS⟩, rfl⟩)
      · rcases hA₂ a haA with h | rfl
        · exact (haS h).elim
        · exact Or.inr (neg_neg_formula _)
    have dcut : Derivation (∼B₂ + ∼B₁) :=
      Derivation.cut (Derivation.contraction d₂ hsub₂) (Derivation.contraction d₁ hsub₁)
    refine (consistent_iff.mp hcon) (B₂ + B₁) ?_ ⟨by simpa [neg_map] using dcut⟩
    intro x hx
    rcases Multiset.mem_add.mp hx with h | h
    · exact (Multiset.mem_filter.mp h).2
    · exact (Multiset.mem_filter.mp h).2

private lemma mem_of_deriv {S : Set (Proposition ℒₛₑₜ)} (hcon : exConsistent.choose S)
    (hmax : ∀ ψ, exConsistent.choose (S ∪ {ψ}) → ψ ∈ S)
    {A : Multiset (Proposition ℒₛₑₜ)} (hA : ∀ ψ ∈ A, ψ ∈ S)
    {φ : Proposition ℒₛₑₜ} (d : Derivation (∼A + ⦃φ⦄)) : φ ∈ S := by
  rw [deriv_neg_elim hcon hmax]
  intro hnφ
  refine (consistent_iff.mp hcon) ((∼φ) ::ₘ A) ?_ ⟨?_⟩
  · intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hxA
    · exact hnφ
    · exact hA x hxA
  · refine Derivation.contraction d ?_
    intro x hx
    simp only [Multiset.mem_add, atom_eq, Multiset.mem_singleton] at hx
    rw [neg_map, Multiset.map_cons, Multiset.mem_cons]
    rcases hx with h | rfl
    · exact Or.inr h
    · exact Or.inl (neg_neg_formula _).symm

private lemma completeness_raw {T : Theory ℒₛₑₜ} {σ : Sentence ℒₛₑₜ}
    (hnp : ¬ FFL.Entailment.Provable T σ) :
    ∃ (req rmem : ℕ → ℕ → Prop),
      (∀ ψ ∈ T, exEvalRaw.choose req rmem Fin.elim0 id (Rewriting.emb ψ)) ∧
      ¬ exEvalRaw.choose req rmem Fin.elim0 id (Rewriting.emb σ) := by
  let S₀ : Set (Proposition ℒₛₑₜ) :=
    {∼(Rewriting.emb σ)} ∪ {p | ∃ ψ ∈ T, p = Rewriting.emb ψ}
  have hS₀_con : exConsistent.choose S₀ := consistent_base hnp
  have hS₀_closed : ∀ φ ∈ S₀, φ.freeVariables = ∅ := by
    intro φ hφ
    rcases hφ with rfl | ⟨ψ, _, rfl⟩
    · rw [freeVariables_neg]; exact freeVariables_emb σ
    · exact freeVariables_emb ψ
  obtain ⟨enum, henum⟩ := exists_enum_prop
  let Sk : ℕ → Set (Proposition ℒₛₑₜ) := fun k => S₀ ∪ (exHenkin.choose S₀ enum k : Set _)
  let S : Set (Proposition ℒₛₑₜ) := ⋃ k : ℕ, Sk k
  have hSk_con : ∀ k, exConsistent.choose (Sk k) := henkin_consistent S₀ enum hS₀_con hS₀_closed
  have hS_con : exConsistent.choose S := by
    rw [consistent_iff]
    intro A hA hd
    have hex : ∃ N : ℕ, ∀ φ ∈ A, φ ∈ Sk N := by
      clear hd
      induction A using Multiset.induction_on with
      | empty => exact ⟨0, by simp⟩
      | cons a s ih =>
        obtain ⟨N₁, hN₁⟩ := ih (fun φ hφ => hA φ (Multiset.mem_cons_of_mem hφ))
        obtain ⟨N₂, hN₂⟩ := Set.mem_iUnion.mp (hA a (Multiset.mem_cons_self a s))
        refine ⟨max N₁ N₂, fun φ hφ => ?_⟩
        rcases Multiset.mem_cons.mp hφ with rfl | hs
        · rcases hN₂ with h0 | hE
          · exact Or.inl h0
          · exact Or.inr (henkinExtra_mono_le S₀ enum (le_max_right N₁ N₂) hE)
        · rcases hN₁ φ hs with h0 | hE
          · exact Or.inl h0
          · exact Or.inr (henkinExtra_mono_le S₀ enum (le_max_left N₁ N₂) hE)
    obtain ⟨N, hN⟩ := hex
    exact (consistent_iff.mp (hSk_con N)) A hN hd
  have hS_max : ∀ φ : Proposition ℒₛₑₜ, exConsistent.choose (S ∪ {φ}) → φ ∈ S := by
    intro φ hcon
    obtain ⟨k, rfl⟩ := henum φ
    have hsub : Sk k ∪ {enum k} ⊆ S ∪ {enum k} := by
      intro x hx
      rcases hx with h | h
      · exact Or.inl (Set.mem_iUnion.mpr ⟨k, h⟩)
      · exact Or.inr h
    have hconk : exConsistent.choose (Sk k ∪ {enum k}) := consistent_mono hsub hcon
    refine Set.mem_iUnion.mpr ⟨k + 1, Or.inr ?_⟩
    show enum k ∈ exHenkin.choose S₀ enum (k + 1)
    rw [exHenkin.choose_spec.2]
    dsimp only
    rw [if_pos hconk]
    cases enum k <;> simp
  have hS_witness : ∀ ψ : Semiproposition ℒₛₑₜ 1, (∃¹ ψ) ∈ S → ∃ c : ℕ, ψ/[&c] ∈ S := by
    intro ψ hmem
    obtain ⟨k, hk⟩ := henum (∃¹ ψ)
    have hconk : exConsistent.choose (Sk k ∪ {enum k}) := by
      rw [hk]
      refine consistent_mono ?_ hS_con
      intro x hx
      rcases hx with h | rfl
      · exact Set.mem_iUnion.mpr ⟨k, h⟩
      · exact hmem
    refine ⟨max ψ.fvSup ((exHenkin.choose S₀ enum k).sup Semiformula.fvSup),
      Set.mem_iUnion.mpr ⟨k + 1, Or.inr ?_⟩⟩
    show ψ/[&_] ∈ exHenkin.choose S₀ enum (k + 1)
    rw [exHenkin.choose_spec.2]
    dsimp only
    rw [if_pos hconk, hk]
    simp
  have hS_neg : ∀ φ, φ ∈ S ↔ ∼φ ∉ S := fun _ => deriv_neg_elim hS_con hS_max
  have hS_verum : (⊤ : Proposition ℒₛₑₜ) ∈ S :=
    mem_of_deriv hS_con hS_max (A := 0) (by simp) (by
      have h0 : ∼(0 : Multiset (Proposition ℒₛₑₜ)) + ⦃⊤⦄ = ⦃⊤⦄ := by simp [neg_map]
      rw [h0]; exact Derivation.verum)
  have hS_falsum : (⊥ : Proposition ℒₛₑₜ) ∉ S := fun h => (hS_neg ⊤).mp hS_verum h
  have hS_and : ∀ φ ψ : Proposition ℒₛₑₜ, (φ ⋏ ψ) ∈ S ↔ φ ∈ S ∧ ψ ∈ S := by
    intro φ ψ
    constructor
    · intro h
      obtain ⟨demφ⟩ := deriv_em φ
      obtain ⟨demψ⟩ := deriv_em ψ
      have h1 : φ ∈ S := mem_of_deriv hS_con hS_max (A := ⦃φ ⋏ ψ⦄) (by simpa [atom_eq]) (by
        have d : Derivation (⦃φ⦄ + ⦃∼φ, ∼ψ⦄) :=
          Derivation.contraction demφ (by
            intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
            rcases hx with rfl | rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl rfl)
        exact Derivation.contraction (Derivation.or d) (by
          intro x hx; simp only [atom_eq, neg_map, Multiset.mem_add, Multiset.map_singleton,
            Multiset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl (neg_and φ ψ).symm))
      have h2 : ψ ∈ S := mem_of_deriv hS_con hS_max (A := ⦃φ ⋏ ψ⦄) (by simpa [atom_eq]) (by
        have d : Derivation (⦃ψ⦄ + ⦃∼φ, ∼ψ⦄) :=
          Derivation.contraction demψ (by
            intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
            rcases hx with rfl | rfl
            · exact Or.inr (Or.inr rfl)
            · exact Or.inl rfl)
        exact Derivation.contraction (Derivation.or d) (by
          intro x hx; simp only [atom_eq, neg_map, Multiset.mem_add, Multiset.map_singleton,
            Multiset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl (neg_and φ ψ).symm))
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨demφ⟩ := deriv_em φ
      obtain ⟨demψ⟩ := deriv_em ψ
      exact mem_of_deriv hS_con hS_max (A := ⦃φ, ψ⦄) (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption) (by
        have d1 : Derivation (∼⦃φ, ψ⦄ + ⦃φ⦄) :=
          Derivation.contraction demφ (by
            intro x hx; simp only [atom_eq, neg_map, Multiset.mem_add, Multiset.map_add,
              Multiset.map_singleton, Multiset.mem_singleton] at hx ⊢
            rcases hx with rfl | rfl
            · exact Or.inl (Or.inl rfl)
            · exact Or.inr rfl)
        have d2 : Derivation (∼⦃φ, ψ⦄ + ⦃ψ⦄) :=
          Derivation.contraction demψ (by
            intro x hx; simp only [atom_eq, neg_map, Multiset.mem_add, Multiset.map_add,
              Multiset.map_singleton, Multiset.mem_singleton] at hx ⊢
            rcases hx with rfl | rfl
            · exact Or.inl (Or.inr rfl)
            · exact Or.inr rfl)
        exact Derivation.and d1 d2)
  have hS_or : ∀ φ ψ : Proposition ℒₛₑₜ, (φ ⋎ ψ) ∈ S ↔ φ ∈ S ∨ ψ ∈ S := by
    intro φ ψ
    rw [hS_neg (φ ⋎ ψ)]
    change (∼φ ⋏ ∼ψ) ∉ S ↔ _
    rw [hS_and, not_and_or, ← hS_neg φ, ← hS_neg ψ]
  have hS_exs : ∀ ψ : Semiproposition ℒₛₑₜ 1, (∃¹ ψ) ∈ S ↔ ∃ c : ℕ, ψ/[&c] ∈ S := by
    intro ψ
    constructor
    · exact hS_witness ψ
    · rintro ⟨c, hc⟩
      obtain ⟨dem⟩ := deriv_em (ψ/[&c])
      exact mem_of_deriv hS_con hS_max (A := ⦃ψ/[&c]⦄) (by simpa [atom_eq]) (by
        have d0 : Derivation (∼⦃ψ/[&c]⦄ + ⦃ψ/[&c]⦄) :=
          Derivation.contraction dem (by
            intro x hx; simp only [atom_eq, neg_map, Multiset.mem_add, Multiset.map_singleton,
              Multiset.mem_singleton] at hx ⊢
            exact hx)
        exact Derivation.exs d0)
  have hS_all : ∀ ψ : Semiproposition ℒₛₑₜ 1, (∀¹ ψ) ∈ S ↔ ∀ c : ℕ, ψ/[&c] ∈ S := by
    intro ψ
    rw [hS_neg (∀¹ ψ)]
    change (∃¹ (∼ψ)) ∉ S ↔ _
    rw [hS_exs, not_exists]
    refine forall_congr' fun c => ?_
    have hneg : (∼ψ)/[&c] = ∼(ψ/[&c]) :=
      (Semiformula.rew (Rew.subst (![&c] : Fin 1 → Semiterm ℒₛₑₜ ℕ 0))).map_neg' ψ
    rw [hneg, ← hS_neg]
  let req : ℕ → ℕ → Prop := fun a b => (Semiformula.rel Language.Set.Rel.eq ![&a, &b]) ∈ S
  let rmem : ℕ → ℕ → Prop := fun a b => (Semiformula.rel Language.Set.Rel.mem ![&a, &b]) ∈ S
  have hvec_subst : ∀ {n : ℕ} (e : Fin n → ℕ) (v : Fin 2 → Semiterm ℒₛₑₜ ℕ n),
      (fun i : Fin 2 => Rew.subst (n' := 0) (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0)) (v i)) =
        ![(&(exTvRaw.choose e id (v 0)) : Semiterm ℒₛₑₜ ℕ 0),
          (&(exTvRaw.choose e id (v 1)) : Semiterm ℒₛₑₜ ℕ 0)] := by
    intro n e v
    funext i; fin_cases i
    · change Rew.subst (n' := 0) (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0)) (v 0) = &(exTvRaw.choose e id (v 0))
      cases v 0 with
      | bvar j => rw [tvRaw_bvar]; rfl
      | fvar x => rw [tvRaw_fvar]; rfl
      | func f _ => exact (f : Empty).elim
    · change Rew.subst (n' := 0) (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0)) (v 1) = &(exTvRaw.choose e id (v 1))
      cases v 1 with
      | bvar j => rw [tvRaw_bvar]; rfl
      | fvar x => rw [tvRaw_fvar]; rfl
      | func f _ => exact (f : Empty).elim
  have htruth : ∀ (k : ℕ) {n : ℕ} (φ : Semiproposition ℒₛₑₜ n), exComp.choose φ ≤ k →
      ∀ (e : Fin n → ℕ),
        exEvalRaw.choose req rmem e id φ ↔ (Rew.subst (fun i => &(e i)) ▹ φ) ∈ S := by
    intro k
    induction k with
    | zero =>
      intro n φ hk e
      cases φ with
      | verum => rw [ev_verum]; exact ⟨fun _ => hS_verum, fun _ => trivial⟩
      | falsum => rw [ev_falsum]; exact ⟨False.elim, fun h => (hS_falsum h).elim⟩
      | rel r v =>
        cases r with
        | eq =>
          rw [ev_rel_eq]
          change req (exTvRaw.choose e id (v 0)) (exTvRaw.choose e id (v 1)) ↔
            Semiformula.rel Language.Set.Rel.eq
              (fun i => Rew.subst (n' := 0) (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0)) (v i)) ∈ S
          rw [hvec_subst e v]
        | mem =>
          rw [ev_rel_mem]
          change rmem (exTvRaw.choose e id (v 0)) (exTvRaw.choose e id (v 1)) ↔
            Semiformula.rel Language.Set.Rel.mem
              (fun i => Rew.subst (n' := 0) (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0)) (v i)) ∈ S
          rw [hvec_subst e v]
      | nrel r v =>
        cases r with
        | eq =>
          rw [ev_nrel_eq]
          change ¬ req (exTvRaw.choose e id (v 0)) (exTvRaw.choose e id (v 1)) ↔
            Semiformula.nrel Language.Set.Rel.eq
              (fun i => Rew.subst (n' := 0) (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0)) (v i)) ∈ S
          rw [hvec_subst e v, hS_neg]; rfl
        | mem =>
          rw [ev_nrel_mem]
          change ¬ rmem (exTvRaw.choose e id (v 0)) (exTvRaw.choose e id (v 1)) ↔
            Semiformula.nrel Language.Set.Rel.mem
              (fun i => Rew.subst (n' := 0) (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0)) (v i)) ∈ S
          rw [hvec_subst e v, hS_neg]; rfl
      | and _ _ => rw [comp_and] at hk; omega
      | or _ _ => rw [comp_or] at hk; omega
      | all _ => rw [comp_all] at hk; omega
      | exs _ => rw [comp_exs] at hk; omega
    | succ k ih =>
      intro n φ hk e
      cases φ with
      | verum => rw [ev_verum]; exact ⟨fun _ => hS_verum, fun _ => trivial⟩
      | falsum => rw [ev_falsum]; exact ⟨False.elim, fun h => (hS_falsum h).elim⟩
      | rel r v => exact ih (Semiformula.rel r v) (by rw [comp_rel]; omega) e
      | nrel r v => exact ih (Semiformula.nrel r v) (by rw [comp_nrel]; omega) e
      | and φ₁ φ₂ =>
        rw [comp_and] at hk
        rw [ev_and]
        change (exEvalRaw.choose req rmem e id φ₁ ∧ exEvalRaw.choose req rmem e id φ₂) ↔
          ((Rew.subst (fun i => &(e i)) ▹ φ₁) ⋏ (Rew.subst (fun i => &(e i)) ▹ φ₂)) ∈ S
        rw [hS_and, ih φ₁ (by omega) e, ih φ₂ (by omega) e]
      | or φ₁ φ₂ =>
        rw [comp_or] at hk
        rw [ev_or]
        change (exEvalRaw.choose req rmem e id φ₁ ∨ exEvalRaw.choose req rmem e id φ₂) ↔
          ((Rew.subst (fun i => &(e i)) ▹ φ₁) ⋎ (Rew.subst (fun i => &(e i)) ▹ φ₂)) ∈ S
        rw [hS_or, ih φ₁ (by omega) e, ih φ₂ (by omega) e]
      | all φ =>
        rw [comp_all] at hk
        rw [ev_all]
        change (∀ d : ℕ, exEvalRaw.choose req rmem (d :> e) id φ) ↔
          (∀¹ ((Rew.subst (n' := 0) (fun i => (&(e i) : Semiterm ℒₛₑₜ ℕ 0))).q ▹ φ)) ∈ S
        rw [hS_all]
        refine forall_congr' fun d => (ih φ (by omega) (d :> e)).trans ?_
        have hcomp : Rew.subst (n' := 0) (fun i => (&((d :> e) i) : Semiterm ℒₛₑₜ ℕ 0)) ▹ φ =
            ((Rew.subst (n' := 0) (fun i => (&(e i) : Semiterm ℒₛₑₜ ℕ 0))).q ▹ φ)/[(&d : Semiterm ℒₛₑₜ ℕ 0)] := by
          change Rew.subst (n' := 0) (fun i => (&((d :> e) i) : Semiterm ℒₛₑₜ ℕ 0)) ▹ φ =
            Rew.subst (n' := 0) ![(&d : Semiterm ℒₛₑₜ ℕ 0)] ▹
              ((Rew.subst (n' := 0) (fun i => (&(e i) : Semiterm ℒₛₑₜ ℕ 0))).q ▹ φ)
          rw [rew_comp]
          exact congrArg (· ▹ φ) (rew_ext (fun i => by cases i using Fin.cases <;> rfl) (fun _ => rfl))
        rw [hcomp]
      | exs φ =>
        rw [comp_exs] at hk
        rw [ev_exs]
        change (∃ d : ℕ, exEvalRaw.choose req rmem (d :> e) id φ) ↔
          (∃¹ ((Rew.subst (n' := 0) (fun i => (&(e i) : Semiterm ℒₛₑₜ ℕ 0))).q ▹ φ)) ∈ S
        rw [hS_exs]
        refine exists_congr fun d => (ih φ (by omega) (d :> e)).trans ?_
        have hcomp : Rew.subst (n' := 0) (fun i => (&((d :> e) i) : Semiterm ℒₛₑₜ ℕ 0)) ▹ φ =
            ((Rew.subst (n' := 0) (fun i => (&(e i) : Semiterm ℒₛₑₜ ℕ 0))).q ▹ φ)/[(&d : Semiterm ℒₛₑₜ ℕ 0)] := by
          change Rew.subst (n' := 0) (fun i => (&((d :> e) i) : Semiterm ℒₛₑₜ ℕ 0)) ▹ φ =
            Rew.subst (n' := 0) ![(&d : Semiterm ℒₛₑₜ ℕ 0)] ▹
              ((Rew.subst (n' := 0) (fun i => (&(e i) : Semiterm ℒₛₑₜ ℕ 0))).q ▹ φ)
          rw [rew_comp]
          exact congrArg (· ▹ φ) (rew_ext (fun i => by cases i using Fin.cases <;> rfl) (fun _ => rfl))
        rw [hcomp]
  have hsubst0 : ∀ φ : Proposition ℒₛₑₜ,
      Rew.subst (fun i : Fin 0 => &(Fin.elim0 i)) ▹ φ = φ := by
    intro φ
    have h1 : Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (fun i : Fin 0 => &(Fin.elim0 i)) = Rew.id :=
      rew_ext (fun i => Fin.elim0 i) (fun _ => rfl)
    rw [h1, rew_id_eq]
  refine ⟨req, rmem, ?_, ?_⟩
  · intro ψ hψ
    rw [htruth (exComp.choose (Rewriting.emb ψ)) (Rewriting.emb ψ) le_rfl Fin.elim0, hsubst0]
    exact Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inr ⟨ψ, hψ, rfl⟩)⟩
  · rw [htruth (exComp.choose (Rewriting.emb σ)) (Rewriting.emb σ) le_rfl Fin.elim0, hsubst0, hS_neg]
    push Not
    exact Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inl rfl)⟩

private lemma evalRaw_quotient {req rmem : ℕ → ℕ → Prop} (heqv : Equivalence req)
    (hresp : ∀ a₁ b₁ a₂ b₂, req a₁ a₂ → req b₁ b₂ → (rmem a₁ b₁ ↔ rmem a₂ b₂)) :
    let s : Setoid ℕ := ⟨req, heqv⟩
    let V := Quotient s
    let mem : V → V → Prop := Quotient.lift₂ rmem (fun a₁ b₁ a₂ b₂ h1 h2 => propext (hresp a₁ b₁ a₂ b₂ h1 h2))
    ∀ {ξ : Type} {n : ℕ} (e : Fin n → ℕ) (ε : ξ → ℕ) (φ : Semiformula ℒₛₑₜ ξ n),
      exEvalRaw.choose Eq mem (Quotient.mk s ∘ e) (Quotient.mk s ∘ ε) φ ↔
        exEvalRaw.choose req rmem e ε φ := by
  intro s V mem ξ n e ε φ
  have htv : ∀ (m : ℕ) (e : Fin m → ℕ) (ε : ξ → ℕ) (t : Semiterm ℒₛₑₜ ξ m),
      exTvRaw.choose (Quotient.mk s ∘ e) (Quotient.mk s ∘ ε) t =
        Quotient.mk s (exTvRaw.choose e ε t) := by
    intro m e ε t
    cases t with
    | bvar i => rw [tvRaw_bvar, tvRaw_bvar]; rfl
    | fvar x => rw [tvRaw_fvar, tvRaw_fvar]; rfl
    | func f _ => exact (f : Empty).elim
  induction φ with
  | verum => rw [ev_verum, ev_verum]
  | falsum => rw [ev_falsum, ev_falsum]
  | rel r v =>
    cases r with
    | eq => rw [ev_rel_eq, ev_rel_eq, htv, htv, Quotient.eq]; rfl
    | mem => rw [ev_rel_mem, ev_rel_mem, htv, htv]; rfl
  | nrel r v =>
    cases r with
    | eq => rw [ev_nrel_eq, ev_nrel_eq, htv, htv, Quotient.eq]; rfl
    | mem => rw [ev_nrel_mem, ev_nrel_mem, htv, htv]; rfl
  | and φ ψ ih1 ih2 => rw [ev_and, ev_and]; exact and_congr (ih1 e) (ih2 e)
  | or φ ψ ih1 ih2 => rw [ev_or, ev_or]; exact or_congr (ih1 e) (ih2 e)
  | all φ ih =>
    rw [ev_all, ev_all]
    constructor
    · intro h d
      have hd := h (Quotient.mk s d)
      have hcons : (Quotient.mk s d :> (Quotient.mk s ∘ e)) = Quotient.mk s ∘ (d :> e) := by
        funext i; cases i using Fin.cases <;> rfl
      rw [hcons] at hd
      exact (ih (d :> e)).mp hd
    · intro h d
      refine Quotient.inductionOn d fun a => ?_
      have hcons : (Quotient.mk s a :> (Quotient.mk s ∘ e)) = Quotient.mk s ∘ (a :> e) := by
        funext i; cases i using Fin.cases <;> rfl
      rw [hcons]
      exact (ih (a :> e)).mpr (h a)
  | exs φ ih =>
    rw [ev_exs, ev_exs]
    constructor
    · rintro ⟨d, hd⟩
      refine Quotient.inductionOn d (fun a ha => ?_) hd
      have hcons : (Quotient.mk s a :> (Quotient.mk s ∘ e)) = Quotient.mk s ∘ (a :> e) := by
        funext i; cases i using Fin.cases <;> rfl
      rw [hcons] at ha
      exact ⟨a, (ih (a :> e)).mp ha⟩
    · rintro ⟨a, ha⟩
      refine ⟨Quotient.mk s a, ?_⟩
      have hcons : (Quotient.mk s a :> (Quotient.mk s ∘ e)) = Quotient.mk s ∘ (a :> e) := by
        funext i; cases i using Fin.cases <;> rfl
      rw [hcons]
      exact (ih (a :> e)).mpr ha

private lemma zf_complete (σ : SetTheorySentence)
    (h : ∀ (V : Type) (mem : V → V → Prop),
      (∀ ψ ∈ 𝗭𝗙, exEvalRaw.choose Eq mem Fin.elim0 Empty.elim ψ) →
      exEvalRaw.choose Eq mem Fin.elim0 Empty.elim σ) :
    FFL.Entailment.Provable 𝗭𝗙 σ := by
  by_contra hnp
  obtain ⟨req, rmem, hT, hnσ⟩ := completeness_raw hnp
  have hemb : ∀ (ψ : SetTheorySentence),
      exEvalRaw.choose req rmem Fin.elim0 Empty.elim ψ ↔
        exEvalRaw.choose req rmem Fin.elim0 id (Rewriting.emb ψ) := by
    intro ψ
    symm
    refine (evalRaw_rew req rmem Fin.elim0 id Rew.emb ψ).trans ?_
    exact evalRaw_congr req rmem ψ (Subsingleton.elim _ _) (funext fun x => x.elim)
  have hT0 : ∀ ψ ∈ 𝗭𝗙, exEvalRaw.choose req rmem Fin.elim0 Empty.elim ψ :=
    fun ψ hψ => (hemb ψ).mpr (hT ψ hψ)
  have hrefl : ∀ a, req a a := by
    have h1 := hT0 (Theory.Eq.refl ℒₛₑₜ) (ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.refl)
    unfold Theory.Eq.refl at h1
    intro a
    have h2 := (ev_all req rmem _ _ _).mp h1 a
    change exEvalRaw.choose req rmem (a :> Fin.elim0) Empty.elim
      (Semiformula.rel Language.Set.Rel.eq ![#0, #0]) at h2
    rw [ev_rel_eq] at h2
    change req (exTvRaw.choose (a :> Fin.elim0) Empty.elim #0)
      (exTvRaw.choose (a :> Fin.elim0) Empty.elim #0) at h2
    rw [tvRaw_bvar] at h2
    exact h2
  have hsymm : ∀ {a b}, req a b → req b a := by
    have h1 := hT0 (Theory.Eq.symm ℒₛₑₜ) (ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.symm)
    unfold Theory.Eq.symm at h1
    intro a b hab
    have h2 := (ev_all req rmem _ _ _).mp ((ev_all req rmem _ _ _).mp h1 a) b
    change exEvalRaw.choose req rmem (b :> a :> Fin.elim0) Empty.elim
      (Semiformula.or (Semiformula.nrel Language.Set.Rel.eq ![#1, #0])
        (Semiformula.rel Language.Set.Rel.eq ![#0, #1])) at h2
    rw [ev_or, ev_nrel_eq, ev_rel_eq] at h2
    change ¬ req (exTvRaw.choose (b :> a :> Fin.elim0) Empty.elim #1)
      (exTvRaw.choose (b :> a :> Fin.elim0) Empty.elim #0) ∨
      req (exTvRaw.choose (b :> a :> Fin.elim0) Empty.elim #0)
        (exTvRaw.choose (b :> a :> Fin.elim0) Empty.elim #1) at h2
    rw [tvRaw_bvar, tvRaw_bvar] at h2
    exact h2.resolve_left (not_not.mpr hab)
  have htrans : ∀ {a b c}, req a b → req b c → req a c := by
    have h1 := hT0 (Theory.Eq.trans ℒₛₑₜ) (ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.trans)
    unfold Theory.Eq.trans at h1
    intro a b c hab hbc
    have h2 := (ev_all req rmem _ _ _).mp ((ev_all req rmem _ _ _).mp
      ((ev_all req rmem _ _ _).mp h1 a) b) c
    change exEvalRaw.choose req rmem (c :> b :> a :> Fin.elim0) Empty.elim
      (Semiformula.or (Semiformula.nrel Language.Set.Rel.eq ![#2, #1])
        (Semiformula.or (Semiformula.nrel Language.Set.Rel.eq ![#1, #0])
          (Semiformula.rel Language.Set.Rel.eq ![#2, #0]))) at h2
    rw [ev_or, ev_or, ev_nrel_eq, ev_nrel_eq, ev_rel_eq] at h2
    change ¬ req (exTvRaw.choose (c :> b :> a :> Fin.elim0) Empty.elim #2)
      (exTvRaw.choose (c :> b :> a :> Fin.elim0) Empty.elim #1) ∨
      (¬ req (exTvRaw.choose (c :> b :> a :> Fin.elim0) Empty.elim #1)
        (exTvRaw.choose (c :> b :> a :> Fin.elim0) Empty.elim #0) ∨
        req (exTvRaw.choose (c :> b :> a :> Fin.elim0) Empty.elim #2)
          (exTvRaw.choose (c :> b :> a :> Fin.elim0) Empty.elim #0)) at h2
    rw [tvRaw_bvar, tvRaw_bvar, tvRaw_bvar] at h2
    exact (h2.resolve_left (not_not.mpr hab)).resolve_left (not_not.mpr hbc)
  have heqv : Equivalence req := ⟨hrefl, hsymm, htrans⟩
  have hmem_fwd : ∀ a₁ b₁ a₂ b₂, req a₁ a₂ → req b₁ b₂ → rmem a₁ b₁ → rmem a₂ b₂ := by
    have hax : @Theory.Eq.relExt ℒₛₑₜ _ 2 Language.Set.Rel.mem ∈ 𝗭𝗙 :=
      ZermeloFraenkel.axiom_of_equality _ (@Theory.eqAxiom.relExt ℒₛₑₜ _ 2 Language.Set.Rel.mem)
    have h1 := hT0 _ hax
    unfold Theory.Eq.relExt at h1
    intro a₁ b₁ a₂ b₂ h12 h34 hm
    have h2 := (ev_all req rmem _ _ _).mp ((ev_all req rmem _ _ _).mp
      ((ev_all req rmem _ _ _).mp ((ev_all req rmem _ _ _).mp h1 b₂) a₂) b₁) a₁
    change exEvalRaw.choose req rmem (a₁ :> b₁ :> a₂ :> b₂ :> Fin.elim0) Empty.elim
      (Semiformula.or
        (Semiformula.or (Semiformula.nrel Language.Set.Rel.eq ![#0, #2])
          (Semiformula.or (Semiformula.nrel Language.Set.Rel.eq ![#1, #3]) Semiformula.falsum))
        (Semiformula.or (Semiformula.nrel Language.Set.Rel.mem (fun i => #(Fin.addCast 2 i)))
          (Semiformula.rel Language.Set.Rel.mem (fun i => #(i.addNat 2))))) at h2
    rw [ev_or, ev_or, ev_or, ev_or, ev_nrel_eq, ev_nrel_eq, ev_falsum, ev_nrel_mem, ev_rel_mem] at h2
    change ((¬ req (exTvRaw.choose (a₁ :> b₁ :> a₂ :> b₂ :> Fin.elim0) Empty.elim #0)
        (exTvRaw.choose (a₁ :> b₁ :> a₂ :> b₂ :> Fin.elim0) Empty.elim #2) ∨
      (¬ req (exTvRaw.choose (a₁ :> b₁ :> a₂ :> b₂ :> Fin.elim0) Empty.elim #1)
        (exTvRaw.choose (a₁ :> b₁ :> a₂ :> b₂ :> Fin.elim0) Empty.elim #3) ∨ False)) ∨
      (¬ rmem (exTvRaw.choose (a₁ :> b₁ :> a₂ :> b₂ :> Fin.elim0) Empty.elim #0)
        (exTvRaw.choose (a₁ :> b₁ :> a₂ :> b₂ :> Fin.elim0) Empty.elim #1) ∨
      rmem (exTvRaw.choose (a₁ :> b₁ :> a₂ :> b₂ :> Fin.elim0) Empty.elim #2)
        (exTvRaw.choose (a₁ :> b₁ :> a₂ :> b₂ :> Fin.elim0) Empty.elim #3))) at h2
    rw [tvRaw_bvar, tvRaw_bvar, tvRaw_bvar, tvRaw_bvar] at h2
    rcases h2 with (h | h | h) | h | h
    · exact (h h12).elim
    · exact (h h34).elim
    · exact h.elim
    · exact (h hm).elim
    · exact h
  have hresp : ∀ a₁ b₁ a₂ b₂, req a₁ a₂ → req b₁ b₂ → (rmem a₁ b₁ ↔ rmem a₂ b₂) :=
    fun a₁ b₁ a₂ b₂ h1 h2 =>
      ⟨hmem_fwd a₁ b₁ a₂ b₂ h1 h2, hmem_fwd a₂ b₂ a₁ b₁ (hsymm h1) (hsymm h2)⟩
  let s : Setoid ℕ := ⟨req, heqv⟩
  let V := Quotient s
  let mem : V → V → Prop :=
    Quotient.lift₂ rmem (fun a₁ b₁ a₂ b₂ h1 h2 => propext (hresp a₁ b₁ a₂ b₂ h1 h2))
  have hV_zf : ∀ ψ ∈ 𝗭𝗙, exEvalRaw.choose Eq mem Fin.elim0 Empty.elim ψ := by
    intro ψ hψ
    have hq := (evalRaw_quotient heqv hresp Fin.elim0 Empty.elim ψ).mpr (hT0 ψ hψ)
    exact (evalRaw_congr Eq mem ψ (Subsingleton.elim _ _) (funext fun x => x.elim)).mp hq
  have hV_σ := h V mem hV_zf
  have hraw_σ : exEvalRaw.choose req rmem Fin.elim0 Empty.elim σ := by
    have hq : exEvalRaw.choose Eq mem (Quotient.mk s ∘ Fin.elim0) (Quotient.mk s ∘ Empty.elim) σ :=
      (evalRaw_congr Eq mem σ (Subsingleton.elim _ _) (funext fun x => x.elim)).mp hV_σ
    exact (evalRaw_quotient heqv hresp Fin.elim0 Empty.elim σ).mp hq
  exact hnσ ((hemb σ).mp hraw_σ)

/- ## 6. Soundness of One-Sided LK `Derivation` in Any Normal Model `(V, mem) ⊨ 𝗭𝗙𝗖` -/

private lemma evalM_shift {V : Type} {mem : V → V → Prop} {n : ℕ} (e : Fin n → V) (ε : ℕ → V)
    (φ : Semiproposition ℒₛₑₜ n) :
    exEvalRaw.choose Eq mem e ε (Rewriting.shift φ) ↔
      exEvalRaw.choose Eq mem e (fun k => ε (k + 1)) φ :=
  (evalRaw_rew Eq mem e ε Rew.shift φ).trans
    (evalRaw_congr Eq mem φ (funext fun i => tvRaw_bvar e ε i)
      (funext fun x => tvRaw_fvar e ε (x + 1)))

private lemma evalM_free {V : Type} {mem : V → V → Prop} (ε : ℕ → V)
    (φ : Semiproposition ℒₛₑₜ 1) :
    exEvalRaw.choose Eq mem Fin.elim0 ε φ.free ↔
      exEvalRaw.choose Eq mem (ε 0 :> Fin.elim0) (fun k => ε (k + 1)) φ := by
  refine (evalRaw_rew Eq mem Fin.elim0 ε Rew.free φ).trans
    (evalRaw_congr Eq mem φ ?_ (funext fun x => tvRaw_fvar Fin.elim0 ε (x + 1)))
  funext i
  refine Fin.cases (tvRaw_fvar Fin.elim0 ε 0) (fun j => j.elim0) i

private lemma evalM_subst1 {V : Type} {mem : V → V → Prop} (ε : ℕ → V)
    (φ : Semiproposition ℒₛₑₜ 1) (t : Semiterm ℒₛₑₜ ℕ 0) :
    exEvalRaw.choose Eq mem Fin.elim0 ε (φ/[t]) ↔
      exEvalRaw.choose Eq mem (exTvRaw.choose Fin.elim0 ε t :> Fin.elim0) ε φ := by
  refine (evalRaw_rew Eq mem Fin.elim0 ε (Rew.subst ![t]) φ).trans
    (evalRaw_congr Eq mem φ ?_ (funext fun x => tvRaw_fvar Fin.elim0 ε x))
  funext i
  refine Fin.cases rfl (fun j => j.elim0) i

private lemma evalM_emb {V : Type} {mem : V → V → Prop} {n : ℕ} (e : Fin n → V) (ε : ℕ → V)
    (φ : Semisentence ℒₛₑₜ n) :
    exEvalRaw.choose Eq mem e ε (Rewriting.emb φ) ↔ exEvalRaw.choose Eq mem e Empty.elim φ := by
  refine (evalRaw_rew Eq mem e ε Rew.emb φ).trans
    (evalRaw_congr Eq mem φ (funext fun i => tvRaw_bvar e ε i) (funext fun x => x.elim))

private lemma deriv_sound {V : Type} {mem : V → V → Prop} {Γ : Sequent ℒₛₑₜ} (d : Derivation Γ) :
    ∀ ε : ℕ → V, ∃ φ ∈ Γ, exEvalRaw.choose Eq mem Fin.elim0 ε φ := by
  induction d with
  | identity r v =>
    intro ε
    by_cases h : exEvalRaw.choose Eq mem Fin.elim0 ε (Semiformula.rel r v)
    · exact ⟨Semiformula.rel r v, Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl)), h⟩
    · refine ⟨Semiformula.nrel r v, Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl)), ?_⟩
      cases r with
      | eq => rw [ev_nrel_eq]; rw [ev_rel_eq] at h; exact h
      | mem => rw [ev_nrel_mem]; rw [ev_rel_mem] at h; exact h
  | @cut Γ φ Δ _ _ ih1 ih2 =>
    intro ε
    obtain ⟨χ1, h1, e1⟩ := ih1 ε
    obtain ⟨χ2, h2, e2⟩ := ih2 ε
    rcases Multiset.mem_add.mp h1 with h1 | h1
    · exact ⟨χ1, Multiset.mem_add.mpr (Or.inl h1), e1⟩
    rcases Multiset.mem_add.mp h2 with h2 | h2
    · exact ⟨χ2, Multiset.mem_add.mpr (Or.inr h2), e2⟩
    have h1' : χ1 = φ := Multiset.mem_singleton.mp h1
    have h2' : χ2 = ∼φ := Multiset.mem_singleton.mp h2
    rw [h1'] at e1
    rw [h2'] at e2
    exact ((evalRaw_neg Eq mem Fin.elim0 ε φ).mp e2 e1).elim
  | contraction _ hsub ih =>
    intro ε
    obtain ⟨χ, h, e⟩ := ih ε
    exact ⟨χ, hsub h, e⟩
  | verum =>
    intro _
    exact ⟨⊤, Multiset.mem_singleton.mpr rfl, (ev_verum Eq mem _ _).mpr trivial⟩
  | @or Γ φ ψ _ ih =>
    intro ε
    obtain ⟨χ, h, e⟩ := ih ε
    rcases Multiset.mem_add.mp h with h | h
    · exact ⟨χ, Multiset.mem_add.mpr (Or.inl h), e⟩
    · refine ⟨φ ⋎ ψ, Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl)), ?_⟩
      rcases Multiset.mem_add.mp h with h | h
      · have h' : χ = φ := Multiset.mem_singleton.mp h
        rw [h'] at e
        exact (ev_or Eq mem _ _ _ _).mpr (Or.inl e)
      · have h' : χ = ψ := Multiset.mem_singleton.mp h
        rw [h'] at e
        exact (ev_or Eq mem _ _ _ _).mpr (Or.inr e)
  | @and Γ φ ψ _ _ ih1 ih2 =>
    intro ε
    obtain ⟨χ1, h1, e1⟩ := ih1 ε
    obtain ⟨χ2, h2, e2⟩ := ih2 ε
    rcases Multiset.mem_add.mp h1 with h1 | h1
    · exact ⟨χ1, Multiset.mem_add.mpr (Or.inl h1), e1⟩
    rcases Multiset.mem_add.mp h2 with h2 | h2
    · exact ⟨χ2, Multiset.mem_add.mpr (Or.inl h2), e2⟩
    have h1' : χ1 = φ := Multiset.mem_singleton.mp h1
    have h2' : χ2 = ψ := Multiset.mem_singleton.mp h2
    rw [h1'] at e1
    rw [h2'] at e2
    exact ⟨φ ⋏ ψ, Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl)),
      (ev_and Eq mem _ _ _ _).mpr ⟨e1, e2⟩⟩
  | @all Γ φ _ ih =>
    intro ε
    by_cases hΓ : ∃ χ ∈ Γ, exEvalRaw.choose Eq mem Fin.elim0 ε χ
    · obtain ⟨χ, h, e⟩ := hΓ
      exact ⟨χ, Multiset.mem_add.mpr (Or.inl h), e⟩
    refine ⟨∀¹ φ, Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl)), ?_⟩
    refine (ev_all Eq mem _ _ _).mpr fun x => ?_
    let ε' : ℕ → V := fun k => Nat.casesOn k x ε
    obtain ⟨χ, h, e⟩ := ih ε'
    rcases Multiset.mem_add.mp h with h | h
    · obtain ⟨ψ, hψ, rfl⟩ := Multiset.mem_map.mp h
      exact (hΓ ⟨ψ, hψ, (evalM_shift Fin.elim0 ε' ψ).mp e⟩).elim
    · have h' : χ = φ.free := Multiset.mem_singleton.mp h
      subst h'
      exact (evalM_free ε' φ).mp e
  | @exs Γ φ t _ ih =>
    intro ε
    obtain ⟨χ, h, e⟩ := ih ε
    rcases Multiset.mem_add.mp h with h | h
    · exact ⟨χ, Multiset.mem_add.mpr (Or.inl h), e⟩
    · have h' : χ = φ/[t] := Multiset.mem_singleton.mp h
      subst h'
      refine ⟨∃¹ φ, Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl)), ?_⟩
      exact (ev_exs Eq mem _ _ _).mpr ⟨exTvRaw.choose Fin.elim0 ε t, (evalM_subst1 ε φ t).mp e⟩

private lemma zfc_sound {V : Type} {mem : V → V → Prop}
    (hZFC : ∀ ψ ∈ 𝗭𝗙𝗖, exEvalRaw.choose Eq mem Fin.elim0 Empty.elim ψ)
    {σ : SetTheorySentence} (h : FFL.Entailment.Provable 𝗭𝗙𝗖 σ) :
    exEvalRaw.choose Eq mem Fin.elim0 Empty.elim σ := by
  have hempty : exEvalRaw.choose Eq mem Fin.elim0 Empty.elim Axiom.empty :=
    hZFC Axiom.empty (Or.inl ZermeloFraenkel.axiom_of_empty_set)
  unfold Axiom.empty at hempty
  obtain ⟨v₀, _⟩ := (ev_exs Eq mem _ _ _).mp hempty
  obtain ⟨pf⟩ := h
  obtain ⟨χ, hχ, he⟩ := deriv_sound pf.derivation (fun _ => v₀)
  obtain ⟨χ0, h0, rfl⟩ := Multiset.mem_map.mp hχ
  rw [evalM_emb] at he
  rcases Multiset.mem_add.mp h0 with h0 | h0
  · have h' : χ0 = σ := Multiset.mem_singleton.mp h0
    subst h'
    exact he
  · obtain ⟨ψ, hψ, rfl⟩ := Multiset.mem_map.mp h0
    exact ((evalRaw_neg Eq mem Fin.elim0 Empty.elim ψ).mp he (hZFC ψ (pf.axioms_mem ψ hψ))).elim

end Helpers

theorem main : H1 → H2 → OMA.R_Constant14_c14_le_432_R1.H1 := by
  intro h1 h2 n _ M
  constructor
  · intro hprov
    apply zf_complete
    intro V mem hV_zf
    obtain ⟨P, hTrans, hL_satZFC⟩ :=
      h1 V mem (fun ψ hψ => (evalRaw_eq_sat mem ψ Fin.elim0).mp (hV_zf ψ hψ))
    have hL_zfc : ∀ ψ ∈ 𝗭𝗙𝗖,
        exEvalRaw.choose Eq (fun a b : {x // P x} => mem a.1 b.1) Fin.elim0 Empty.elim ψ :=
      fun ψ hψ => (evalRaw_eq_sat (fun a b : {x // P x} => mem a.1 b.1) ψ Fin.elim0).mpr (hL_satZFC ψ hψ)
    have hiff := h2 V mem P
      (fun ψ hψ => (evalRaw_eq_sat mem ψ Fin.elim0).mp (hV_zf ψ hψ))
      hTrans
      (fun ψ hψ => hL_satZFC ψ (Or.inl hψ))
      n M
    generalize Constant14.halts M = σ at hprov hiff ⊢
    have hL_σ : exEvalRaw.choose Eq (fun a b : {x // P x} => mem a.1 b.1)
        Fin.elim0 Empty.elim σ := zfc_sound hL_zfc hprov
    exact (evalRaw_eq_sat mem σ Fin.elim0).mpr
      (hiff.mpr ((evalRaw_eq_sat (fun a b : {x // P x} => mem a.1 b.1) σ Fin.elim0).mp hL_σ))
  · intro hprov
    apply zf_complete
    intro V mem hV_zf
    obtain ⟨P, hTrans, hL_satZFC⟩ :=
      h1 V mem (fun ψ hψ => (evalRaw_eq_sat mem ψ Fin.elim0).mp (hV_zf ψ hψ))
    have hL_zfc : ∀ ψ ∈ 𝗭𝗙𝗖,
        exEvalRaw.choose Eq (fun a b : {x // P x} => mem a.1 b.1) Fin.elim0 Empty.elim ψ :=
      fun ψ hψ => (evalRaw_eq_sat (fun a b : {x // P x} => mem a.1 b.1) ψ Fin.elim0).mpr (hL_satZFC ψ hψ)
    have hiff := h2 V mem P
      (fun ψ hψ => (evalRaw_eq_sat mem ψ Fin.elim0).mp (hV_zf ψ hψ))
      hTrans
      (fun ψ hψ => hL_satZFC ψ (Or.inl hψ))
      n M
    generalize Constant14.halts M = σ at hprov hiff ⊢
    have hL_nσ : ¬ exEvalRaw.choose Eq (fun a b : {x // P x} => mem a.1 b.1)
        Fin.elim0 Empty.elim σ :=
      (evalRaw_neg Eq (fun a b : {x // P x} => mem a.1 b.1) Fin.elim0 Empty.elim σ).mp
        (zfc_sound hL_zfc hprov)
    rw [evalRaw_neg]
    intro hV_σ
    exact hL_nσ ((evalRaw_eq_sat (fun a b : {x // P x} => mem a.1 b.1) σ Fin.elim0).mpr
      (hiff.mp ((evalRaw_eq_sat mem σ Fin.elim0).mp hV_σ)))

end OMA.R_Constant14_c14_le_432_R1_H1_R1
