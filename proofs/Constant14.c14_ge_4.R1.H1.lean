import OMAReductions.R_Constant14_c14_ge_4_R1
import Mathlib.Tactic

/-!
# Proof of `Constant14.c14_ge_4.R1.H1` (Sigma-1 Completeness of `Constant14.halts` in `𝗭𝗙𝗖`)

We prove that for every halting two-symbol Turing machine `M` (for arbitrary `n` with `[NeZero n]`),
`FFL.Entailment.Provable 𝗭𝗙𝗖 (Constant14.halts M)`.

1. **Stage 1 (`C14Completeness`):** Gödel's Completeness Theorem for `FFL.FirstOrder.Derivation`
   over `ℒₛₑₜ` via a Henkin maximal consistent witness extension and quotienting by `req` to obtain
   a normal model `(V, mem) ⊨ 𝗭𝗙𝗖`.
2. **Stage 2 (`C14Stage2`):** Semantic evaluation of `Constant14.halts M` in an arbitrary model
   `(V, mem) ⊨ 𝗭𝗙𝗖` using finite induction along the halting execution trace of `M`.
-/

namespace C14Completeness

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open scoped Classical

/- ## 1. Direct Tarski semantics on arbitrary `(V, req, rmem)` -/

def tvRaw {V : Type} {ξ : Type*} {n : ℕ} (e : Fin n → V) (ε : ξ → V) :
    Semiterm ℒₛₑₜ ξ n → V
  | Semiterm.bvar i => e i
  | Semiterm.fvar x => ε x
  | Semiterm.func f _ => (f : Empty).elim

def evalRaw {V : Type} (req rmem : V → V → Prop) {ξ : Type*} :
    ∀ {n : ℕ}, (Fin n → V) → (ξ → V) → Semiformula ℒₛₑₜ ξ n → Prop
  | _, _, _, Semiformula.verum => True
  | _, _, _, Semiformula.falsum => False
  | _, e, ε, Semiformula.rel Language.Set.Rel.eq v => req (tvRaw e ε (v 0)) (tvRaw e ε (v 1))
  | _, e, ε, Semiformula.rel Language.Set.Rel.mem v => rmem (tvRaw e ε (v 0)) (tvRaw e ε (v 1))
  | _, e, ε, Semiformula.nrel Language.Set.Rel.eq v => ¬ req (tvRaw e ε (v 0)) (tvRaw e ε (v 1))
  | _, e, ε, Semiformula.nrel Language.Set.Rel.mem v => ¬ rmem (tvRaw e ε (v 0)) (tvRaw e ε (v 1))
  | _, e, ε, Semiformula.and φ ψ => evalRaw req rmem e ε φ ∧ evalRaw req rmem e ε ψ
  | _, e, ε, Semiformula.or φ ψ => evalRaw req rmem e ε φ ∨ evalRaw req rmem e ε ψ
  | _, e, ε, Semiformula.all φ => ∀ d : V, evalRaw req rmem (d :> e) ε φ
  | _, e, ε, Semiformula.exs φ => ∃ d : V, evalRaw req rmem (d :> e) ε φ

abbrev evalM {V : Type} (mem : V → V → Prop) {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ n) : Prop :=
  evalRaw (V := V) Eq mem e ε φ

lemma evalRaw_neg {V : Type} (req rmem : V → V → Prop) {ξ : Type*} :
    ∀ {n : ℕ} (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ n),
      evalRaw req rmem e ε (∼φ) ↔ ¬ evalRaw req rmem e ε φ
  | _, _, _, Semiformula.verum => by simp [evalRaw, HTilde.hTilde, Tilde.tilde, Semiformula.neg]
  | _, _, _, Semiformula.falsum => by simp [evalRaw, HTilde.hTilde, Tilde.tilde, Semiformula.neg]
  | _, _, _, Semiformula.rel Language.Set.Rel.eq _ => Iff.rfl
  | _, _, _, Semiformula.rel Language.Set.Rel.mem _ => Iff.rfl
  | _, _, _, Semiformula.nrel Language.Set.Rel.eq _ => by
      change _ ↔ ¬ ¬ _; exact not_not.symm
  | _, _, _, Semiformula.nrel Language.Set.Rel.mem _ => by
      change _ ↔ ¬ ¬ _; exact not_not.symm
  | _, e, ε, Semiformula.and φ ψ => by
      change evalRaw req rmem e ε (∼φ) ∨ evalRaw req rmem e ε (∼ψ) ↔
        ¬ (evalRaw req rmem e ε φ ∧ evalRaw req rmem e ε ψ)
      rw [evalRaw_neg req rmem e ε φ, evalRaw_neg req rmem e ε ψ, not_and_or]
  | _, e, ε, Semiformula.or φ ψ => by
      change evalRaw req rmem e ε (∼φ) ∧ evalRaw req rmem e ε (∼ψ) ↔
        ¬ (evalRaw req rmem e ε φ ∨ evalRaw req rmem e ε ψ)
      rw [evalRaw_neg req rmem e ε φ, evalRaw_neg req rmem e ε ψ, not_or]
  | _, e, ε, Semiformula.all φ => by
      change (∃ d, evalRaw req rmem (d :> e) ε (∼φ)) ↔ ¬ ∀ d, evalRaw req rmem (d :> e) ε φ
      simp_rw [evalRaw_neg req rmem _ ε φ]
      exact not_forall.symm
  | _, e, ε, Semiformula.exs φ => by
      change (∀ d, evalRaw req rmem (d :> e) ε (∼φ)) ↔ ¬ ∃ d, evalRaw req rmem (d :> e) ε φ
      simp_rw [evalRaw_neg req rmem _ ε φ]
      exact not_exists.symm

lemma tvRaw_rew {V : Type} {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ}
    (e : Fin n₂ → V) (ε : ξ₂ → V) (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (t : Semiterm ℒₛₑₜ ξ₁ n₁) :
    tvRaw e ε (ω t) = tvRaw (fun i => tvRaw e ε (ω #i)) (fun x => tvRaw e ε (ω &x)) t := by
  cases t with
  | bvar i => rfl
  | fvar x => rfl
  | func f _ => exact (f : Empty).elim

lemma tvRaw_bShift {V : Type} {ξ : Type*} {n : ℕ} (d : V) (e : Fin n → V) (ε : ξ → V)
    (t : Semiterm ℒₛₑₜ ξ n) :
    tvRaw (d :> e) ε (Rew.bShift t) = tvRaw e ε t := by
  cases t with
  | bvar i => rfl
  | fvar x => rfl
  | func f _ => exact (f : Empty).elim

lemma evalRaw_congr {V : Type} (req rmem : V → V → Prop) {ξ : Type*} :
    ∀ {n : ℕ} {e₁ e₂ : Fin n → V} {ε₁ ε₂ : ξ → V} (φ : Semiformula ℒₛₑₜ ξ n),
      e₁ = e₂ → ε₁ = ε₂ → (evalRaw req rmem e₁ ε₁ φ ↔ evalRaw req rmem e₂ ε₂ φ) := by
  intro n e₁ e₂ ε₁ ε₂ φ he hε
  subst he hε; rfl

lemma evalRaw_rew {V : Type} (req rmem : V → V → Prop) {ξ₁ ξ₂ : Type*} :
    ∀ {n₁ n₂ : ℕ} (e : Fin n₂ → V) (ε : ξ₂ → V) (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
      (φ : Semiformula ℒₛₑₜ ξ₁ n₁),
      evalRaw req rmem e ε (ω ▹ φ) ↔
        evalRaw req rmem (fun i => tvRaw e ε (ω #i)) (fun x => tvRaw e ε (ω &x)) φ
  | _, _, _, _, _, Semiformula.verum => Iff.rfl
  | _, _, _, _, _, Semiformula.falsum => Iff.rfl
  | _, _, e, ε, ω, Semiformula.rel Language.Set.Rel.eq v => by
      change req (tvRaw e ε (ω (v 0))) (tvRaw e ε (ω (v 1))) ↔ _
      rw [tvRaw_rew e ε ω (v 0), tvRaw_rew e ε ω (v 1)]; rfl
  | _, _, e, ε, ω, Semiformula.rel Language.Set.Rel.mem v => by
      change rmem (tvRaw e ε (ω (v 0))) (tvRaw e ε (ω (v 1))) ↔ _
      rw [tvRaw_rew e ε ω (v 0), tvRaw_rew e ε ω (v 1)]; rfl
  | _, _, e, ε, ω, Semiformula.nrel Language.Set.Rel.eq v => by
      change ¬ req (tvRaw e ε (ω (v 0))) (tvRaw e ε (ω (v 1))) ↔ _
      rw [tvRaw_rew e ε ω (v 0), tvRaw_rew e ε ω (v 1)]; rfl
  | _, _, e, ε, ω, Semiformula.nrel Language.Set.Rel.mem v => by
      change ¬ rmem (tvRaw e ε (ω (v 0))) (tvRaw e ε (ω (v 1))) ↔ _
      rw [tvRaw_rew e ε ω (v 0), tvRaw_rew e ε ω (v 1)]; rfl
  | _, _, e, ε, ω, Semiformula.and φ ψ =>
      and_congr (evalRaw_rew req rmem e ε ω φ) (evalRaw_rew req rmem e ε ω ψ)
  | _, _, e, ε, ω, Semiformula.or φ ψ =>
      or_congr (evalRaw_rew req rmem e ε ω φ) (evalRaw_rew req rmem e ε ω ψ)
  | _, _, e, ε, ω, Semiformula.all φ => by
      change (∀ d, evalRaw req rmem (d :> e) ε (ω.q ▹ φ)) ↔ _
      refine forall_congr' fun d => (evalRaw_rew req rmem (d :> e) ε ω.q φ).trans ?_
      refine evalRaw_congr req rmem φ ?_ ?_
      · funext i
        cases i using Fin.cases with
        | zero => rfl
        | succ i =>
          change tvRaw (d :> e) ε (Rew.bShift (ω #i)) = tvRaw e ε (ω #i)
          exact tvRaw_bShift d e ε _
      · funext x
        change tvRaw (d :> e) ε (Rew.bShift (ω &x)) = tvRaw e ε (ω &x)
        exact tvRaw_bShift d e ε _
  | _, _, e, ε, ω, Semiformula.exs φ => by
      change (∃ d, evalRaw req rmem (d :> e) ε (ω.q ▹ φ)) ↔ _
      refine exists_congr fun d => (evalRaw_rew req rmem (d :> e) ε ω.q φ).trans ?_
      refine evalRaw_congr req rmem φ ?_ ?_
      · funext i
        cases i using Fin.cases with
        | zero => rfl
        | succ i =>
          change tvRaw (d :> e) ε (Rew.bShift (ω #i)) = tvRaw e ε (ω #i)
          exact tvRaw_bShift d e ε _
      · funext x
        change tvRaw (d :> e) ε (Rew.bShift (ω &x)) = tvRaw e ε (ω &x)
        exact tvRaw_bShift d e ε _

/- ## 2. Basic syntactic properties of `Semiformula` and `Rew` -/

lemma neg_neg_formula {ξ : Type*} : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n), ∼(∼φ) = φ
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

lemma rew_ext {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} {ω₁ ω₂ : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂}
    (hb : ∀ i : Fin n₁, ω₁ #i = ω₂ #i) (hf : ∀ x : ξ₁, ω₁ &x = ω₂ &x) : ω₁ = ω₂ := by
  rcases ω₁ with ⟨f₁, _⟩
  rcases ω₂ with ⟨f₂, _⟩
  congr 1
  funext t
  cases t with
  | bvar i => exact hb i
  | fvar x => exact hf x
  | func f _ => exact (f : Empty).elim

lemma rew_q_comp {ξ₁ ξ₂ ξ₃ : Type*} {n₁ n₂ n₃ : ℕ}
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

lemma rew_comp {ξ₁ ξ₂ ξ₃ : Type*} :
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

lemma rew_id_q {ξ : Type*} (n : ℕ) :
    (Rew.id (L := ℒₛₑₜ) (ξ := ξ) (n := n)).q = Rew.id := by
  apply rew_ext
  · intro i; cases i using Fin.cases <;> rfl
  · intro x; rfl

lemma rew_id_eq {ξ : Type*} : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n), Rew.id ▹ φ = φ
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

lemma rew_term_congr_fv {ξ₁ ξ₂ : Type*} [DecidableEq ξ₁] {n₁ n₂ : ℕ}
    {ω₁ ω₂ : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂} (t : Semiterm ℒₛₑₜ ξ₁ n₁)
    (hb : ∀ i : Fin n₁, ω₁ #i = ω₂ #i)
    (hf : ∀ x ∈ t.freeVariables, ω₁ &x = ω₂ &x) : ω₁ t = ω₂ t := by
  cases t with
  | bvar i => exact hb i
  | fvar x => exact hf x (by simp [Semiterm.freeVariables])
  | func f _ => exact (f : Empty).elim

lemma rew_congr_fv {ξ₁ ξ₂ : Type*} [DecidableEq ξ₁] :
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

def complexity {ξ : Type*} : ∀ {n : ℕ}, Semiformula ℒₛₑₜ ξ n → ℕ
  | _, Semiformula.verum => 0
  | _, Semiformula.falsum => 0
  | _, Semiformula.rel _ _ => 0
  | _, Semiformula.nrel _ _ => 0
  | _, Semiformula.and φ ψ => complexity φ + complexity ψ + 1
  | _, Semiformula.or φ ψ => complexity φ + complexity ψ + 1
  | _, Semiformula.all φ => complexity φ + 1
  | _, Semiformula.exs φ => complexity φ + 1

lemma complexity_neg {ξ : Type*} : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n),
    complexity (∼φ) = complexity φ
  | _, Semiformula.verum => rfl
  | _, Semiformula.falsum => rfl
  | _, Semiformula.rel _ _ => rfl
  | _, Semiformula.nrel _ _ => rfl
  | _, Semiformula.and φ ψ => by
      change complexity (∼φ) + complexity (∼ψ) + 1 = complexity φ + complexity ψ + 1
      rw [complexity_neg φ, complexity_neg ψ]
  | _, Semiformula.or φ ψ => by
      change complexity (∼φ) + complexity (∼ψ) + 1 = complexity φ + complexity ψ + 1
      rw [complexity_neg φ, complexity_neg ψ]
  | _, Semiformula.all φ => by
      change complexity (∼φ) + 1 = complexity φ + 1
      rw [complexity_neg φ]
  | _, Semiformula.exs φ => by
      change complexity (∼φ) + 1 = complexity φ + 1
      rw [complexity_neg φ]

lemma complexity_rew {ξ₁ ξ₂ : Type*} :
    ∀ {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (φ : Semiformula ℒₛₑₜ ξ₁ n₁),
      complexity (ω ▹ φ) = complexity φ
  | _, _, _, Semiformula.verum => rfl
  | _, _, _, Semiformula.falsum => rfl
  | _, _, _, Semiformula.rel _ _ => rfl
  | _, _, _, Semiformula.nrel _ _ => rfl
  | _, _, ω, Semiformula.and φ ψ => by
      change complexity (ω ▹ φ) + complexity (ω ▹ ψ) + 1 = complexity φ + complexity ψ + 1
      rw [complexity_rew ω φ, complexity_rew ω ψ]
  | _, _, ω, Semiformula.or φ ψ => by
      change complexity (ω ▹ φ) + complexity (ω ▹ ψ) + 1 = complexity φ + complexity ψ + 1
      rw [complexity_rew ω φ, complexity_rew ω ψ]
  | _, _, ω, Semiformula.all φ => by
      change complexity (ω.q ▹ φ) + 1 = complexity φ + 1
      rw [complexity_rew ω.q φ]
  | _, _, ω, Semiformula.exs φ => by
      change complexity (ω.q ▹ φ) + 1 = complexity φ + 1
      rw [complexity_rew ω.q φ]

lemma fv_lt_fvSup {n : ℕ} (φ : Semiproposition ℒₛₑₜ n) {x : ℕ} (hx : x ∈ φ.freeVariables) :
    x < φ.fvSup := by
  unfold Semiformula.fvSup
  have hne : φ.freeVariables.Nonempty := ⟨x, hx⟩
  obtain ⟨m, hm⟩ := Finset.max_of_nonempty hne
  rw [hm]
  exact Nat.lt_succ_of_le (Finset.le_max_of_eq hx hm)

lemma rew_emb_q (m : ℕ) :
    (Rew.emb (L := ℒₛₑₜ) (o := Empty) (ξ := ℕ) (n := m)).q = Rew.emb := by
  apply rew_ext
  · intro i; cases i using Fin.cases <;> rfl
  · intro x; exact x.elim

lemma freeVariables_emb {n : ℕ} (φ : Semisentence ℒₛₑₜ n) :
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

lemma freeVariables_neg {n : ℕ} (φ : Semiproposition ℒₛₑₜ n) :
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

lemma neg_map {α : Type*} [Tilde α] (A : Multiset α) : ∼A = A.map (∼·) := rfl
lemma atom_eq {α : Type*} (a : α) : ⦃a⦄ = {a} := rfl
lemma neg_exs (ψ : Semiproposition ℒₛₑₜ 1) : ∼(∃¹ ψ) = ∀¹ (∼ψ) := rfl
lemma neg_all (ψ : Semiproposition ℒₛₑₜ 1) : ∼(∀¹ ψ) = ∃¹ (∼ψ) := rfl
lemma neg_and (φ ψ : Proposition ℒₛₑₜ) : ∼(φ ⋏ ψ) = ∼φ ⋎ ∼ψ := rfl
lemma neg_or (φ ψ : Proposition ℒₛₑₜ) : ∼(φ ⋎ ψ) = ∼φ ⋏ ∼ψ := rfl

/- ## 3. Derivation constructors: renaming, fresh universal generalization, excluded middle -/

def fvarMap (f : ℕ → ℕ) {n : ℕ} : SyntacticRew ℒₛₑₜ n n :=
  Rew.map id f

lemma fvarMap_q (f : ℕ → ℕ) (n : ℕ) : (fvarMap f (n := n)).q = fvarMap f (n := n + 1) := by
  apply rew_ext
  · intro i; cases i using Fin.cases <;> rfl
  · intro x; rfl

noncomputable def deriv_fvarMap (f : ℕ → ℕ) {Γ : Sequent ℒₛₑₜ} (d : Derivation Γ) :
    Derivation (Γ.map (fvarMap f ▹ ·)) := by
  induction d generalizing f with
  | identity r v =>
    have heq : (⦃Semiformula.rel r v, Semiformula.nrel r v⦄ : Sequent ℒₛₑₜ).map (fvarMap f ▹ ·) =
        ⦃Semiformula.rel r (fvarMap f ∘ v), Semiformula.nrel r (fvarMap f ∘ v)⦄ := by
      simp [atom_eq]; rfl
    rw [heq]
    exact Derivation.identity r (fvarMap f ∘ v)
  | @cut Γ φ Δ d1 d2 ih1 ih2 =>
    have h1 := ih1 f
    have h2 := ih2 f
    simp only [Multiset.map_add, atom_eq, Multiset.map_singleton] at h1 h2 ⊢
    have hneg : fvarMap f ▹ (∼φ) = ∼(fvarMap f ▹ φ) := (Semiformula.rew (fvarMap f)).map_neg' φ
    rw [hneg] at h2
    exact Derivation.cut h1 h2
  | contraction d hsub ih =>
    exact Derivation.contraction (ih f) (Multiset.map_subset_map hsub)
  | verum =>
    have heq : (⦃⊤⦄ : Sequent ℒₛₑₜ).map (fvarMap f ▹ ·) = ⦃⊤⦄ := by simp [atom_eq]; rfl
    rw [heq]
    exact Derivation.verum
  | or d ih =>
    have h := ih f
    simp only [Multiset.map_add, atom_eq, Multiset.map_singleton] at h ⊢
    exact Derivation.or h
  | and d1 d2 ih1 ih2 =>
    have h1 := ih1 f
    have h2 := ih2 f
    simp only [Multiset.map_add, atom_eq, Multiset.map_singleton] at h1 h2 ⊢
    exact Derivation.and h1 h2
  | @all Γ φ d ih =>
    let f' : ℕ → ℕ := Nat.cases 0 (fun k => f k + 1)
    have h := ih f'
    simp only [Multiset.map_add, atom_eq, Multiset.map_singleton] at h ⊢
    have hshift : Γ⁺.map (fvarMap f' ▹ ·) = Rewriting.shifts (Γ.map (fvarMap f ▹ ·)) := by
      simp only [Rewriting.shifts, Multiset.map_map]
      congr 1; funext ψ
      change fvarMap f' ▹ (Rew.shift ▹ ψ) = Rew.shift ▹ (fvarMap f ▹ ψ)
      rw [rew_comp, rew_comp]
      exact congrArg (fun ω : SyntacticRew ℒₛₑₜ 0 0 => ω ▹ ψ)
        (rew_ext (fun i => Fin.elim0 i) (fun _ => rfl))
    have hfree : fvarMap f' ▹ φ.free = (fvarMap f ▹ φ).free := by
      change fvarMap f' ▹ (Rew.free ▹ φ) = Rew.free ▹ (fvarMap f ▹ φ)
      rw [rew_comp, rew_comp]
      exact congrArg (fun ω : SyntacticRew ℒₛₑₜ 1 0 => ω ▹ φ) (rew_ext (fun i => by
        have hi : i = 0 := Fin.ext (by omega); subst hi; rfl) (fun _ => rfl))
    rw [hshift, hfree] at h
    have hall : fvarMap f ▹ (∀¹ φ) = ∀¹ (fvarMap f ▹ φ) := by
      change ∀¹ ((fvarMap f).q ▹ φ) = ∀¹ (fvarMap f ▹ φ)
      rw [fvarMap_q]
    rw [hall]
    exact Derivation.all h
  | @exs Γ φ t d ih =>
    have h := ih f
    simp only [Multiset.map_add, atom_eq, Multiset.map_singleton] at h ⊢
    have hsubst : fvarMap f ▹ (φ/[t]) = (fvarMap f ▹ φ)/[fvarMap f t] := by
      change fvarMap f ▹ (Rew.subst ![t] ▹ φ) = Rew.subst ![fvarMap f t] ▹ (fvarMap f ▹ φ)
      rw [rew_comp, rew_comp]
      exact congrArg (fun ω : SyntacticRew ℒₛₑₜ 1 0 => ω ▹ φ) (rew_ext (fun i => by
        have hi : i = 0 := Subsingleton.elim i 0; subst hi; rfl) (fun _ => rfl))
    rw [hsubst] at h
    have hexs : fvarMap f ▹ (∃¹ φ) = ∃¹ (fvarMap f ▹ φ) := by
      change ∃¹ ((fvarMap f).q ▹ φ) = ∃¹ (fvarMap f ▹ φ)
      rw [fvarMap_q]
    rw [hexs]
    exact Derivation.exs h

noncomputable def deriv_all_of_fresh {Γ : Sequent ℒₛₑₜ} {φ : Semiproposition ℒₛₑₜ 1} {c : ℕ}
    (hΓ : ∀ ψ ∈ Γ, c ∉ ψ.freeVariables) (hφ : c ∉ φ.freeVariables)
    (d : Derivation (Γ + ⦃φ/[&c]⦄)) : Derivation (Γ + ⦃∀¹ φ⦄) := by
  let f : ℕ → ℕ := fun k => if k = c then 0 else k + 1
  have hd := deriv_fvarMap f d
  simp only [Multiset.map_add, atom_eq, Multiset.map_singleton] at hd
  have hΓ' : Γ.map (fvarMap f ▹ ·) = Γ⁺ := by
    unfold Rewriting.shifts
    apply Multiset.map_congr rfl
    intro ψ hψ
    refine rew_congr_fv ψ (fun i => Fin.elim0 i) ?_
    intro x hx
    have hxc : x ≠ c := fun h => hΓ ψ hψ (h ▸ hx)
    change &(if x = c then 0 else x + 1) = &(x + 1)
    rw [if_neg hxc]
  have hφ' : fvarMap f ▹ (φ/[&c]) = φ.free := by
    change fvarMap f ▹ (Rew.subst ![&c] ▹ φ) = Rew.free ▹ φ
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
  exact Derivation.all hd

noncomputable def deriv_em : ∀ (φ : Proposition ℒₛₑₜ), Derivation ⦃∼φ, φ⦄ := by
  intro φ
  suffices h : ∀ k : ℕ, ∀ φ : Proposition ℒₛₑₜ, complexity φ ≤ k → Derivation ⦃∼φ, φ⦄ from
    h (complexity φ) φ le_rfl
  intro k
  induction k with
  | zero =>
    intro φ hk
    cases φ with
    | verum =>
      exact Derivation.contraction Derivation.verum (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        exact Or.inr hx)
    | falsum =>
      exact Derivation.contraction Derivation.verum (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        exact Or.inl hx)
    | rel r v =>
      exact Derivation.contraction (Derivation.identity r v) (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl rfl)
    | nrel r v =>
      exact Derivation.identity r v
    | and _ _ => simp [complexity] at hk
    | or _ _ => simp [complexity] at hk
    | all _ => simp [complexity] at hk
    | exs _ => simp [complexity] at hk
  | succ k ih =>
    intro φ hk
    cases φ with
    | verum =>
      exact Derivation.contraction Derivation.verum (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        exact Or.inr hx)
    | falsum =>
      exact Derivation.contraction Derivation.verum (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        exact Or.inl hx)
    | rel r v =>
      exact Derivation.contraction (Derivation.identity r v) (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl rfl)
    | nrel r v => exact Derivation.identity r v
    | and ψ₁ ψ₂ =>
      simp only [complexity] at hk
      have d1 : Derivation (⦃∼ψ₁, ∼ψ₂⦄ + ⦃ψ₁⦄) :=
        Derivation.contraction (ih ψ₁ (by omega)) (by
          intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr rfl)
      have d2 : Derivation (⦃∼ψ₁, ∼ψ₂⦄ + ⦃ψ₂⦄) :=
        Derivation.contraction (ih ψ₂ (by omega)) (by
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
      exact Derivation.contraction dor (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl rfl)
    | or ψ₁ ψ₂ =>
      simp only [complexity] at hk
      have d1 : Derivation (⦃ψ₁, ψ₂⦄ + ⦃∼ψ₁⦄) :=
        Derivation.contraction (ih ψ₁ (by omega)) (by
          intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl (Or.inl rfl))
      have d2 : Derivation (⦃ψ₁, ψ₂⦄ + ⦃∼ψ₂⦄) :=
        Derivation.contraction (ih ψ₂ (by omega)) (by
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
      exact Derivation.or dand
    | all ψ =>
      simp only [complexity] at hk
      have hcomp : complexity ψ.free ≤ k := by
        change complexity (Rew.free ▹ ψ) ≤ k
        rw [complexity_rew]; omega
      have d0 : Derivation ⦃∼ψ.free, ψ.free⦄ := ih ψ.free hcomp
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
      exact Derivation.all d3
    | exs ψ =>
      simp only [complexity] at hk
      have hcomp : complexity (∼ψ).free ≤ k := by
        change complexity (Rew.free ▹ (∼ψ)) ≤ k
        rw [complexity_rew, complexity_neg]; omega
      have d0 : Derivation ⦃∼(∼ψ).free, (∼ψ).free⦄ := ih (∼ψ).free hcomp
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
      exact Derivation.contraction d4 (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl rfl)

/- ## 4. Countability of `Proposition ℒₛₑₜ` -/

def encodeTerm {n : ℕ} : Semiterm ℒₛₑₜ ℕ n → ℕ
  | Semiterm.bvar i => Nat.pair 0 i.val
  | Semiterm.fvar x => Nat.pair 1 x
  | Semiterm.func f _ => (f : Empty).elim

lemma encodeTerm_injective {n : ℕ} : Function.Injective (encodeTerm (n := n)) := by
  intro t₁ t₂ h
  cases t₁ with
  | func f _ => exact (f : Empty).elim
  | bvar i =>
    cases t₂ with
    | func f _ => exact (f : Empty).elim
    | bvar j =>
      simp only [encodeTerm] at h
      have h1 := congrArg (fun k => (Nat.unpair k).2) h
      simp only [Nat.unpair_pair] at h1
      exact congrArg Semiterm.bvar (Fin.ext h1)
    | fvar y =>
      simp only [encodeTerm] at h
      have h1 := congrArg (fun k => (Nat.unpair k).1) h
      simp only [Nat.unpair_pair] at h1
      omega
  | fvar x =>
    cases t₂ with
    | func f _ => exact (f : Empty).elim
    | bvar j =>
      simp only [encodeTerm] at h
      have h1 := congrArg (fun k => (Nat.unpair k).1) h
      simp only [Nat.unpair_pair] at h1
      omega
    | fvar y =>
      simp only [encodeTerm] at h
      have h1 := congrArg (fun k => (Nat.unpair k).2) h
      simp only [Nat.unpair_pair] at h1
      exact congrArg Semiterm.fvar h1

def encodeFormula : ∀ {n : ℕ}, Semiformula ℒₛₑₜ ℕ n → ℕ
  | _, Semiformula.verum => Nat.pair 0 0
  | _, Semiformula.falsum => Nat.pair 1 0
  | _, Semiformula.rel Language.Set.Rel.eq v => Nat.pair 2 (Nat.pair (encodeTerm (v 0)) (encodeTerm (v 1)))
  | _, Semiformula.rel Language.Set.Rel.mem v => Nat.pair 3 (Nat.pair (encodeTerm (v 0)) (encodeTerm (v 1)))
  | _, Semiformula.nrel Language.Set.Rel.eq v => Nat.pair 4 (Nat.pair (encodeTerm (v 0)) (encodeTerm (v 1)))
  | _, Semiformula.nrel Language.Set.Rel.mem v => Nat.pair 5 (Nat.pair (encodeTerm (v 0)) (encodeTerm (v 1)))
  | _, Semiformula.and φ ψ => Nat.pair 6 (Nat.pair (encodeFormula φ) (encodeFormula ψ))
  | _, Semiformula.or φ ψ => Nat.pair 7 (Nat.pair (encodeFormula φ) (encodeFormula ψ))
  | _, Semiformula.all φ => Nat.pair 8 (encodeFormula φ)
  | _, Semiformula.exs φ => Nat.pair 9 (encodeFormula φ)

lemma vec2_eq_of_encode {n : ℕ} {v₁ v₂ : Fin 2 → Semiterm ℒₛₑₜ ℕ n}
    (h : Nat.pair (encodeTerm (v₁ 0)) (encodeTerm (v₁ 1)) =
      Nat.pair (encodeTerm (v₂ 0)) (encodeTerm (v₂ 1))) : v₁ = v₂ := by
  have h0 : encodeTerm (v₁ 0) = encodeTerm (v₂ 0) := by
    have := congrArg (fun k => (Nat.unpair k).1) h; simpa [Nat.unpair_pair] using this
  have h1 : encodeTerm (v₁ 1) = encodeTerm (v₂ 1) := by
    have := congrArg (fun k => (Nat.unpair k).2) h; simpa [Nat.unpair_pair] using this
  funext i
  fin_cases i
  · exact encodeTerm_injective h0
  · exact encodeTerm_injective h1

def formulaTag {n : ℕ} : Semiformula ℒₛₑₜ ℕ n → ℕ
  | Semiformula.verum => 0
  | Semiformula.falsum => 1
  | Semiformula.rel Language.Set.Rel.eq _ => 2
  | Semiformula.rel Language.Set.Rel.mem _ => 3
  | Semiformula.nrel Language.Set.Rel.eq _ => 4
  | Semiformula.nrel Language.Set.Rel.mem _ => 5
  | Semiformula.and _ _ => 6
  | Semiformula.or _ _ => 7
  | Semiformula.all _ => 8
  | Semiformula.exs _ => 9

lemma unpair_fst_encodeFormula {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) :
    (Nat.unpair (encodeFormula φ)).1 = formulaTag φ := by
  cases φ with
  | rel r _ => cases r <;> simp [encodeFormula, formulaTag]
  | nrel r _ => cases r <;> simp [encodeFormula, formulaTag]
  | _ => simp [encodeFormula, formulaTag]

lemma encodeFormula_injective : ∀ {n : ℕ}, Function.Injective (encodeFormula (n := n)) := by
  intro n φ₁ φ₂ h
  induction φ₁ with
  | verum =>
    have ht := congrArg (fun k => (Nat.unpair k).1) h
    rw [unpair_fst_encodeFormula, unpair_fst_encodeFormula] at ht
    cases φ₂ with
    | verum => rfl
    | rel r _ => cases r <;> simp [formulaTag] at ht
    | nrel r _ => cases r <;> simp [formulaTag] at ht
    | _ => simp [formulaTag] at ht
  | falsum =>
    have ht := congrArg (fun k => (Nat.unpair k).1) h
    rw [unpair_fst_encodeFormula, unpair_fst_encodeFormula] at ht
    cases φ₂ with
    | falsum => rfl
    | rel r _ => cases r <;> simp [formulaTag] at ht
    | nrel r _ => cases r <;> simp [formulaTag] at ht
    | _ => simp [formulaTag] at ht
  | rel r₁ v₁ =>
    have ht := congrArg (fun k => (Nat.unpair k).1) h
    rw [unpair_fst_encodeFormula, unpair_fst_encodeFormula] at ht
    cases r₁ with
    | eq =>
      cases φ₂ with
      | rel r₂ v₂ =>
        cases r₂ with
        | eq =>
          have h2 := congrArg (fun k => (Nat.unpair k).2) h
          simp only [encodeFormula, Nat.unpair_pair] at h2
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
          simp only [encodeFormula, Nat.unpair_pair] at h2
          rw [vec2_eq_of_encode h2]
      | nrel r₂ _ => cases r₂ <;> simp [formulaTag] at ht
      | _ => simp [formulaTag] at ht
  | nrel r₁ v₁ =>
    have ht := congrArg (fun k => (Nat.unpair k).1) h
    rw [unpair_fst_encodeFormula, unpair_fst_encodeFormula] at ht
    cases r₁ with
    | eq =>
      cases φ₂ with
      | nrel r₂ v₂ =>
        cases r₂ with
        | eq =>
          have h2 := congrArg (fun k => (Nat.unpair k).2) h
          simp only [encodeFormula, Nat.unpair_pair] at h2
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
          simp only [encodeFormula, Nat.unpair_pair] at h2
          rw [vec2_eq_of_encode h2]
      | rel r₂ _ => cases r₂ <;> simp [formulaTag] at ht
      | _ => simp [formulaTag] at ht
  | and φ₁ ψ₁ ih1 ih2 =>
    have ht := congrArg (fun k => (Nat.unpair k).1) h
    rw [unpair_fst_encodeFormula, unpair_fst_encodeFormula] at ht
    cases φ₂ with
    | and φ₂ ψ₂ =>
      have h2 := congrArg (fun k => (Nat.unpair k).2) h
      simp only [encodeFormula, Nat.unpair_pair] at h2
      have ha : encodeFormula φ₁ = encodeFormula φ₂ := by
        have := congrArg (fun k => (Nat.unpair k).1) h2; simpa [Nat.unpair_pair] using this
      have hb : encodeFormula ψ₁ = encodeFormula ψ₂ := by
        have := congrArg (fun k => (Nat.unpair k).2) h2; simpa [Nat.unpair_pair] using this
      rw [ih1 ha, ih2 hb]
    | rel r _ => cases r <;> simp [formulaTag] at ht
    | nrel r _ => cases r <;> simp [formulaTag] at ht
    | _ => simp [formulaTag] at ht
  | or φ₁ ψ₁ ih1 ih2 =>
    have ht := congrArg (fun k => (Nat.unpair k).1) h
    rw [unpair_fst_encodeFormula, unpair_fst_encodeFormula] at ht
    cases φ₂ with
    | or φ₂ ψ₂ =>
      have h2 := congrArg (fun k => (Nat.unpair k).2) h
      simp only [encodeFormula, Nat.unpair_pair] at h2
      have ha : encodeFormula φ₁ = encodeFormula φ₂ := by
        have := congrArg (fun k => (Nat.unpair k).1) h2; simpa [Nat.unpair_pair] using this
      have hb : encodeFormula ψ₁ = encodeFormula ψ₂ := by
        have := congrArg (fun k => (Nat.unpair k).2) h2; simpa [Nat.unpair_pair] using this
      rw [ih1 ha, ih2 hb]
    | rel r _ => cases r <;> simp [formulaTag] at ht
    | nrel r _ => cases r <;> simp [formulaTag] at ht
    | _ => simp [formulaTag] at ht
  | all φ₁ ih =>
    have ht := congrArg (fun k => (Nat.unpair k).1) h
    rw [unpair_fst_encodeFormula, unpair_fst_encodeFormula] at ht
    cases φ₂ with
    | all φ₂ =>
      have h2 := congrArg (fun k => (Nat.unpair k).2) h
      simp only [encodeFormula, Nat.unpair_pair] at h2
      rw [ih h2]
    | rel r _ => cases r <;> simp [formulaTag] at ht
    | nrel r _ => cases r <;> simp [formulaTag] at ht
    | _ => simp [formulaTag] at ht
  | exs φ₁ ih =>
    have ht := congrArg (fun k => (Nat.unpair k).1) h
    rw [unpair_fst_encodeFormula, unpair_fst_encodeFormula] at ht
    cases φ₂ with
    | exs φ₂ =>
      have h2 := congrArg (fun k => (Nat.unpair k).2) h
      simp only [encodeFormula, Nat.unpair_pair] at h2
      rw [ih h2]
    | rel r _ => cases r <;> simp [formulaTag] at ht
    | nrel r _ => cases r <;> simp [formulaTag] at ht
    | _ => simp [formulaTag] at ht

lemma exists_enum_prop : ∃ enum : ℕ → Proposition ℒₛₑₜ, Function.Surjective enum := by
  have : Countable (Proposition ℒₛₑₜ) := Function.Injective.countable encodeFormula_injective
  have : Nonempty (Proposition ℒₛₑₜ) := ⟨Semiformula.verum⟩
  exact exists_surjective_nat (Proposition ℒₛₑₜ)

/- ## 5. Henkin maximal consistent set construction -/

def Consistent (S : Set (Proposition ℒₛₑₜ)) : Prop :=
  ∀ A : Multiset (Proposition ℒₛₑₜ), (∀ φ ∈ A, φ ∈ S) → ¬ Nonempty (Derivation (∼A))

lemma consistent_mono {S₁ S₂ : Set (Proposition ℒₛₑₜ)} (h : S₁ ⊆ S₂) (h2 : Consistent S₂) :
    Consistent S₁ :=
  fun A hA => h2 A (fun φ hφ => h (hA φ hφ))

lemma consistent_base {T : Theory ℒₛₑₜ} {σ : Sentence ℒₛₑₜ}
    (hnp : ¬ FFL.Entailment.Provable T σ) :
    Consistent ({∼(Rewriting.emb σ)} ∪ {p | ∃ ψ ∈ T, p = Rewriting.emb ψ}) := by
  intro A hA ⟨d⟩
  have hsplit : ∃ axms : Multiset (Sentence ℒₛₑₜ),
      (∀ ψ ∈ axms, ψ ∈ T) ∧ ∼A ⊆ (⦃σ⦄ + ∼axms).map Rewriting.emb := by
    clear d
    induction A using Multiset.induction_on with
    | empty =>
      refine ⟨0, by simp, by simp [neg_map]⟩
    | cons a s ih =>
      obtain ⟨axms, hax, hsub⟩ := ih (fun φ hφ => hA φ (Multiset.mem_cons_of_mem hφ))
      have ha := hA a (Multiset.mem_cons_self a s)
      rcases ha with rfl | ⟨ψ, hψT, rfl⟩
      · refine ⟨axms, hax, ?_⟩
        intro x hx
        rw [neg_map, Multiset.map_cons, Multiset.mem_cons] at hx
        rcases hx with rfl | hxs
        · rw [neg_neg_formula]
          rw [Multiset.map_add, atom_eq, Multiset.map_singleton, Multiset.mem_add]
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

lemma consistent_union_witness {S : Set (Proposition ℒₛₑₜ)} {ψ : Semiproposition ℒₛₑₜ 1} {c : ℕ}
    (hcon : Consistent (S ∪ {∃¹ ψ}))
    (hfreshS : ∀ φ ∈ S, c ∉ φ.freeVariables)
    (hfreshψ : c ∉ ψ.freeVariables) :
    Consistent (S ∪ {∃¹ ψ, ψ/[&c]}) := by
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
  have d2 : Derivation ((∼B + ⦃∀¹ (∼ψ)⦄) + ⦃∀¹ (∼ψ)⦄) :=
    deriv_all_of_fresh hfresh_ctx hfresh_negψ d1
  have d3 : Derivation (∼((∃¹ ψ) ::ₘ B)) := by
    refine Derivation.contraction d2 ?_
    intro x hx
    simp only [Multiset.mem_add, atom_eq, Multiset.mem_singleton] at hx
    rw [neg_map, Multiset.map_cons, Multiset.mem_cons]
    rcases hx with (h1 | rfl) | rfl
    · exact Or.inr h1
    · exact Or.inl (neg_exs ψ).symm
    · exact Or.inl (neg_exs ψ).symm
  refine hcon ((∃¹ ψ) ::ₘ B) ?_ ⟨d3⟩
  intro x hx
  rcases Multiset.mem_cons.mp hx with rfl | hxB
  · exact Or.inr rfl
  · exact Or.inl (hB_mem x hxB)

noncomputable def henkinExtra (S₀ : Set (Proposition ℒₛₑₜ)) (enum : ℕ → Proposition ℒₛₑₜ) :
    ℕ → Finset (Proposition ℒₛₑₜ)
  | 0 => ∅
  | k + 1 =>
    let E := henkinExtra S₀ enum k
    let φ := enum k
    if Consistent (S₀ ∪ (E : Set (Proposition ℒₛₑₜ)) ∪ {φ}) then
      match φ with
      | Semiformula.exs ψ =>
        let c := max ψ.fvSup (E.sup Semiformula.fvSup)
        insert (ψ/[&c]) (insert (Semiformula.exs ψ) E)
      | _ => insert φ E
    else E

lemma henkinExtra_mono (S₀ : Set (Proposition ℒₛₑₜ)) (enum : ℕ → Proposition ℒₛₑₜ) (k : ℕ) :
    henkinExtra S₀ enum k ⊆ henkinExtra S₀ enum (k + 1) := by
  rw [henkinExtra]
  dsimp only
  split_ifs
  · intro x hx
    cases enum k <;> simp [hx]
  · exact Finset.Subset.refl _

lemma henkinExtra_mono_le (S₀ : Set (Proposition ℒₛₑₜ)) (enum : ℕ → Proposition ℒₛₑₜ)
    {j k : ℕ} (h : j ≤ k) :
    henkinExtra S₀ enum j ⊆ henkinExtra S₀ enum k := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (henkinExtra_mono S₀ enum _)

lemma henkin_consistent (S₀ : Set (Proposition ℒₛₑₜ)) (enum : ℕ → Proposition ℒₛₑₜ)
    (hS₀_con : Consistent S₀) (hS₀_closed : ∀ φ ∈ S₀, φ.freeVariables = ∅) :
    ∀ k : ℕ, Consistent (S₀ ∪ (henkinExtra S₀ enum k : Set (Proposition ℒₛₑₜ))) := by
  intro k
  induction k with
  | zero =>
    simpa [henkinExtra] using hS₀_con
  | succ k ih =>
    unfold henkinExtra
    dsimp only
    split_ifs with hcon
    · cases hφ : enum k with
      | exs ψ =>
        rw [hφ] at hcon
        set E := henkinExtra S₀ enum k
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

/- ## 6. Properties of the maximal consistent Henkin set `S` and Term/Quotient Model -/

lemma deriv_neg_elim {S : Set (Proposition ℒₛₑₜ)} (hcon : Consistent S)
    {φ : Proposition ℒₛₑₜ} (hmax : ∀ ψ, Consistent (S ∪ {ψ}) → ψ ∈ S) :
    φ ∈ S ↔ ∼φ ∉ S := by
  constructor
  · intro hφ hnφ
    exact hcon ⦃∼φ, φ⦄ (by
      intro x hx
      simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
      ⟨Derivation.contraction (deriv_em φ) (by
        intro x hx
        simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton,
          neg_map, Multiset.map_add, Multiset.map_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (neg_neg_formula _).symm)⟩
  · intro hnφ
    by_contra hφ
    have h1 : ¬ Consistent (S ∪ {φ}) := fun hc => hφ (hmax φ hc)
    have h2 : ¬ Consistent (S ∪ {∼φ}) := fun hc => hnφ (hmax (∼φ) hc)
    unfold Consistent at h1 h2
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
    refine hcon (B₂ + B₁) ?_ ⟨by simpa [neg_map] using dcut⟩
    intro x hx
    rcases Multiset.mem_add.mp hx with h | h
    · exact (Multiset.mem_filter.mp h).2
    · exact (Multiset.mem_filter.mp h).2

lemma mem_of_deriv {S : Set (Proposition ℒₛₑₜ)} (hcon : Consistent S)
    (hmax : ∀ ψ, Consistent (S ∪ {ψ}) → ψ ∈ S)
    {A : Multiset (Proposition ℒₛₑₜ)} (hA : ∀ ψ ∈ A, ψ ∈ S)
    {φ : Proposition ℒₛₑₜ} (d : Derivation (∼A + ⦃φ⦄)) : φ ∈ S := by
  rw [deriv_neg_elim hcon hmax]
  intro hnφ
  refine hcon ((∼φ) ::ₘ A) ?_ ⟨?_⟩
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

theorem completeness_raw {T : Theory ℒₛₑₜ} {σ : Sentence ℒₛₑₜ}
    (hnp : ¬ FFL.Entailment.Provable T σ) :
    ∃ (req rmem : ℕ → ℕ → Prop),
      (∀ ψ ∈ T, evalRaw req rmem Fin.elim0 id (Rewriting.emb ψ)) ∧
      ¬ evalRaw req rmem Fin.elim0 id (Rewriting.emb σ) := by
  let S₀ : Set (Proposition ℒₛₑₜ) :=
    {∼(Rewriting.emb σ)} ∪ {p | ∃ ψ ∈ T, p = Rewriting.emb ψ}
  have hS₀_con : Consistent S₀ := consistent_base hnp
  have hS₀_closed : ∀ φ ∈ S₀, φ.freeVariables = ∅ := by
    intro φ hφ
    rcases hφ with rfl | ⟨ψ, _, rfl⟩
    · rw [freeVariables_neg]; exact freeVariables_emb σ
    · exact freeVariables_emb ψ
  obtain ⟨enum, henum⟩ := exists_enum_prop
  let Sk : ℕ → Set (Proposition ℒₛₑₜ) := fun k => S₀ ∪ (henkinExtra S₀ enum k : Set _)
  let S : Set (Proposition ℒₛₑₜ) := ⋃ k : ℕ, Sk k
  have hSk_con : ∀ k, Consistent (Sk k) := henkin_consistent S₀ enum hS₀_con hS₀_closed
  have hS_con : Consistent S := by
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
    exact hSk_con N A hN hd
  have hS_max : ∀ φ : Proposition ℒₛₑₜ, Consistent (S ∪ {φ}) → φ ∈ S := by
    intro φ hcon
    obtain ⟨k, rfl⟩ := henum φ
    have hsub : Sk k ∪ {enum k} ⊆ S ∪ {enum k} := by
      intro x hx
      rcases hx with h | h
      · exact Or.inl (Set.mem_iUnion.mpr ⟨k, h⟩)
      · exact Or.inr h
    have hconk : Consistent (Sk k ∪ {enum k}) := consistent_mono hsub hcon
    refine Set.mem_iUnion.mpr ⟨k + 1, Or.inr ?_⟩
    show enum k ∈ henkinExtra S₀ enum (k + 1)
    unfold henkinExtra
    dsimp only
    rw [if_pos hconk]
    cases enum k <;> simp
  have hS_witness : ∀ ψ : Semiproposition ℒₛₑₜ 1, (∃¹ ψ) ∈ S → ∃ c : ℕ, ψ/[&c] ∈ S := by
    intro ψ hmem
    obtain ⟨k, hk⟩ := henum (∃¹ ψ)
    have hconk : Consistent (Sk k ∪ {enum k}) := by
      rw [hk]
      refine consistent_mono ?_ hS_con
      intro x hx
      rcases hx with h | rfl
      · exact Set.mem_iUnion.mpr ⟨k, h⟩
      · exact hmem
    refine ⟨max ψ.fvSup ((henkinExtra S₀ enum k).sup Semiformula.fvSup),
      Set.mem_iUnion.mpr ⟨k + 1, Or.inr ?_⟩⟩
    show ψ/[&_] ∈ henkinExtra S₀ enum (k + 1)
    rw [henkinExtra]
    dsimp only
    rw [if_pos hconk, hk]
    simp
  have hS_neg : ∀ φ, φ ∈ S ↔ ∼φ ∉ S := fun _ => deriv_neg_elim hS_con hS_max
  have hS_verum : (⊤ : Proposition ℒₛₑₜ) ∈ S :=
    mem_of_deriv hS_con hS_max (A := 0) (by simp) (by
      have h0 : ∼(0 : Multiset (Proposition ℒₛₑₜ)) + ⦃⊤⦄ = ⦃⊤⦄ := by simp [neg_map]
      rw [h0]; exact Derivation.verum)
  have hS_falsum : (⊥ : Proposition ℒₛₑₜ) ∉ S := by
    intro h
    exact (hS_neg ⊤).mp hS_verum h
  have hS_and : ∀ φ ψ : Proposition ℒₛₑₜ, (φ ⋏ ψ) ∈ S ↔ φ ∈ S ∧ ψ ∈ S := by
    intro φ ψ
    constructor
    · intro h
      have h1 : φ ∈ S := mem_of_deriv hS_con hS_max (A := ⦃φ ⋏ ψ⦄) (by simpa [atom_eq]) (by
        have d : Derivation (⦃φ⦄ + ⦃∼φ, ∼ψ⦄) :=
          Derivation.contraction (deriv_em φ) (by
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
          Derivation.contraction (deriv_em ψ) (by
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
      exact mem_of_deriv hS_con hS_max (A := ⦃φ, ψ⦄) (by
        intro x hx; simp only [atom_eq, Multiset.mem_add, Multiset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption) (by
        have d1 : Derivation (∼⦃φ, ψ⦄ + ⦃φ⦄) :=
          Derivation.contraction (deriv_em φ) (by
            intro x hx; simp only [atom_eq, neg_map, Multiset.mem_add, Multiset.map_add,
              Multiset.map_singleton, Multiset.mem_singleton] at hx ⊢
            rcases hx with rfl | rfl
            · exact Or.inl (Or.inl rfl)
            · exact Or.inr rfl)
        have d2 : Derivation (∼⦃φ, ψ⦄ + ⦃ψ⦄) :=
          Derivation.contraction (deriv_em ψ) (by
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
      exact mem_of_deriv hS_con hS_max (A := ⦃ψ/[&c]⦄) (by simpa [atom_eq]) (by
        have d0 : Derivation (∼⦃ψ/[&c]⦄ + ⦃ψ/[&c]⦄) :=
          Derivation.contraction (deriv_em (ψ/[&c])) (by
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
        ![(&(tvRaw e id (v 0)) : Semiterm ℒₛₑₜ ℕ 0), (&(tvRaw e id (v 1)) : Semiterm ℒₛₑₜ ℕ 0)] := by
    intro n e v
    funext i; fin_cases i
    · change Rew.subst (n' := 0) (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0)) (v 0) = &(tvRaw e id (v 0))
      cases v 0 with | bvar _ => rfl | fvar _ => rfl | func f _ => exact (f : Empty).elim
    · change Rew.subst (n' := 0) (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0)) (v 1) = &(tvRaw e id (v 1))
      cases v 1 with | bvar _ => rfl | fvar _ => rfl | func f _ => exact (f : Empty).elim
  have htruth : ∀ (k : ℕ) {n : ℕ} (φ : Semiproposition ℒₛₑₜ n), complexity φ ≤ k →
      ∀ (e : Fin n → ℕ),
        evalRaw req rmem e id φ ↔ (Rew.subst (fun i => &(e i)) ▹ φ) ∈ S := by
    intro k
    induction k with
    | zero =>
      intro n φ hk e
      cases φ with
      | verum => exact ⟨fun _ => hS_verum, fun _ => trivial⟩
      | falsum => exact ⟨False.elim, fun h => (hS_falsum h).elim⟩
      | rel r v =>
        cases r with
        | eq =>
          change req (tvRaw e id (v 0)) (tvRaw e id (v 1)) ↔
            Semiformula.rel Language.Set.Rel.eq
              (fun i => Rew.subst (n' := 0) (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0)) (v i)) ∈ S
          rw [hvec_subst e v]
        | mem =>
          change rmem (tvRaw e id (v 0)) (tvRaw e id (v 1)) ↔
            Semiformula.rel Language.Set.Rel.mem
              (fun i => Rew.subst (n' := 0) (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0)) (v i)) ∈ S
          rw [hvec_subst e v]
      | nrel r v =>
        cases r with
        | eq =>
          change ¬ req (tvRaw e id (v 0)) (tvRaw e id (v 1)) ↔
            Semiformula.nrel Language.Set.Rel.eq
              (fun i => Rew.subst (n' := 0) (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0)) (v i)) ∈ S
          rw [hvec_subst e v, hS_neg]; rfl
        | mem =>
          change ¬ rmem (tvRaw e id (v 0)) (tvRaw e id (v 1)) ↔
            Semiformula.nrel Language.Set.Rel.mem
              (fun i => Rew.subst (n' := 0) (fun j => (&(e j) : Semiterm ℒₛₑₜ ℕ 0)) (v i)) ∈ S
          rw [hvec_subst e v, hS_neg]; rfl
      | and _ _ => simp [complexity] at hk
      | or _ _ => simp [complexity] at hk
      | all _ => simp [complexity] at hk
      | exs _ => simp [complexity] at hk
    | succ k ih =>
      intro n φ hk e
      cases φ with
      | verum => exact ⟨fun _ => hS_verum, fun _ => trivial⟩
      | falsum => exact ⟨False.elim, fun h => (hS_falsum h).elim⟩
      | rel r v => exact ih (Semiformula.rel r v) (by simp [complexity]) e
      | nrel r v => exact ih (Semiformula.nrel r v) (by simp [complexity]) e
      | and φ₁ φ₂ =>
        simp only [complexity] at hk
        change (evalRaw req rmem e id φ₁ ∧ evalRaw req rmem e id φ₂) ↔
          ((Rew.subst (fun i => &(e i)) ▹ φ₁) ⋏ (Rew.subst (fun i => &(e i)) ▹ φ₂)) ∈ S
        rw [hS_and, ih φ₁ (by omega) e, ih φ₂ (by omega) e]
      | or φ₁ φ₂ =>
        simp only [complexity] at hk
        change (evalRaw req rmem e id φ₁ ∨ evalRaw req rmem e id φ₂) ↔
          ((Rew.subst (fun i => &(e i)) ▹ φ₁) ⋎ (Rew.subst (fun i => &(e i)) ▹ φ₂)) ∈ S
        rw [hS_or, ih φ₁ (by omega) e, ih φ₂ (by omega) e]
      | all φ =>
        simp only [complexity] at hk
        change (∀ d : ℕ, evalRaw req rmem (d :> e) id φ) ↔
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
        simp only [complexity] at hk
        change (∃ d : ℕ, evalRaw req rmem (d :> e) id φ) ↔
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
    rw [htruth (complexity (Rewriting.emb ψ)) (Rewriting.emb ψ) le_rfl Fin.elim0, hsubst0]
    exact Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inr ⟨ψ, hψ, rfl⟩)⟩
  · rw [htruth (complexity (Rewriting.emb σ)) (Rewriting.emb σ) le_rfl Fin.elim0, hsubst0, hS_neg]
    push Not
    exact Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inl rfl)⟩

/- ## 7. Quotienting by `req` to obtain a normal model `(V, mem) ⊨ 𝗭𝗙𝗖` -/

lemma evalRaw_quotient {req rmem : ℕ → ℕ → Prop} (heqv : Equivalence req)
    (hresp : ∀ a₁ b₁ a₂ b₂, req a₁ a₂ → req b₁ b₂ → (rmem a₁ b₁ ↔ rmem a₂ b₂)) :
    let s : Setoid ℕ := ⟨req, heqv⟩
    let V := Quotient s
    let mem : V → V → Prop := Quotient.lift₂ rmem (fun a₁ b₁ a₂ b₂ h1 h2 => propext (hresp a₁ b₁ a₂ b₂ h1 h2))
    ∀ {ξ : Type*} {n : ℕ} (e : Fin n → ℕ) (ε : ξ → ℕ) (φ : Semiformula ℒₛₑₜ ξ n),
      evalM mem (Quotient.mk s ∘ e) (Quotient.mk s ∘ ε) φ ↔ evalRaw req rmem e ε φ := by
  intro s V mem ξ n e ε φ
  have htv : ∀ (m : ℕ) (e : Fin m → ℕ) (ε : ξ → ℕ) (t : Semiterm ℒₛₑₜ ξ m),
      tvRaw (Quotient.mk s ∘ e) (Quotient.mk s ∘ ε) t = Quotient.mk s (tvRaw e ε t) := by
    intro m e ε t
    cases t with
    | bvar i => rfl
    | fvar x => rfl
    | func f _ => exact (f : Empty).elim
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r v =>
    cases r with
    | eq =>
      change tvRaw (Quotient.mk s ∘ e) (Quotient.mk s ∘ ε) (v 0) =
          tvRaw (Quotient.mk s ∘ e) (Quotient.mk s ∘ ε) (v 1) ↔ _
      rw [htv, htv, Quotient.eq]; rfl
    | mem =>
      change mem (tvRaw (Quotient.mk s ∘ e) (Quotient.mk s ∘ ε) (v 0))
          (tvRaw (Quotient.mk s ∘ e) (Quotient.mk s ∘ ε) (v 1)) ↔ _
      rw [htv, htv]; rfl
  | nrel r v =>
    cases r with
    | eq =>
      change ¬ (tvRaw (Quotient.mk s ∘ e) (Quotient.mk s ∘ ε) (v 0) =
          tvRaw (Quotient.mk s ∘ e) (Quotient.mk s ∘ ε) (v 1)) ↔ _
      rw [htv, htv, Quotient.eq]; rfl
    | mem =>
      change ¬ mem (tvRaw (Quotient.mk s ∘ e) (Quotient.mk s ∘ ε) (v 0))
          (tvRaw (Quotient.mk s ∘ e) (Quotient.mk s ∘ ε) (v 1)) ↔ _
      rw [htv, htv]; rfl
  | and φ ψ ih1 ih2 => exact and_congr (ih1 e) (ih2 e)
  | or φ ψ ih1 ih2 => exact or_congr (ih1 e) (ih2 e)
  | all φ ih =>
    change (∀ d : V, evalM mem (d :> (Quotient.mk s ∘ e)) (Quotient.mk s ∘ ε) φ) ↔
      ∀ d : ℕ, evalRaw req rmem (d :> e) ε φ
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
    change (∃ d : V, evalM mem (d :> (Quotient.mk s ∘ e)) (Quotient.mk s ∘ ε) φ) ↔
      ∃ d : ℕ, evalRaw req rmem (d :> e) ε φ
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

theorem zfc_complete (σ : SetTheorySentence)
    (h : ∀ (V : Type) (mem : V → V → Prop),
      (∀ ψ ∈ 𝗭𝗙𝗖, evalM mem Fin.elim0 Empty.elim ψ) →
      evalM mem Fin.elim0 Empty.elim σ) :
    FFL.Entailment.Provable 𝗭𝗙𝗖 σ := by
  by_contra hnp
  obtain ⟨req, rmem, hT, hnσ⟩ := completeness_raw hnp
  have hemb : ∀ (ψ : SetTheorySentence),
      evalRaw req rmem Fin.elim0 Empty.elim ψ ↔
        evalRaw req rmem Fin.elim0 id (Rewriting.emb ψ) := by
    intro ψ
    symm
    refine (evalRaw_rew req rmem Fin.elim0 id Rew.emb ψ).trans ?_
    exact evalRaw_congr req rmem ψ (Subsingleton.elim _ _) (funext fun x => x.elim)
  have hT0 : ∀ ψ ∈ 𝗭𝗙𝗖, evalRaw req rmem Fin.elim0 Empty.elim ψ :=
    fun ψ hψ => (hemb ψ).mpr (hT ψ hψ)
  have hrefl : ∀ a, req a a :=
    hT0 (Theory.Eq.refl ℒₛₑₜ) (Or.inl (ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.refl))
  have hsymm : ∀ {a b}, req a b → req b a := by
    have h1 := hT0 (Theory.Eq.symm ℒₛₑₜ) (Or.inl (ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.symm))
    intro a b hab
    have h2 := h1 a b
    change ¬ req a b ∨ req b a at h2
    exact h2.resolve_left (not_not.mpr hab)
  have htrans : ∀ {a b c}, req a b → req b c → req a c := by
    have h1 := hT0 (Theory.Eq.trans ℒₛₑₜ) (Or.inl (ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.trans))
    intro a b c hab hbc
    have h2 := h1 a b c
    change ¬ req a b ∨ (¬ req b c ∨ req a c) at h2
    exact (h2.resolve_left (not_not.mpr hab)).resolve_left (not_not.mpr hbc)
  have heqv : Equivalence req := ⟨hrefl, hsymm, htrans⟩
  have hmem_fwd : ∀ a₁ b₁ a₂ b₂, req a₁ a₂ → req b₁ b₂ → rmem a₁ b₁ → rmem a₂ b₂ := by
    have hax : @Theory.Eq.relExt ℒₛₑₜ _ 2 Language.Set.Rel.mem ∈ 𝗭𝗙𝗖 :=
      Or.inl (ZermeloFraenkel.axiom_of_equality _ (@Theory.eqAxiom.relExt ℒₛₑₜ _ 2 Language.Set.Rel.mem))
    have h1 := hT0 _ hax
    intro a₁ b₁ a₂ b₂ h12 h34 hm
    have h2 := h1 b₂ a₂ b₁ a₁
    change ((¬ req a₁ a₂ ∨ (¬ req b₁ b₂ ∨ False)) ∨ (¬ rmem a₁ b₁ ∨ rmem a₂ b₂)) at h2
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
  have hV_zfc : ∀ ψ ∈ 𝗭𝗙𝗖, evalM mem Fin.elim0 Empty.elim ψ := by
    intro ψ hψ
    have hq := (evalRaw_quotient heqv hresp Fin.elim0 Empty.elim ψ).mpr (hT0 ψ hψ)
    exact (evalRaw_congr Eq mem ψ (Subsingleton.elim _ _) (funext fun x => x.elim)).mp hq
  have hV_σ := h V mem hV_zfc
  have hraw_σ : evalRaw req rmem Fin.elim0 Empty.elim σ := by
    have hq : evalM mem (Quotient.mk s ∘ Fin.elim0) (Quotient.mk s ∘ Empty.elim) σ :=
      (evalRaw_congr Eq mem σ (Subsingleton.elim _ _) (funext fun x => x.elim)).mp hV_σ
    exact (evalRaw_quotient heqv hresp Fin.elim0 Empty.elim σ).mp hq
  exact hnσ ((hemb σ).mp hraw_σ)

end C14Completeness

namespace C14Stage2

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver C14Completeness
open scoped Classical

/- ## Section 1: `evalM` Connective Rules and `univCl` Elimination -/

lemma evalM_top {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) :
    evalM mem e ε (⊤ : Semiformula ℒₛₑₜ ξ n) ↔ True := Iff.rfl

lemma evalM_bot {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) :
    evalM mem e ε (⊥ : Semiformula ℒₛₑₜ ξ n) ↔ False := Iff.rfl

lemma evalM_eq {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (t₁ t₂ : Semiterm ℒₛₑₜ ξ n) :
    evalM mem e ε (op(=).operator ![t₁, t₂]) ↔ tvRaw e ε t₁ = tvRaw e ε t₂ := Iff.rfl

lemma evalM_mem {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (t₁ t₂ : Semiterm ℒₛₑₜ ξ n) :
    evalM mem e ε (Semiformula.Operator.Mem.mem.operator ![t₁, t₂]) ↔
      mem (tvRaw e ε t₁) (tvRaw e ε t₂) := Iff.rfl

lemma evalM_not {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ n) :
    evalM mem e ε (∼φ) ↔ ¬ evalM mem e ε φ :=
  evalRaw_neg Eq mem e ε φ

lemma evalM_and {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    evalM mem e ε (φ ⋏ ψ) ↔ evalM mem e ε φ ∧ evalM mem e ε ψ := Iff.rfl

lemma evalM_or {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    evalM mem e ε (φ ⋎ ψ) ↔ evalM mem e ε φ ∨ evalM mem e ε ψ := Iff.rfl

lemma evalM_imp {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    evalM mem e ε (φ 🡒 ψ) ↔ (evalM mem e ε φ → evalM mem e ε ψ) := by
  change evalM mem e ε (∼φ) ∨ evalM mem e ε ψ ↔ _
  rw [evalM_not, imp_iff_not_or]

lemma evalM_iff {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    evalM mem e ε (φ 🡘 ψ) ↔ (evalM mem e ε φ ↔ evalM mem e ε ψ) := by
  change evalM mem e ε (φ 🡒 ψ) ∧ evalM mem e ε (ψ 🡒 φ) ↔ _
  rw [evalM_imp, evalM_imp]
  exact iff_iff_implies_and_implies.symm

lemma evalM_all {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    evalM mem e ε (∀¹ φ) ↔ ∀ d : V, evalM mem (d :> e) ε φ := Iff.rfl

lemma evalM_exs {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    evalM mem e ε (∃¹ φ) ↔ ∃ d : V, evalM mem (d :> e) ε φ := Iff.rfl

lemma evalM_ballMem {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (t : Semiterm ℒₛₑₜ ξ n) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    evalM mem e ε (Semiformula.ballMem t φ) ↔
      ∀ d : V, mem d (tvRaw e ε t) → evalM mem (d :> e) ε φ := by
  change (∀ d : V, evalM mem (d :> e) ε
    (Semiformula.Operator.Mem.mem.operator ![#0, Rew.bShift t] 🡒 φ)) ↔ _
  refine forall_congr' fun d => ?_
  rw [evalM_imp, evalM_mem]
  change (mem d (tvRaw (d :> e) ε (Rew.bShift t)) → _) ↔ _
  rw [tvRaw_bShift]

lemma evalM_bexsMem {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (t : Semiterm ℒₛₑₜ ξ n) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    evalM mem e ε (Semiformula.bexsMem t φ) ↔
      ∃ d : V, mem d (tvRaw e ε t) ∧ evalM mem (d :> e) ε φ := by
  change (∃ d : V, evalM mem (d :> e) ε
    (Semiformula.Operator.Mem.mem.operator ![#0, Rew.bShift t] ⋏ φ)) ↔ _
  refine exists_congr fun d => ?_
  rw [evalM_and, evalM_mem]
  change (mem d (tvRaw (d :> e) ε (Rew.bShift t)) ∧ _) ↔ _
  rw [tvRaw_bShift]

lemma evalM_subst {V : Type} {mem : V → V → Prop} {ξ : Type*} {n₁ n₂ : ℕ}
    (e : Fin n₂ → V) (ε : ξ → V) (v : Fin n₁ → Semiterm ℒₛₑₜ ξ n₂)
    (φ : Semiformula ℒₛₑₜ ξ n₁) :
    evalM mem e ε (φ ⇜ v) ↔ evalM mem (fun i => tvRaw e ε (v i)) ε φ := by
  exact evalRaw_rew Eq mem e ε (Rew.subst v) φ

lemma evalM_emb {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semisentence ℒₛₑₜ n) :
    evalM mem e ε (Rewriting.emb φ) ↔ evalM mem e Empty.elim φ := by
  refine (evalRaw_rew Eq mem e ε Rew.emb φ).trans ?_
  exact evalRaw_congr Eq mem φ rfl (funext fun x => x.elim)

lemma evalM_existsUnique {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    evalM mem e ε (∃¹! φ) ↔ ∃! y : V, evalM mem (y :> e) ε φ := by
  unfold Semiformula.existsUnique ExistsUnique
  rw [evalM_exs]
  refine exists_congr fun y => ?_
  rw [evalM_and, evalM_subst, evalM_all]
  have he1 : (fun k : Fin (n + 1) =>
      tvRaw (y :> e) ε ((#0 :> fun x : Fin n => #(BinderNotation.finSuccItr x 1)) k)) =
      (y :> e) := by
    funext k
    refine Fin.cases rfl (fun j => ?_) k
    simp [BinderNotation.finSuccItr, tvRaw]
  rw [he1]
  refine and_congr Iff.rfl (forall_congr' fun z => ?_)
  rw [evalM_imp, evalM_subst, evalM_eq]
  have he2 : (fun k : Fin (n + 1) =>
      tvRaw (z :> y :> e) ε ((#0 :> fun x : Fin n => #(BinderNotation.finSuccItr x 2)) k)) =
      (z :> e) := by
    funext k
    refine Fin.cases rfl (fun j => ?_) k
    simp [BinderNotation.finSuccItr, tvRaw]
  rw [he2]
  rfl

lemma tvRaw_toEmpty {V : Type} {n : ℕ} (e : Fin n → V) (ε : ℕ → V) (ε0 : Empty → V)
    (t : Semiterm ℒₛₑₜ ℕ n) (h : t.freeVariables = ∅) :
    tvRaw e ε0 (t.toEmpty h) = tvRaw e ε t := by
  cases t with
  | bvar i => rfl
  | fvar x => exact absurd h (by simp [Semiterm.freeVariables])
  | func f _ => exact (f : Empty).elim

lemma evalM_toEmpty {V : Type} {mem : V → V → Prop} :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) (h : φ.freeVariables = ∅)
      (e : Fin n → V) (ε : ℕ → V) (ε0 : Empty → V),
      evalM mem e ε0 (φ.toEmpty h) ↔ evalM mem e ε φ
  | _, Semiformula.verum, _, _, _, _ => Iff.rfl
  | _, Semiformula.falsum, _, _, _, _ => Iff.rfl
  | _, Semiformula.rel Language.Set.Rel.eq v, h, e, ε, ε0 => by
      change tvRaw e ε0 ((v 0).toEmpty _) = tvRaw e ε0 ((v 1).toEmpty _) ↔
        tvRaw e ε (v 0) = tvRaw e ε (v 1)
      rw [tvRaw_toEmpty, tvRaw_toEmpty]
  | _, Semiformula.rel Language.Set.Rel.mem v, h, e, ε, ε0 => by
      change mem (tvRaw e ε0 ((v 0).toEmpty _)) (tvRaw e ε0 ((v 1).toEmpty _)) ↔
        mem (tvRaw e ε (v 0)) (tvRaw e ε (v 1))
      rw [tvRaw_toEmpty, tvRaw_toEmpty]
  | _, Semiformula.nrel Language.Set.Rel.eq v, h, e, ε, ε0 => by
      change ¬ tvRaw e ε0 ((v 0).toEmpty _) = tvRaw e ε0 ((v 1).toEmpty _) ↔
        ¬ tvRaw e ε (v 0) = tvRaw e ε (v 1)
      rw [tvRaw_toEmpty, tvRaw_toEmpty]
  | _, Semiformula.nrel Language.Set.Rel.mem v, h, e, ε, ε0 => by
      change ¬ mem (tvRaw e ε0 ((v 0).toEmpty _)) (tvRaw e ε0 ((v 1).toEmpty _)) ↔
        ¬ mem (tvRaw e ε (v 0)) (tvRaw e ε (v 1))
      rw [tvRaw_toEmpty, tvRaw_toEmpty]
  | _, Semiformula.and φ ψ, h, e, ε, ε0 =>
      and_congr (evalM_toEmpty φ _ e ε ε0) (evalM_toEmpty ψ _ e ε ε0)
  | _, Semiformula.or φ ψ, h, e, ε, ε0 =>
      or_congr (evalM_toEmpty φ _ e ε ε0) (evalM_toEmpty ψ _ e ε ε0)
  | _, Semiformula.all φ, h, e, ε, ε0 =>
      forall_congr' fun d => evalM_toEmpty φ h (d :> e) ε ε0
  | _, Semiformula.exs φ, h, e, ε, ε0 =>
      exists_congr fun d => evalM_toEmpty φ h (d :> e) ε ε0

lemma evalM_allClosure_elim {V : Type} {mem : V → V → Prop} :
    ∀ {m : ℕ} (ψ : Semiformula ℒₛₑₜ ℕ m) (ε : ℕ → V),
      evalM mem (Fin.elim0 : Fin 0 → V) ε (∀¹* ψ) →
        ∀ w : Fin m → V, evalM mem w ε ψ
  | 0, ψ, ε, h, w => by
      have hw : w = Fin.elim0 := Subsingleton.elim _ _
      rwa [hw]
  | m + 1, ψ, ε, h, w => by
      have h1 := evalM_allClosure_elim (m := m) (∀¹ ψ) ε h (fun i => w i.succ)
      have h2 := h1 (w 0)
      have hw : (w 0 :> fun i : Fin m => w i.succ) = w := by
        funext i; cases i using Fin.cases <;> rfl
      rwa [hw] at h2

lemma fixitr_fvar_aux (n m x : ℕ) :
    Rew.fixitr n m (Semiterm.fvar x : Semiterm ℒₛₑₜ ℕ n) =
      if h : x < m then Semiterm.bvar (Fin.natAdd n ⟨x, h⟩) else Semiterm.fvar (x - m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Rew.fix (Rew.fixitr n m (Semiterm.fvar x)) = _
    rw [ih]
    by_cases hx : x < m
    · have hx' : x < m + 1 := by omega
      simp only [dif_pos hx, dif_pos hx']
      rfl
    · by_cases hx' : x < m + 1
      · have he : x = m := by omega
        subst x
        simp only [dif_neg (Nat.lt_irrefl m), dif_pos (Nat.lt_succ_self m), Nat.sub_self]
        rfl
      · have he : x - m = x - (m + 1) + 1 := by omega
        simp only [dif_neg hx, dif_neg hx', he]
        rfl

lemma evalM_univCl_elim {V : Type} {mem : V → V → Prop} (ψ : Proposition ℒₛₑₜ)
    (h : evalM mem Fin.elim0 Empty.elim (Semiformula.univCl ψ)) (ε : ℕ → V) :
    evalM mem Fin.elim0 ε ψ := by
  let m := ψ.fvSup
  let εOuter : ℕ → V := fun k => ε (k + m)
  unfold Semiformula.univCl at h
  rw [evalM_toEmpty _ _ Fin.elim0 εOuter Empty.elim] at h
  unfold Semiformula.univCl' at h
  have h1 := evalM_allClosure_elim (Rew.fixitr 0 m ▹ ψ) εOuter h (fun i => ε i.val)
  have h2 := (evalRaw_rew Eq mem (fun i : Fin (0 + m) => ε i.val) εOuter (Rew.fixitr 0 m) ψ).mp h1
  refine (evalRaw_congr Eq mem ψ (Subsingleton.elim _ _) ?_).mp h2
  funext x
  rw [fixitr_fvar_aux 0 m x]
  by_cases hx : x < m
  · simp only [dif_pos hx, tvRaw, Fin.natAdd]
    simp
  · simp only [dif_neg hx, tvRaw, εOuter]
    congr 1
    omega

/- ## Section 2: Arbitrary Model of ZFC Toolkit -/

structure ZFCModel where
  V : Type
  mem : V → V → Prop
  sat : ∀ ψ ∈ 𝗭𝗙𝗖, evalM mem Fin.elim0 Empty.elim ψ

section WithModel

variable (M0 : ZFCModel)

def mEv {n : ℕ} (e : Fin n → M0.V) (φ : SetTheorySemisentence n) : Prop :=
  evalM M0.mem e Empty.elim φ

lemma mEv_top {n : ℕ} (e : Fin n → M0.V) : mEv M0 e (⊤ : SetTheorySemisentence n) ↔ True := Iff.rfl
lemma mEv_bot {n : ℕ} (e : Fin n → M0.V) : mEv M0 e (⊥ : SetTheorySemisentence n) ↔ False := Iff.rfl
lemma mEv_eq {n : ℕ} (e : Fin n → M0.V) (t₁ t₂ : Semiterm ℒₛₑₜ Empty n) :
    mEv M0 e (op(=).operator ![t₁, t₂]) ↔ tvRaw e Empty.elim t₁ = tvRaw e Empty.elim t₂ := Iff.rfl
lemma mEv_mem {n : ℕ} (e : Fin n → M0.V) (t₁ t₂ : Semiterm ℒₛₑₜ Empty n) :
    mEv M0 e (Semiformula.Operator.Mem.mem.operator ![t₁, t₂]) ↔
      M0.mem (tvRaw e Empty.elim t₁) (tvRaw e Empty.elim t₂) := Iff.rfl
lemma mEv_not {n : ℕ} (e : Fin n → M0.V) (φ : SetTheorySemisentence n) :
    mEv M0 e (∼φ) ↔ ¬ mEv M0 e φ := evalM_not e Empty.elim φ
lemma mEv_and {n : ℕ} (e : Fin n → M0.V) (φ ψ : SetTheorySemisentence n) :
    mEv M0 e (φ ⋏ ψ) ↔ mEv M0 e φ ∧ mEv M0 e ψ := Iff.rfl
lemma mEv_or {n : ℕ} (e : Fin n → M0.V) (φ ψ : SetTheorySemisentence n) :
    mEv M0 e (φ ⋎ ψ) ↔ mEv M0 e φ ∨ mEv M0 e ψ := Iff.rfl
lemma mEv_imp {n : ℕ} (e : Fin n → M0.V) (φ ψ : SetTheorySemisentence n) :
    mEv M0 e (φ 🡒 ψ) ↔ (mEv M0 e φ → mEv M0 e ψ) := evalM_imp e Empty.elim φ ψ
lemma mEv_iff {n : ℕ} (e : Fin n → M0.V) (φ ψ : SetTheorySemisentence n) :
    mEv M0 e (φ 🡘 ψ) ↔ (mEv M0 e φ ↔ mEv M0 e ψ) := evalM_iff e Empty.elim φ ψ
lemma mEv_all {n : ℕ} (e : Fin n → M0.V) (φ : SetTheorySemisentence (n + 1)) :
    mEv M0 e (∀¹ φ) ↔ ∀ d : M0.V, mEv M0 (d :> e) φ := Iff.rfl
lemma mEv_exs {n : ℕ} (e : Fin n → M0.V) (φ : SetTheorySemisentence (n + 1)) :
    mEv M0 e (∃¹ φ) ↔ ∃ d : M0.V, mEv M0 (d :> e) φ := Iff.rfl
lemma mEv_ballMem {n : ℕ} (e : Fin n → M0.V) (t : Semiterm ℒₛₑₜ Empty n)
    (φ : SetTheorySemisentence (n + 1)) :
    mEv M0 e (Semiformula.ballMem t φ) ↔
      ∀ d : M0.V, M0.mem d (tvRaw e Empty.elim t) → mEv M0 (d :> e) φ :=
  evalM_ballMem e Empty.elim t φ
lemma mEv_bexsMem {n : ℕ} (e : Fin n → M0.V) (t : Semiterm ℒₛₑₜ Empty n)
    (φ : SetTheorySemisentence (n + 1)) :
    mEv M0 e (Semiformula.bexsMem t φ) ↔
      ∃ d : M0.V, M0.mem d (tvRaw e Empty.elim t) ∧ mEv M0 (d :> e) φ :=
  evalM_bexsMem e Empty.elim t φ
lemma mEv_subst {n₁ n₂ : ℕ} (e : Fin n₂ → M0.V) (v : Fin n₁ → Semiterm ℒₛₑₜ Empty n₂)
    (φ : SetTheorySemisentence n₁) :
    mEv M0 e (φ ⇜ v) ↔ mEv M0 (fun i => tvRaw e Empty.elim (v i)) φ :=
  evalM_subst e Empty.elim v φ
lemma mEv_existsUnique {n : ℕ} (e : Fin n → M0.V) (φ : SetTheorySemisentence (n + 1)) :
    mEv M0 e (∃¹! φ) ↔ ∃! y : M0.V, mEv M0 (y :> e) φ :=
  evalM_existsUnique e Empty.elim φ

lemma extV {x y : M0.V} (h : ∀ z : M0.V, M0.mem z x ↔ M0.mem z y) : x = y := by
  have hax : mEv M0 Fin.elim0 Axiom.extentionality :=
    M0.sat Axiom.extentionality (Or.inl ZermeloFraenkel.axiom_of_extentionality)
  unfold Axiom.extentionality at hax
  rw [mEv_all] at hax
  have h1 := hax x
  rw [mEv_all] at h1
  have h2 := h1 y
  rw [mEv_iff, mEv_eq, mEv_all] at h2
  refine h2.mpr fun z => ?_
  rw [mEv_iff, mEv_mem, mEv_mem]
  exact h z

lemma exists_emptyV : ∃ e : M0.V, ∀ y : M0.V, ¬ M0.mem y e := by
  have hax : mEv M0 Fin.elim0 Axiom.empty :=
    M0.sat Axiom.empty (Or.inl ZermeloFraenkel.axiom_of_empty_set)
  unfold Axiom.empty at hax
  rw [mEv_exs] at hax
  obtain ⟨e, he⟩ := hax
  rw [mEv_all] at he
  refine ⟨e, fun y => ?_⟩
  have hy := he y
  rw [mEv_not, mEv_mem] at hy
  exact hy

noncomputable def emptyV : M0.V := (exists_emptyV M0).choose

lemma not_mem_emptyV (y : M0.V) : ¬ M0.mem y (emptyV M0) :=
  (exists_emptyV M0).choose_spec y

lemma exists_doubletonV (x y : M0.V) :
    ∃ p : M0.V, ∀ z : M0.V, M0.mem z p ↔ z = x ∨ z = y := by
  have hax : mEv M0 Fin.elim0 Axiom.pairing :=
    M0.sat Axiom.pairing (Or.inl ZermeloFraenkel.axiom_of_pairing)
  unfold Axiom.pairing at hax
  rw [mEv_all] at hax
  have h1 := hax x
  rw [mEv_all] at h1
  have h2 := h1 y
  rw [mEv_exs] at h2
  obtain ⟨p, hp⟩ := h2
  rw [mEv_all] at hp
  refine ⟨p, fun z => ?_⟩
  have hz := hp z
  rw [mEv_iff, mEv_mem, mEv_or, mEv_eq, mEv_eq] at hz
  exact hz

noncomputable def doubletonV (x y : M0.V) : M0.V := (exists_doubletonV M0 x y).choose

lemma mem_doubletonV {z x y : M0.V} :
    M0.mem z (doubletonV M0 x y) ↔ z = x ∨ z = y :=
  (exists_doubletonV M0 x y).choose_spec z

noncomputable def singletonV (x : M0.V) : M0.V := doubletonV M0 x x

lemma mem_singletonV {z x : M0.V} :
    M0.mem z (singletonV M0 x) ↔ z = x := by
  unfold singletonV
  rw [mem_doubletonV, or_self]

lemma exists_sUnionV (x : M0.V) :
    ∃ u : M0.V, ∀ z : M0.V, M0.mem z u ↔ ∃ w : M0.V, M0.mem w x ∧ M0.mem z w := by
  have hax : mEv M0 Fin.elim0 Axiom.union :=
    M0.sat Axiom.union (Or.inl ZermeloFraenkel.axiom_of_union)
  unfold Axiom.union at hax
  rw [mEv_all] at hax
  have h1 := hax x
  rw [mEv_exs] at h1
  obtain ⟨u, hu⟩ := h1
  rw [mEv_all] at hu
  refine ⟨u, fun z => ?_⟩
  have hz := hu z
  rw [mEv_iff, mEv_mem, mEv_bexsMem] at hz
  exact hz

noncomputable def sUnionV (x : M0.V) : M0.V := (exists_sUnionV M0 x).choose

lemma mem_sUnionV {z x : M0.V} :
    M0.mem z (sUnionV M0 x) ↔ ∃ w : M0.V, M0.mem w x ∧ M0.mem z w :=
  (exists_sUnionV M0 x).choose_spec z

noncomputable def unionV (x y : M0.V) : M0.V := sUnionV M0 (doubletonV M0 x y)

lemma mem_unionV {z x y : M0.V} :
    M0.mem z (unionV M0 x y) ↔ M0.mem z x ∨ M0.mem z y := by
  unfold unionV
  rw [mem_sUnionV]
  constructor
  · rintro ⟨w, hw, hz⟩
    rcases (mem_doubletonV M0).mp hw with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr hz
  · rintro (hz | hz)
    · exact ⟨x, (mem_doubletonV M0).mpr (Or.inl rfl), hz⟩
    · exact ⟨y, (mem_doubletonV M0).mpr (Or.inr rfl), hz⟩

noncomputable def insertV (x y : M0.V) : M0.V := unionV M0 (singletonV M0 x) y

lemma mem_insertV {z x y : M0.V} :
    M0.mem z (insertV M0 x y) ↔ z = x ∨ M0.mem z y := by
  unfold insertV
  rw [mem_unionV, mem_singletonV]

lemma sUnionV_singletonV (x : M0.V) : sUnionV M0 (singletonV M0 x) = x := by
  apply extV M0
  intro z
  rw [mem_sUnionV]
  constructor
  · rintro ⟨w, hw, hz⟩
    rwa [(mem_singletonV M0).mp hw] at hz
  · intro hz
    exact ⟨x, (mem_singletonV M0).mpr rfl, hz⟩

lemma exists_powersetV (x : M0.V) :
    ∃ P : M0.V, ∀ z : M0.V, M0.mem z P ↔ ∀ w : M0.V, M0.mem w z → M0.mem w x := by
  have hax : mEv M0 Fin.elim0 Axiom.power :=
    M0.sat Axiom.power (Or.inl ZermeloFraenkel.axiom_of_power_set)
  unfold Axiom.power at hax
  rw [mEv_all] at hax
  have h1 := hax x
  rw [mEv_exs] at h1
  obtain ⟨P, hP⟩ := h1
  rw [mEv_all] at hP
  refine ⟨P, fun z => ?_⟩
  have hz := hP z
  rw [mEv_iff, mEv_mem, mEv_subst] at hz
  refine hz.trans ?_
  unfold SetTheory.isSubsetOf
  rw [mEv_ballMem]
  rfl

noncomputable def powersetV (x : M0.V) : M0.V := (exists_powersetV M0 x).choose

lemma mem_powersetV {z x : M0.V} :
    M0.mem z (powersetV M0 x) ↔ ∀ w : M0.V, M0.mem w z → M0.mem w x :=
  (exists_powersetV M0 x).choose_spec z

lemma foundationV (x : M0.V) (hne : ∃ y : M0.V, M0.mem y x) :
    ∃ y : M0.V, M0.mem y x ∧ ∀ z : M0.V, M0.mem z x → ¬ M0.mem z y := by
  have hax : mEv M0 Fin.elim0 Axiom.foundation :=
    M0.sat Axiom.foundation (Or.inl ZermeloFraenkel.axiom_of_foundation)
  unfold Axiom.foundation at hax
  rw [mEv_all] at hax
  have h1 := hax x
  rw [mEv_imp, mEv_subst, mEv_bexsMem] at h1
  have hne' : mEv M0 ![x] SetTheory.isNonempty := hne
  have h2 := h1 (by
    unfold mEv at hne' ⊢
    refine (evalRaw_congr Eq M0.mem SetTheory.isNonempty ?_ rfl).mpr hne'
    funext i; fin_cases i; rfl)
  obtain ⟨y, hyx, hymin⟩ := h2
  rw [mEv_ballMem] at hymin
  refine ⟨y, hyx, fun z hzx => ?_⟩
  have hz := hymin z hzx
  rw [mEv_not, mEv_mem] at hz
  exact hz

lemma irreflV (x : M0.V) : ¬ M0.mem x x := by
  intro hxx
  obtain ⟨y, hy, hmin⟩ := foundationV M0 (singletonV M0 x) ⟨x, (mem_singletonV M0).mpr rfl⟩
  have hyx : y = x := (mem_singletonV M0).mp hy
  subst y
  exact hmin x ((mem_singletonV M0).mpr rfl) hxx

lemma asymmV {x y : M0.V} (hxy : M0.mem x y) (hyx : M0.mem y x) : False := by
  obtain ⟨u, hu, hmin⟩ := foundationV M0 (doubletonV M0 x y) ⟨x, (mem_doubletonV M0).mpr (Or.inl rfl)⟩
  rcases (mem_doubletonV M0).mp hu with rfl | rfl
  · exact hmin y ((mem_doubletonV M0).mpr (Or.inr rfl)) hyx
  · exact hmin x ((mem_doubletonV M0).mpr (Or.inl rfl)) hxy

lemma succV_inj {a b : M0.V} (h : insertV M0 a a = insertV M0 b b) : a = b := by
  by_contra hne
  have ha : M0.mem a (insertV M0 b b) := h ▸ (mem_insertV M0).mpr (Or.inl rfl)
  have hb : M0.mem b (insertV M0 a a) := h.symm ▸ (mem_insertV M0).mpr (Or.inl rfl)
  have hab : M0.mem a b := ((mem_insertV M0).mp ha).resolve_left hne
  have hba : M0.mem b a := ((mem_insertV M0).mp hb).resolve_left (Ne.symm hne)
  exact asymmV M0 hab hba

lemma sepV (X : M0.V) (φ : SetTheorySemiproposition 1) (ε : ℕ → M0.V) :
    ∃ Y : M0.V, ∀ z : M0.V, M0.mem z Y ↔ M0.mem z X ∧ evalM M0.mem ![z] ε φ := by
  have hax := M0.sat (Axiom.separationSchema φ) (Or.inl (ZermeloFraenkel.axiom_of_separation φ))
  have hinst := evalM_univCl_elim _ hax ε
  rw [evalM_all] at hinst
  have h1 := hinst X
  rw [evalM_exs] at h1
  obtain ⟨Y, hY⟩ := h1
  rw [evalM_all] at hY
  refine ⟨Y, fun z => ?_⟩
  have hz := hY z
  rw [evalM_iff, evalM_mem, evalM_and, evalM_mem, evalM_subst] at hz
  refine hz.trans (and_congr Iff.rfl ?_)
  refine evalRaw_congr Eq M0.mem φ ?_ rfl
  funext i; fin_cases i; rfl

lemma exists_sInterV (x : M0.V) :
    ∃ u : M0.V, ∀ z : M0.V, M0.mem z u ↔ (∃ y : M0.V, M0.mem y x) ∧ ∀ y : M0.V, M0.mem y x → M0.mem z y := by
  by_cases hne : ∃ w₀ : M0.V, M0.mem w₀ x
  · obtain ⟨w₀, hw₀⟩ := hne
    let φ : SetTheorySemiproposition 1 :=
      Semiformula.ballMem (&0) (Semiformula.rel Language.Set.Rel.mem ![#1, #0])
    obtain ⟨Y, hY⟩ := sepV M0 w₀ φ (fun _ => x)
    refine ⟨Y, fun z => ?_⟩
    rw [hY z]
    have hφ : evalM M0.mem ![z] (fun _ => x) φ ↔ ∀ y : M0.V, M0.mem y x → M0.mem z y := by
      dsimp only [φ]
      rw [evalM_ballMem]
      rfl
    rw [hφ]
    exact ⟨fun ⟨_, hall⟩ => ⟨⟨w₀, hw₀⟩, hall⟩, fun ⟨_, hall⟩ => ⟨hall w₀ hw₀, hall⟩⟩
  · refine ⟨emptyV M0, fun z => ?_⟩
    simp only [not_mem_emptyV, hne, false_and]

noncomputable def sInterV (x : M0.V) : M0.V := (exists_sInterV M0 x).choose

lemma mem_sInterV {z x : M0.V} :
    M0.mem z (sInterV M0 x) ↔ (∃ y : M0.V, M0.mem y x) ∧ ∀ y : M0.V, M0.mem y x → M0.mem z y :=
  (exists_sInterV M0 x).choose_spec z

noncomputable def kpairV (a b : M0.V) : M0.V :=
  doubletonV M0 (singletonV M0 a) (doubletonV M0 a b)

lemma kpairV_inj {a b c d : M0.V} (h : kpairV M0 a b = kpairV M0 c d) : a = c ∧ b = d := by
  have hc_mem : M0.mem (singletonV M0 c) (kpairV M0 a b) :=
    h ▸ (mem_doubletonV M0).mpr (Or.inl rfl)
  have hac : a = c := by
    have ha_mem : M0.mem (singletonV M0 a) (kpairV M0 c d) :=
      h ▸ (mem_doubletonV M0).mpr (Or.inl rfl)
    rcases (mem_doubletonV M0).mp ha_mem with h1 | h1
    · have : M0.mem c (singletonV M0 a) := h1 ▸ (mem_singletonV M0).mpr rfl
      exact ((mem_singletonV M0).mp this).symm
    · have : M0.mem c (singletonV M0 a) := h1 ▸ (mem_doubletonV M0).mpr (Or.inl rfl)
      exact ((mem_singletonV M0).mp this).symm
  subst hac
  refine ⟨rfl, ?_⟩
  by_cases hab : a = b
  · subst hab
    have hd_mem : M0.mem (doubletonV M0 a d) (kpairV M0 a a) :=
      h ▸ (mem_doubletonV M0).mpr (Or.inr rfl)
    have hdaa : doubletonV M0 a d = singletonV M0 a := by
      rcases (mem_doubletonV M0).mp hd_mem with h1 | h1
      · exact h1
      · exact h1
    have : M0.mem d (singletonV M0 a) := hdaa ▸ (mem_doubletonV M0).mpr (Or.inr rfl)
    exact ((mem_singletonV M0).mp this).symm
  · have hne : doubletonV M0 a b ≠ singletonV M0 a := by
      intro heq
      have : M0.mem b (singletonV M0 a) := heq ▸ (mem_doubletonV M0).mpr (Or.inr rfl)
      exact hab ((mem_singletonV M0).mp this).symm
    have hab_mem : M0.mem (doubletonV M0 a b) (kpairV M0 a d) :=
      h ▸ (mem_doubletonV M0).mpr (Or.inr rfl)
    have heq : doubletonV M0 a b = doubletonV M0 a d :=
      ((mem_doubletonV M0).mp hab_mem).resolve_left hne
    have : M0.mem b (doubletonV M0 a d) := heq ▸ (mem_doubletonV M0).mpr (Or.inr rfl)
    exact ((mem_doubletonV M0).mp this).resolve_left (Ne.symm hab)

lemma sInterV_kpairV (a b : M0.V) : sInterV M0 (kpairV M0 a b) = singletonV M0 a := by
  apply extV M0
  intro z
  rw [mem_sInterV, mem_singletonV]
  constructor
  · rintro ⟨_, hall⟩
    exact (mem_singletonV M0).mp (hall (singletonV M0 a) ((mem_doubletonV M0).mpr (Or.inl rfl)))
  · rintro rfl
    refine ⟨⟨singletonV M0 z, (mem_doubletonV M0).mpr (Or.inl rfl)⟩, fun y hy => ?_⟩
    rcases (mem_doubletonV M0).mp hy with rfl | rfl
    · exact (mem_singletonV M0).mpr rfl
    · exact (mem_doubletonV M0).mpr (Or.inl rfl)

lemma sUnionV_kpairV (a b : M0.V) : sUnionV M0 (kpairV M0 a b) = doubletonV M0 a b := by
  apply extV M0
  intro z
  rw [mem_sUnionV, mem_doubletonV]
  constructor
  · rintro ⟨w, hw, hz⟩
    rcases (mem_doubletonV M0).mp hw with rfl | rfl
    · exact Or.inl ((mem_singletonV M0).mp hz)
    · exact (mem_doubletonV M0).mp hz
  · rintro (rfl | rfl)
    · exact ⟨singletonV M0 z, (mem_doubletonV M0).mpr (Or.inl rfl), (mem_singletonV M0).mpr rfl⟩
    · exact ⟨doubletonV M0 a z, (mem_doubletonV M0).mpr (Or.inr rfl), (mem_doubletonV M0).mpr (Or.inr rfl)⟩

noncomputable def pi1V (w : M0.V) : M0.V := sUnionV M0 (sInterV M0 w)

lemma pi1V_kpairV (a b : M0.V) : pi1V M0 (kpairV M0 a b) = a := by
  unfold pi1V
  rw [sInterV_kpairV, sUnionV_singletonV]

lemma exists_pi2SepV (w : M0.V) :
    ∃ s : M0.V, ∀ z : M0.V, M0.mem z s ↔
      M0.mem z (sUnionV M0 w) ∧ (M0.mem z (sInterV M0 w) → sUnionV M0 w = sInterV M0 w) := by
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.rel Language.Set.Rel.mem ![#0, &0] 🡒
      Semiformula.rel Language.Set.Rel.eq ![&1, &0]
  let ε : ℕ → M0.V := fun k => if k = 0 then sInterV M0 w else sUnionV M0 w
  obtain ⟨s, hs⟩ := sepV M0 (sUnionV M0 w) φ ε
  refine ⟨s, fun z => ?_⟩
  rw [hs z]
  refine and_congr Iff.rfl ?_
  dsimp only [φ]
  rw [evalM_imp]
  rfl

noncomputable def pi2SepV (w : M0.V) : M0.V := (exists_pi2SepV M0 w).choose

lemma mem_pi2SepV {z w : M0.V} :
    M0.mem z (pi2SepV M0 w) ↔
      M0.mem z (sUnionV M0 w) ∧ (M0.mem z (sInterV M0 w) → sUnionV M0 w = sInterV M0 w) :=
  (exists_pi2SepV M0 w).choose_spec z

noncomputable def pi2V (w : M0.V) : M0.V := sUnionV M0 (pi2SepV M0 w)

lemma pi2V_kpairV (a b : M0.V) : pi2V M0 (kpairV M0 a b) = b := by
  unfold pi2V
  have hsep : pi2SepV M0 (kpairV M0 a b) = singletonV M0 b := by
    apply extV M0
    intro z
    rw [mem_pi2SepV, sUnionV_kpairV, sInterV_kpairV, mem_doubletonV, mem_singletonV, mem_singletonV]
    by_cases hab : a = b
    · subst hab
      have hdd : doubletonV M0 a a = singletonV M0 a := rfl
      simp [hdd]
    · have hne : doubletonV M0 a b ≠ singletonV M0 a := by
        intro heq
        have : M0.mem b (singletonV M0 a) := heq ▸ (mem_doubletonV M0).mpr (Or.inr rfl)
        exact hab ((mem_singletonV M0).mp this).symm
      constructor
      · rintro ⟨rfl | rfl, h2⟩
        · exact (hne (h2 rfl)).elim
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, fun hba => (hab hba.symm).elim⟩
  rw [hsep, sUnionV_singletonV]

/- ## Section 3: Basic `mEv` Evaluations & Remaining ZFC Set Constructors -/

lemma mEv_e0 (e1 e2 : Fin 0 → M0.V) (φ : SetTheorySemisentence 0) :
    mEv M0 e1 φ ↔ mEv M0 e2 φ := by
  rw [Subsingleton.elim e1 e2]

lemma mEv_e1 (y : M0.V) (e : Fin 0 → M0.V) (φ : SetTheorySemisentence 1) :
    mEv M0 (y :> e) φ ↔ mEv M0 ![y] φ := by
  rw [Subsingleton.elim e ![]]

lemma mEv_congr {n : ℕ} {e₁ e₂ : Fin n → M0.V} (φ : SetTheorySemisentence n) (he : e₁ = e₂) :
    mEv M0 e₁ φ ↔ mEv M0 e₂ φ := by
  subst he; rfl

lemma mEv_subst1 {m : ℕ} (e : Fin m → M0.V) (φ : SetTheorySemisentence 1) (i₀ : Fin m) :
    mEv M0 e (φ ⇜ ![#i₀]) ↔ mEv M0 ![e i₀] φ := by
  rw [mEv_subst]
  refine mEv_congr M0 φ ?_
  funext k; fin_cases k; rfl

lemma mEv_subst2 {m : ℕ} (e : Fin m → M0.V) (φ : SetTheorySemisentence 2) (i₀ i₁ : Fin m) :
    mEv M0 e (φ ⇜ ![#i₀, #i₁]) ↔ mEv M0 ![e i₀, e i₁] φ := by
  rw [mEv_subst]
  refine mEv_congr M0 φ ?_
  funext k; fin_cases k <;> rfl

lemma mEv_subst3 {m : ℕ} (e : Fin m → M0.V) (φ : SetTheorySemisentence 3) (i₀ i₁ i₂ : Fin m) :
    mEv M0 e (φ ⇜ ![#i₀, #i₁, #i₂]) ↔ mEv M0 ![e i₀, e i₁, e i₂] φ := by
  rw [mEv_subst]
  refine mEv_congr M0 φ ?_
  funext k; fin_cases k <;> rfl

lemma ev_isEmpty (x : M0.V) : mEv M0 ![x] SetTheory.isEmpty ↔ x = emptyV M0 := by
  unfold SetTheory.isEmpty
  rw [mEv_all]
  constructor
  · intro h
    apply extV M0
    intro z
    have hz := h z
    rw [mEv_not, mEv_mem] at hz
    exact ⟨fun hzx => (hz hzx).elim, fun hze => (not_mem_emptyV M0 z hze).elim⟩
  · rintro rfl y
    rw [mEv_not, mEv_mem]
    exact not_mem_emptyV M0 y

lemma ev_isNonempty (x : M0.V) : mEv M0 ![x] SetTheory.isNonempty ↔ ∃ y : M0.V, M0.mem y x := Iff.rfl

lemma ev_isSubsetOf (x y : M0.V) :
    mEv M0 ![x, y] SetTheory.isSubsetOf ↔ ∀ z : M0.V, M0.mem z x → M0.mem z y := by
  unfold SetTheory.isSubsetOf
  rw [mEv_ballMem]
  rfl

lemma ev_doubleton (p x y : M0.V) :
    mEv M0 ![p, x, y] SetTheory.doubleton.dfn ↔ p = doubletonV M0 x y := by
  unfold SetTheory.doubleton.dfn
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ z : M0.V, M0.mem z p ↔ z = x ∨ z = y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [mEv_iff, mEv_mem, mEv_or, mEv_eq, mEv_eq]
    rfl
  · constructor
    · intro h
      apply extV M0
      intro z
      rw [h z, mem_doubletonV]
    · rintro rfl z
      rw [mem_doubletonV]

lemma ev_singleton (p x : M0.V) :
    mEv M0 ![p, x] SetTheory.singleton.dfn ↔ p = singletonV M0 x := by
  unfold SetTheory.singleton.dfn
  exact (mEv_subst3 M0 _ _ _ _ _).trans (ev_doubleton M0 p x x)

lemma ev_sUnion (u x : M0.V) :
    mEv M0 ![u, x] SetTheory.sUnion.dfn ↔ u = sUnionV M0 x := by
  unfold SetTheory.sUnion.dfn
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ z : M0.V, M0.mem z u ↔ ∃ w : M0.V, M0.mem w x ∧ M0.mem z w).trans ?_
  · refine forall_congr' fun z => ?_
    rw [mEv_iff, mEv_mem, mEv_bexsMem]
    rfl
  · constructor
    · intro h
      apply extV M0
      intro z
      rw [h z, mem_sUnionV]
    · rintro rfl z
      rw [mem_sUnionV]

lemma ev_union (u x y : M0.V) :
    mEv M0 ![u, x, y] SetTheory.union.dfn ↔ u = unionV M0 x y := by
  unfold SetTheory.union.dfn unionV
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ d : M0.V, d = doubletonV M0 x y → u = sUnionV M0 d).trans
    ⟨fun h => h (doubletonV M0 x y) rfl, fun h d hd => hd ▸ h⟩
  refine forall_congr' fun d => ?_
  rw [mEv_imp]
  exact imp_congr
    ((mEv_subst3 M0 _ _ _ _ _).trans (ev_doubleton M0 d x y))
    ((mEv_subst2 M0 _ _ _ _).trans (ev_sUnion M0 u d))

lemma ev_insert (u x y : M0.V) :
    mEv M0 ![u, x, y] SetTheory.insert.dfn ↔ u = insertV M0 x y := by
  unfold SetTheory.insert.dfn insertV
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ s : M0.V, s = singletonV M0 x → u = unionV M0 s y).trans
    ⟨fun h => h (singletonV M0 x) rfl, fun h s hs => hs ▸ h⟩
  refine forall_congr' fun s => ?_
  rw [mEv_imp]
  exact imp_congr
    ((mEv_subst2 M0 _ _ _ _).trans (ev_singleton M0 s x))
    ((mEv_subst3 M0 _ _ _ _ _).trans (ev_union M0 u s y))

lemma ev_sInter (u x : M0.V) :
    mEv M0 ![u, x] SetTheory.sInter.dfn ↔ u = sInterV M0 x := by
  unfold SetTheory.sInter.dfn
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ z : M0.V,
      M0.mem z u ↔ (∃ y : M0.V, M0.mem y x) ∧ ∀ y : M0.V, M0.mem y x → M0.mem z y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [mEv_iff, mEv_mem, mEv_and, mEv_ballMem]
    exact iff_congr Iff.rfl (and_congr ((mEv_subst1 M0 _ _ _).trans (ev_isNonempty M0 x)) Iff.rfl)
  · constructor
    · intro h
      apply extV M0
      intro z
      rw [h z, mem_sInterV]
    · rintro rfl z
      rw [mem_sInterV]

lemma ev_kpair (k x y : M0.V) :
    mEv M0 ![k, x, y] SetTheory.kpair.dfn ↔ k = kpairV M0 x y := by
  unfold SetTheory.kpair.dfn kpairV
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ x' : M0.V, x' = singletonV M0 x →
      ∀ z : M0.V, z = doubletonV M0 x y → k = doubletonV M0 x' z).trans
    ⟨fun h => h (singletonV M0 x) rfl (doubletonV M0 x y) rfl,
     fun h x' hx' z hz => by subst hx' hz; exact h⟩
  refine forall_congr' fun x' => ?_
  rw [mEv_imp, mEv_all]
  refine imp_congr ((mEv_subst2 M0 _ _ _ _).trans (ev_singleton M0 x' x)) (forall_congr' fun z => ?_)
  rw [mEv_imp]
  exact imp_congr
    ((mEv_subst3 M0 _ _ _ _ _).trans (ev_doubleton M0 z x y))
    ((mEv_subst3 M0 _ _ _ _ _).trans (ev_doubleton M0 k x' z))

lemma ev_pi1 (p w : M0.V) :
    mEv M0 ![p, w] SetTheory.kpair.π₁.dfn ↔ p = pi1V M0 w := by
  unfold SetTheory.kpair.π₁.dfn pi1V
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ i : M0.V, i = sInterV M0 w → p = sUnionV M0 i).trans
    ⟨fun h => h (sInterV M0 w) rfl, fun h i hi => hi ▸ h⟩
  refine forall_congr' fun i => ?_
  rw [mEv_imp]
  exact imp_congr
    ((mEv_subst2 M0 _ _ _ _).trans (ev_sInter M0 i w))
    ((mEv_subst2 M0 _ _ _ _).trans (ev_sUnion M0 p i))

lemma ev_pi2 (p w : M0.V) :
    mEv M0 ![p, w] SetTheory.kpair.π₂.dfn ↔ p = pi2V M0 w := by
  unfold SetTheory.kpair.π₂.dfn pi2V
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ u : M0.V, u = sUnionV M0 w → ∀ i : M0.V, i = sInterV M0 w →
      ∀ s : M0.V, (∀ z : M0.V, M0.mem z s ↔ M0.mem z u ∧ (M0.mem z i → u = i)) →
        p = sUnionV M0 s).trans ?_
  · refine forall_congr' fun u => ?_
    rw [mEv_imp, mEv_all]
    refine imp_congr ((mEv_subst2 M0 _ _ _ _).trans (ev_sUnion M0 u w)) (forall_congr' fun i => ?_)
    rw [mEv_imp, mEv_all]
    refine imp_congr ((mEv_subst2 M0 _ _ _ _).trans (ev_sInter M0 i w)) (forall_congr' fun s => ?_)
    rw [mEv_imp, mEv_all]
    refine imp_congr (forall_congr' fun z => ?_) ((mEv_subst2 M0 _ _ _ _).trans (ev_sUnion M0 p s))
    rw [mEv_iff, mEv_mem, mEv_and, mEv_mem, mEv_imp, mEv_mem, mEv_eq]
    rfl
  · constructor
    · intro h
      exact h (sUnionV M0 w) rfl (sInterV M0 w) rfl (pi2SepV M0 w) (fun z => mem_pi2SepV M0)
    · intro hp u hu i hi s hs
      subst hu hi
      have hseq : s = pi2SepV M0 w := extV M0 fun z => (hs z).trans (mem_pi2SepV M0).symm
      rw [hseq, hp]

lemma ev_succ (y x : M0.V) :
    mEv M0 ![y, x] SetTheory.succ.dfn ↔ y = insertV M0 x x := by
  unfold SetTheory.succ.dfn SetTheory.isSucc
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ z : M0.V, M0.mem z y ↔ z = x ∨ M0.mem z x).trans ?_
  · refine forall_congr' fun z => ?_
    rw [mEv_iff, mEv_mem, mEv_or, mEv_eq, mEv_mem]
    rfl
  · constructor
    · intro h
      apply extV M0
      intro z
      rw [h z, mem_insertV]
    · rintro rfl z
      rw [mem_insertV]

lemma ev_IsInductive (I : M0.V) :
    mEv M0 ![I] SetTheory.IsInductive.dfn ↔
      (M0.mem (emptyV M0) I ∧ ∀ y : M0.V, M0.mem y I → M0.mem (insertV M0 y y) I) := by
  unfold SetTheory.IsInductive.dfn
  rw [mEv_and, mEv_all, mEv_ballMem]
  refine and_congr ?_ ?_
  · refine (?_ : _ ↔ ∀ e : M0.V, e = emptyV M0 → M0.mem e I).trans
      ⟨fun h => h (emptyV M0) rfl, fun h e he => he.symm ▸ h⟩
    refine forall_congr' fun e => ?_
    rw [mEv_imp, mEv_mem]
    exact imp_congr ((mEv_subst1 M0 _ _ _).trans (ev_isEmpty M0 e)) Iff.rfl
  · refine forall₂_congr fun y _ => ?_
    rw [mEv_all]
    refine (?_ : _ ↔ ∀ y' : M0.V, y' = insertV M0 y y → M0.mem y' I).trans
      ⟨fun h => h (insertV M0 y y) rfl, fun h y' hy' => hy'.symm ▸ h⟩
    refine forall_congr' fun y' => ?_
    rw [mEv_imp, mEv_mem]
    exact imp_congr ((mEv_subst2 M0 _ _ _ _).trans (ev_succ M0 y' y)) Iff.rfl

/- Product, Von Neumann numerals, `vnOmegaV`, `relRangeV`, `funsV`, `zfcAppV` -/

lemma exists_prodV (X Y : M0.V) :
    ∃ P : M0.V, ∀ z : M0.V, M0.mem z P ↔
      ∃ x : M0.V, M0.mem x X ∧ ∃ y : M0.V, M0.mem y Y ∧ z = kpairV M0 x y := by
  let ambient := powersetV M0 (powersetV M0 (unionV M0 X Y))
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.bexsMem (&0)
      (Semiformula.bexsMem (&1)
        (Rew.subst ![#2, #1, #0] ▹ Rewriting.emb SetTheory.kpair.dfn))
  let ε : ℕ → M0.V := fun k => if k = 0 then X else Y
  obtain ⟨P, hP⟩ := sepV M0 ambient φ ε
  refine ⟨P, fun z => ?_⟩
  rw [hP z]
  have hφ : evalM M0.mem ![z] ε φ ↔
      ∃ x : M0.V, M0.mem x X ∧ ∃ y : M0.V, M0.mem y Y ∧ z = kpairV M0 x y := by
    dsimp only [φ]
    rw [evalM_bexsMem]
    refine exists_congr fun x => and_congr Iff.rfl ?_
    rw [evalM_bexsMem]
    refine exists_congr fun y => and_congr Iff.rfl ?_
    change evalM M0.mem (y :> x :> z :> ![]) ε
      ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#2, #1, #0]) ↔ _
    rw [evalM_subst, evalM_emb]
    refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).trans (ev_kpair M0 z x y)
    funext i; fin_cases i <;> rfl
  rw [hφ]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rcases h with ⟨x, hx, y, hy, rfl⟩
  rw [mem_powersetV]
  intro w hw
  rw [mem_powersetV]
  intro u hu
  rw [mem_unionV]
  rcases (mem_doubletonV M0).mp hw with rfl | rfl
  · rw [(mem_singletonV M0).mp hu]; exact Or.inl hx
  · rcases (mem_doubletonV M0).mp hu with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr hy

noncomputable def prodV (X Y : M0.V) : M0.V := (exists_prodV M0 X Y).choose

lemma mem_prodV {z X Y : M0.V} :
    M0.mem z (prodV M0 X Y) ↔
      ∃ x : M0.V, M0.mem x X ∧ ∃ y : M0.V, M0.mem y Y ∧ z = kpairV M0 x y :=
  (exists_prodV M0 X Y).choose_spec z

lemma kpairV_mem_prodV {x y X Y : M0.V} :
    M0.mem (kpairV M0 x y) (prodV M0 X Y) ↔ M0.mem x X ∧ M0.mem y Y := by
  rw [mem_prodV]
  constructor
  · rintro ⟨a, ha, b, hb, heq⟩
    obtain ⟨rfl, rfl⟩ := kpairV_inj M0 heq
    exact ⟨ha, hb⟩
  · rintro ⟨hx, hy⟩
    exact ⟨x, hx, y, hy, rfl⟩

lemma ev_prod (p X Y : M0.V) :
    mEv M0 ![p, X, Y] SetTheory.prod.dfn ↔ p = prodV M0 X Y := by
  unfold SetTheory.prod.dfn
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ z : M0.V, M0.mem z p ↔
      ∃ x : M0.V, M0.mem x X ∧ ∃ y : M0.V, M0.mem y Y ∧ z = kpairV M0 x y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [mEv_iff, mEv_mem, mEv_bexsMem]
    refine iff_congr Iff.rfl (exists_congr fun x => and_congr_right fun _ => ?_)
    rw [mEv_bexsMem]
    refine exists_congr fun y => and_congr_right fun _ => ?_
    exact (mEv_subst3 M0 _ _ _ _ _).trans (ev_kpair M0 z x y)
  · constructor
    · intro h
      apply extV M0
      intro z
      rw [h z, mem_prodV]
    · rintro rfl z
      rw [mem_prodV]

noncomputable def vnNatV : ℕ → M0.V
  | 0 => emptyV M0
  | k + 1 => insertV M0 (vnNatV k) (vnNatV k)

lemma mem_vnNatV_iff {x : M0.V} {m : ℕ} :
    M0.mem x (vnNatV M0 m) ↔ ∃ k < m, x = vnNatV M0 k := by
  induction m with
  | zero =>
    simp [vnNatV, not_mem_emptyV]
  | succ m ih =>
    simp only [vnNatV, mem_insertV, ih]
    constructor
    · rintro (rfl | ⟨k, hk, rfl⟩)
      · exact ⟨m, Nat.lt_succ_self m, rfl⟩
      · exact ⟨k, Nat.lt_succ_of_lt hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hlt, rfl⟩

lemma vnNatV_lt_mem {a b : ℕ} (h : a < b) : M0.mem (vnNatV M0 a) (vnNatV M0 b) :=
  (mem_vnNatV_iff M0).mpr ⟨a, h, rfl⟩

lemma vnNatV_inj : Function.Injective (vnNatV M0) := by
  intro a b hab
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · have hm := vnNatV_lt_mem M0 hlt
    rw [← hab] at hm
    exact (irreflV M0 _ hm).elim
  · rfl
  · have hm := vnNatV_lt_mem M0 hgt
    rw [hab] at hm
    exact (irreflV M0 _ hm).elim

lemma exists_inductiveV :
    ∃ I : M0.V, M0.mem (emptyV M0) I ∧ ∀ y : M0.V, M0.mem y I → M0.mem (insertV M0 y y) I := by
  have hax : mEv M0 Fin.elim0 Axiom.infinity :=
    M0.sat Axiom.infinity (Or.inl ZermeloFraenkel.axiom_of_infinity)
  unfold Axiom.infinity at hax
  rw [mEv_exs] at hax
  obtain ⟨I, hI⟩ := hax
  refine ⟨I, (ev_IsInductive M0 I).mp ?_⟩
  exact (mEv_congr M0 SetTheory.IsInductive.dfn (by funext i; fin_cases i; rfl)).mp hI

lemma exists_vnOmegaV :
    ∃ ω : M0.V, ∀ x : M0.V, M0.mem x ω ↔
      ∀ I : M0.V, (M0.mem (emptyV M0) I ∧ ∀ y : M0.V, M0.mem y I → M0.mem (insertV M0 y y) I) →
        M0.mem x I := by
  obtain ⟨I₀, hI₀⟩ := exists_inductiveV M0
  let φ : SetTheorySemiproposition 1 :=
    Rewriting.emb “x. ∀ I, !SetTheory.IsInductive.dfn I → x ∈ I”
  obtain ⟨ω, hω⟩ := sepV M0 I₀ φ (fun _ => emptyV M0)
  refine ⟨ω, fun x => ?_⟩
  rw [hω x]
  have hφ : evalM M0.mem ![x] (fun _ => emptyV M0) φ ↔
      ∀ I : M0.V, (M0.mem (emptyV M0) I ∧ ∀ y : M0.V, M0.mem y I → M0.mem (insertV M0 y y) I) →
        M0.mem x I := by
    dsimp only [φ]
    rw [evalM_emb]
    change mEv M0 ![x] “x. ∀ I, !SetTheory.IsInductive.dfn I → x ∈ I” ↔ _
    rw [mEv_all]
    refine forall_congr' fun I => ?_
    rw [mEv_imp, mEv_mem]
    exact imp_congr ((mEv_subst1 M0 _ _ _).trans (ev_IsInductive M0 I)) Iff.rfl
  rw [hφ]
  exact ⟨And.right, fun hall => ⟨hall I₀ hI₀, hall⟩⟩

noncomputable def vnOmegaV : M0.V := (exists_vnOmegaV M0).choose

lemma mem_vnOmegaV_iff {x : M0.V} :
    M0.mem x (vnOmegaV M0) ↔
      ∀ I : M0.V, (M0.mem (emptyV M0) I ∧ ∀ y : M0.V, M0.mem y I → M0.mem (insertV M0 y y) I) →
        M0.mem x I :=
  (exists_vnOmegaV M0).choose_spec x

lemma vnNatV_mem_vnOmegaV (k : ℕ) : M0.mem (vnNatV M0 k) (vnOmegaV M0) := by
  rw [mem_vnOmegaV_iff]
  intro I ⟨h0, hs⟩
  induction k with
  | zero => exact h0
  | succ k ih => exact hs (vnNatV M0 k) ih

lemma exists_relRangeV (R : M0.V) :
    ∃ r : M0.V, ∀ y : M0.V, M0.mem y r ↔ ∃ x : M0.V, M0.mem (kpairV M0 x y) R := by
  let ambient := sUnionV M0 (sUnionV M0 R)
  let φ : SetTheorySemiproposition 1 :=
    ∃¹ (∃¹
        ((Rew.subst ![#0, #1, #2] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋏
          Semiformula.rel Language.Set.Rel.mem ![#0, &0]))
  obtain ⟨r, hr⟩ := sepV M0 ambient φ (fun _ => R)
  refine ⟨r, fun y => ?_⟩
  rw [hr y]
  have hφ : evalM M0.mem ![y] (fun _ => R) φ ↔ ∃ x : M0.V, M0.mem (kpairV M0 x y) R := by
    dsimp only [φ]
    rw [evalM_exs]
    refine exists_congr fun x => ?_
    rw [evalM_exs]
    constructor
    · rintro ⟨p, hp1, hp2⟩
      change evalM M0.mem (p :> x :> y :> ![]) _
        ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #1, #2]) at hp1
      rw [evalM_subst, evalM_emb] at hp1
      have hpeq : p = kpairV M0 x y := (ev_kpair M0 p x y).mp (by
        refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mp hp1
        funext i; fin_cases i <;> rfl)
      subst hpeq
      exact hp2
    · intro hxy
      refine ⟨kpairV M0 x y, ?_, hxy⟩
      change evalM M0.mem (kpairV M0 x y :> x :> y :> ![]) _
        ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #1, #2])
      rw [evalM_subst, evalM_emb]
      refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mpr ((ev_kpair M0 _ x y).mpr rfl)
      funext i; fin_cases i <;> rfl
  rw [hφ]
  refine ⟨And.right, fun ⟨x, hx⟩ => ⟨?_, x, hx⟩⟩
  rw [mem_sUnionV]
  refine ⟨doubletonV M0 x y, ?_, (mem_doubletonV M0).mpr (Or.inr rfl)⟩
  rw [mem_sUnionV]
  exact ⟨kpairV M0 x y, hx, (mem_doubletonV M0).mpr (Or.inr rfl)⟩

noncomputable def relRangeV (R : M0.V) : M0.V := (exists_relRangeV M0 R).choose

lemma mem_relRangeV {y R : M0.V} :
    M0.mem y (relRangeV M0 R) ↔ ∃ x : M0.V, M0.mem (kpairV M0 x y) R :=
  (exists_relRangeV M0 R).choose_spec y

lemma exists_funsV (X Y : M0.V) :
    ∃ F : M0.V, ∀ f : M0.V, M0.mem f F ↔
      (∀ p : M0.V, M0.mem p f → M0.mem p (prodV M0 X Y)) ∧
      ∀ x : M0.V, M0.mem x X → ∃! y : M0.V, M0.mem (kpairV M0 x y) f := by
  let ambient := powersetV M0 (prodV M0 X Y)
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.ballMem (&0)
      (Semiformula.existsUnique
        (∃¹
          ((Rew.subst ![#0, #2, #1] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋏
            Semiformula.rel Language.Set.Rel.mem ![#0, #3])))
  obtain ⟨F, hF⟩ := sepV M0 ambient φ (fun _ => X)
  refine ⟨F, fun f => ?_⟩
  rw [hF f, mem_powersetV]
  refine and_congr Iff.rfl ?_
  dsimp only [φ]
  rw [evalM_ballMem]
  refine forall₂_congr fun x _ => ?_
  rw [evalM_existsUnique]
  refine existsUnique_congr fun y => ?_
  rw [evalM_exs]
  constructor
  · rintro ⟨p, hp1, hp2⟩
    change evalM M0.mem (p :> y :> x :> f :> ![]) _
      ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #2, #1]) at hp1
    rw [evalM_subst, evalM_emb] at hp1
    have hpeq : p = kpairV M0 x y := (ev_kpair M0 p x y).mp (by
      refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mp hp1
      funext i; fin_cases i <;> rfl)
    subst hpeq
    exact hp2
  · intro hxy
    refine ⟨kpairV M0 x y, ?_, hxy⟩
    change evalM M0.mem (kpairV M0 x y :> y :> x :> f :> ![]) _
      ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #2, #1])
    rw [evalM_subst, evalM_emb]
    refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mpr ((ev_kpair M0 _ x y).mpr rfl)
    funext i; fin_cases i <;> rfl

noncomputable def funsV (X Y : M0.V) : M0.V := (exists_funsV M0 X Y).choose

lemma mem_funsV {f X Y : M0.V} :
    M0.mem f (funsV M0 X Y) ↔
      (∀ p : M0.V, M0.mem p f → M0.mem p (prodV M0 X Y)) ∧
      ∀ x : M0.V, M0.mem x X → ∃! y : M0.V, M0.mem (kpairV M0 x y) f :=
  (exists_funsV M0 X Y).choose_spec f

lemma exists_zfcAppV (f x : M0.V) :
    ∃ v : M0.V, ∀ z : M0.V, M0.mem z v ↔
      M0.mem z (sUnionV M0 (relRangeV M0 f)) ∧ ∃ y : M0.V, M0.mem z y ∧ M0.mem (kpairV M0 x y) f := by
  let ambient := sUnionV M0 (relRangeV M0 f)
  let φ : SetTheorySemiproposition 1 :=
    ∃¹ (Semiformula.rel Language.Set.Rel.mem ![#1, #0] ⋏
        (∃¹ ((Rew.subst ![#0, &1, #1] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋏
            Semiformula.rel Language.Set.Rel.mem ![#0, &0])))
  let ε : ℕ → M0.V := fun k => if k = 0 then f else x
  obtain ⟨v, hv⟩ := sepV M0 ambient φ ε
  refine ⟨v, fun z => ?_⟩
  rw [hv z]
  refine and_congr Iff.rfl ?_
  dsimp only [φ]
  rw [evalM_exs]
  refine exists_congr fun y => ?_
  rw [evalM_and]
  refine and_congr Iff.rfl ?_
  rw [evalM_exs]
  constructor
  · rintro ⟨p, hp1, hp2⟩
    change evalM M0.mem (p :> y :> z :> ![]) ε
      ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, &1, #1]) at hp1
    rw [evalM_subst, evalM_emb] at hp1
    have hpeq : p = kpairV M0 x y := (ev_kpair M0 p x y).mp (by
      refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mp hp1
      funext i; fin_cases i <;> rfl)
    subst hpeq
    exact hp2
  · intro hxy
    refine ⟨kpairV M0 x y, ?_, hxy⟩
    change evalM M0.mem (kpairV M0 x y :> y :> z :> ![]) ε
      ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, &1, #1])
    rw [evalM_subst, evalM_emb]
    refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mpr ((ev_kpair M0 _ x y).mpr rfl)
    funext i; fin_cases i <;> rfl

noncomputable def zfcAppV (f x : M0.V) : M0.V := (exists_zfcAppV M0 f x).choose

lemma mem_zfcAppV {z f x : M0.V} :
    M0.mem z (zfcAppV M0 f x) ↔
      M0.mem z (sUnionV M0 (relRangeV M0 f)) ∧ ∃ y : M0.V, M0.mem z y ∧ M0.mem (kpairV M0 x y) f :=
  (exists_zfcAppV M0 f x).choose_spec z

lemma zfcAppV_of_unique {f x y : M0.V} (huniq : ∀ y' : M0.V, M0.mem (kpairV M0 x y') f ↔ y' = y) :
    zfcAppV M0 f x = y := by
  apply extV M0
  intro z
  rw [mem_zfcAppV]
  constructor
  · rintro ⟨_, y', hzy', hp⟩
    rw [(huniq y').mp hp] at hzy'
    exact hzy'
  · intro hzy
    have hmem : M0.mem (kpairV M0 x y) f := (huniq y).mpr rfl
    refine ⟨?_, y, hzy, hmem⟩
    rw [mem_sUnionV]
    exact ⟨y, (mem_relRangeV M0).mpr ⟨x, hmem⟩, hzy⟩

lemma zfcAppV_of_mem_funs {X Y f x y : M0.V}
    (hf : M0.mem f (funsV M0 X Y)) (hx : M0.mem x X) (hp : M0.mem (kpairV M0 x y) f) :
    zfcAppV M0 f x = y := by
  obtain ⟨_, huniq⟩ := (mem_funsV M0).mp hf
  obtain ⟨y0, hy0, hyeq⟩ := huniq x hx
  have hy : y = y0 := hyeq y hp
  subst hy
  exact zfcAppV_of_unique M0 fun y' => ⟨fun h => hyeq y' h, fun h => h ▸ hy0⟩

lemma zfcAppV_mem_codomain {X Y f x : M0.V}
    (hf : M0.mem f (funsV M0 X Y)) (hx : M0.mem x X) :
    M0.mem (zfcAppV M0 f x) Y := by
  obtain ⟨hsub, huniq⟩ := (mem_funsV M0).mp hf
  obtain ⟨y, hy, _⟩ := huniq x hx
  rw [zfcAppV_of_mem_funs M0 hf hx hy]
  exact ((kpairV_mem_prodV M0).mp (hsub _ hy)).2

lemma funsV_ext {X Y f1 f2 : M0.V}
    (hf1 : M0.mem f1 (funsV M0 X Y)) (hf2 : M0.mem f2 (funsV M0 X Y))
    (heq : ∀ x : M0.V, M0.mem x X → zfcAppV M0 f1 x = zfcAppV M0 f2 x) : f1 = f2 := by
  obtain ⟨hsub1, huniq1⟩ := (mem_funsV M0).mp hf1
  obtain ⟨hsub2, huniq2⟩ := (mem_funsV M0).mp hf2
  apply extV M0
  intro p
  constructor
  · intro hp1
    obtain ⟨x, hx, y, _, rfl⟩ := (mem_prodV M0).mp (hsub1 p hp1)
    have ha1 := zfcAppV_of_mem_funs M0 hf1 hx hp1
    obtain ⟨y2, hy2, _⟩ := huniq2 x hx
    have ha2 := zfcAppV_of_mem_funs M0 hf2 hx hy2
    have hy : y = y2 := by rw [← ha1, heq x hx, ha2]
    rwa [hy]
  · intro hp2
    obtain ⟨x, hx, y, _, rfl⟩ := (mem_prodV M0).mp (hsub2 p hp2)
    have ha2 := zfcAppV_of_mem_funs M0 hf2 hx hp2
    obtain ⟨y1, hy1, _⟩ := huniq1 x hx
    have ha1 := zfcAppV_of_mem_funs M0 hf1 hx hy1
    have hy : y = y1 := by rw [← ha2, ← heq x hx, ha1]
    rwa [hy]

/- Encoded integers, finite lists, configurations, and tapes inside `M0` -/

noncomputable def intSetV : M0.V := prodV M0 (vnNatV M0 2) (vnOmegaV M0)

noncomputable def encodeIntV : ℤ → M0.V
  | Int.ofNat k => kpairV M0 (vnNatV M0 0) (vnNatV M0 k)
  | Int.negSucc k => kpairV M0 (vnNatV M0 1) (vnNatV M0 k)

lemma encodeIntV_mem (z : ℤ) : M0.mem (encodeIntV M0 z) (intSetV M0) := by
  unfold intSetV
  cases z with
  | ofNat k =>
    exact (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 0 < 2), vnNatV_mem_vnOmegaV M0 k⟩
  | negSucc k =>
    exact (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 1 < 2), vnNatV_mem_vnOmegaV M0 k⟩

lemma encodeIntV_inj : Function.Injective (encodeIntV M0) := by
  intro z1 z2 heq
  cases z1 <;> cases z2 <;> dsimp only [encodeIntV] at heq
  · rw [vnNatV_inj M0 (kpairV_inj M0 heq).2]
  · exact absurd (vnNatV_inj M0 (kpairV_inj M0 heq).1) (by decide)
  · exact absurd (vnNatV_inj M0 (kpairV_inj M0 heq).1) (by decide)
  · rw [vnNatV_inj M0 (kpairV_inj M0 heq).2]

noncomputable def listToV : List M0.V → M0.V
  | [] => emptyV M0
  | x :: xs => insertV M0 x (listToV xs)

lemma mem_listToV {z : M0.V} {xs : List M0.V} :
    M0.mem z (listToV M0 xs) ↔ z ∈ xs := by
  induction xs with
  | nil => simp [listToV, not_mem_emptyV]
  | cons x xs ih => simp [listToV, mem_insertV, ih]

noncomputable def cfgSetV (N : ℕ) : M0.V :=
  prodV M0 (vnNatV M0 N) (prodV M0 (intSetV M0) (funsV M0 (intSetV M0) (vnNatV M0 2)))

lemma exists_emptyTapeV :
    ∃ g : M0.V, ∀ p : M0.V, M0.mem p g ↔ ∃ u : M0.V, M0.mem u (intSetV M0) ∧ p = kpairV M0 u (vnNatV M0 0) := by
  let ambient := prodV M0 (intSetV M0) (vnNatV M0 2)
  let φ : SetTheorySemiproposition 1 :=
    ∃¹ (Rew.subst ![#1, #0, &0] ▹ Rewriting.emb SetTheory.kpair.dfn)
  obtain ⟨g, hg⟩ := sepV M0 ambient φ (fun _ => vnNatV M0 0)
  refine ⟨g, fun p => ?_⟩
  rw [hg p]
  have hφ : evalM M0.mem ![p] (fun _ => vnNatV M0 0) φ ↔ ∃ u : M0.V, p = kpairV M0 u (vnNatV M0 0) := by
    dsimp only [φ]
    rw [evalM_exs]
    refine exists_congr fun u => ?_
    change evalM M0.mem (u :> p :> ![]) _
      ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#1, #0, &0]) ↔ _
    rw [evalM_subst, evalM_emb]
    refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).trans (ev_kpair M0 p u (vnNatV M0 0))
    funext i; fin_cases i <;> rfl
  rw [hφ]
  constructor
  · rintro ⟨hp, u, rfl⟩
    exact ⟨u, ((kpairV_mem_prodV M0).mp hp).1, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(kpairV_mem_prodV M0).mpr ⟨hu, vnNatV_lt_mem M0 (by decide : 0 < 2)⟩, u, rfl⟩

noncomputable def emptyTapeV : M0.V := (exists_emptyTapeV M0).choose

lemma mem_emptyTapeV {p : M0.V} :
    M0.mem p (emptyTapeV M0) ↔ ∃ u : M0.V, M0.mem u (intSetV M0) ∧ p = kpairV M0 u (vnNatV M0 0) :=
  (exists_emptyTapeV M0).choose_spec p

lemma emptyTapeV_mem_funs : M0.mem (emptyTapeV M0) (funsV M0 (intSetV M0) (vnNatV M0 2)) := by
  rw [mem_funsV]
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨u, hu, rfl⟩ := (mem_emptyTapeV M0).mp hp
    exact (kpairV_mem_prodV M0).mpr ⟨hu, vnNatV_lt_mem M0 (by decide : 0 < 2)⟩
  · intro u hu
    refine ⟨vnNatV M0 0, (mem_emptyTapeV M0).mpr ⟨u, hu, rfl⟩, fun y hy => ?_⟩
    obtain ⟨u', _, heq⟩ := (mem_emptyTapeV M0).mp hy
    exact (kpairV_inj M0 heq).2

lemma emptyTapeV_app {u : M0.V} (hu : M0.mem u (intSetV M0)) :
    zfcAppV M0 (emptyTapeV M0) u = vnNatV M0 0 :=
  zfcAppV_of_mem_funs M0 (emptyTapeV_mem_funs M0) hu ((mem_emptyTapeV M0).mpr ⟨u, hu, rfl⟩)

lemma exists_updateTapeV (g pos val : M0.V) :
    ∃ g' : M0.V, ∀ p : M0.V, M0.mem p g' ↔
      M0.mem p (prodV M0 (intSetV M0) (vnNatV M0 2)) ∧
      (p = kpairV M0 pos val ∨ (M0.mem p g ∧ ∀ v : M0.V, p ≠ kpairV M0 pos v)) := by
  let ambient := prodV M0 (intSetV M0) (vnNatV M0 2)
  let φ : SetTheorySemiproposition 1 :=
    (Rew.subst ![#0, &1, &2] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋎
      (Semiformula.rel Language.Set.Rel.mem ![#0, &0] ⋏
        (∀¹ (∼(Rew.subst ![#1, &1, #0] ▹ Rewriting.emb SetTheory.kpair.dfn))))
  let ε : ℕ → M0.V := fun k => if k = 0 then g else if k = 1 then pos else val
  obtain ⟨g', hg'⟩ := sepV M0 ambient φ ε
  refine ⟨g', fun p => ?_⟩
  rw [hg' p]
  refine and_congr Iff.rfl ?_
  dsimp only [φ]
  rw [evalM_or, evalM_and, evalM_all]
  refine or_congr ?_ (and_congr Iff.rfl (forall_congr' fun v => ?_))
  · change evalM M0.mem ![p] ε ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, &1, &2]) ↔ _
    rw [evalM_subst, evalM_emb]
    refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).trans (ev_kpair M0 p pos val)
    funext i; fin_cases i <;> rfl
  · rw [evalM_not]
    refine not_congr ?_
    change evalM M0.mem (v :> p :> ![]) ε ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#1, &1, #0]) ↔ _
    rw [evalM_subst, evalM_emb]
    refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).trans (ev_kpair M0 p pos v)
    funext i; fin_cases i <;> rfl

noncomputable def updateTapeV (g pos val : M0.V) : M0.V := (exists_updateTapeV M0 g pos val).choose

lemma mem_updateTapeV {p g pos val : M0.V} :
    M0.mem p (updateTapeV M0 g pos val) ↔
      M0.mem p (prodV M0 (intSetV M0) (vnNatV M0 2)) ∧
      (p = kpairV M0 pos val ∨ (M0.mem p g ∧ ∀ v : M0.V, p ≠ kpairV M0 pos v)) :=
  (exists_updateTapeV M0 g pos val).choose_spec p

lemma updateTapeV_mem_funs {g pos val : M0.V}
    (hg : M0.mem g (funsV M0 (intSetV M0) (vnNatV M0 2)))
    (hpos : M0.mem pos (intSetV M0)) (hval : M0.mem val (vnNatV M0 2)) :
    M0.mem (updateTapeV M0 g pos val) (funsV M0 (intSetV M0) (vnNatV M0 2)) := by
  obtain ⟨hsub, huniq⟩ := (mem_funsV M0).mp hg
  rw [mem_funsV]
  refine ⟨fun p hp => ((mem_updateTapeV M0).mp hp).1, fun u hu => ?_⟩
  by_cases hup : u = pos
  · subst hup
    refine ⟨val, (mem_updateTapeV M0).mpr ⟨(kpairV_mem_prodV M0).mpr ⟨hpos, hval⟩, Or.inl rfl⟩, ?_⟩
    intro y hy
    rcases ((mem_updateTapeV M0).mp hy).2 with heq | ⟨_, hne⟩
    · exact (kpairV_inj M0 heq).2
    · exact (hne y rfl).elim
  · obtain ⟨y0, hy0, hyeq⟩ := huniq u hu
    refine ⟨y0, ?_, ?_⟩
    · exact (mem_updateTapeV M0).mpr
        ⟨hsub _ hy0, Or.inr ⟨hy0, fun v heq => hup (kpairV_inj M0 heq).1⟩⟩
    · intro y hy
      rcases ((mem_updateTapeV M0).mp hy).2 with heq | ⟨hyg, _⟩
      · exact (hup (kpairV_inj M0 heq).1).elim
      · exact hyeq y hyg

lemma updateTapeV_app {g pos val u : M0.V}
    (hg : M0.mem g (funsV M0 (intSetV M0) (vnNatV M0 2)))
    (hpos : M0.mem pos (intSetV M0)) (hval : M0.mem val (vnNatV M0 2))
    (hu : M0.mem u (intSetV M0)) :
    zfcAppV M0 (updateTapeV M0 g pos val) u =
      if u = pos then val else zfcAppV M0 g u := by
  have hf := updateTapeV_mem_funs M0 hg hpos hval
  by_cases hup : u = pos
  · subst hup
    rw [if_pos rfl]
    exact zfcAppV_of_mem_funs M0 hf hpos
      ((mem_updateTapeV M0).mpr ⟨(kpairV_mem_prodV M0).mpr ⟨hpos, hval⟩, Or.inl rfl⟩)
  · rw [if_neg hup]
    obtain ⟨hsub, huniq⟩ := (mem_funsV M0).mp hg
    obtain ⟨y0, hy0, _⟩ := huniq u hu
    have happ_g : zfcAppV M0 g u = y0 := zfcAppV_of_mem_funs M0 hg hu hy0
    rw [happ_g]
    exact zfcAppV_of_mem_funs M0 hf hu
      ((mem_updateTapeV M0).mpr
        ⟨hsub _ hy0, Or.inr ⟨hy0, fun v heq => hup (kpairV_inj M0 heq).1⟩⟩)

/- ## Section 4: `EvalTermAt` Combinators and `Constant14` Evaluations in `M0` -/

def EvalTermAt {m : ℕ} (e : Fin m → M0.V) (Ψ : SetTheorySemisentence (m + 1)) (val : M0.V) : Prop :=
  ∀ y : M0.V, mEv M0 (y :> e) Ψ ↔ y = val

def DefinesConst (Ψ : SetTheorySemisentence 1) (c : M0.V) : Prop :=
  ∀ y : M0.V, mEv M0 ![y] Ψ ↔ y = c

lemma et_bvar_succ {m : ℕ} (e : Fin m → M0.V) (i : Fin m) :
    EvalTermAt M0 e (op(=).operator (#0 :> #(i.succ) :> ![])) (e i) := by
  intro y
  change y = (y :> e) i.succ ↔ y = e i
  rfl

lemma et_bvar1 {m : ℕ} (a : M0.V) (e : Fin m → M0.V) :
    EvalTermAt M0 (a :> e) (op(=).operator (#0 :> #1 :> ![])) a :=
  et_bvar_succ M0 (a :> e) 0

lemma et_bvar2 {m : ℕ} (a b : M0.V) (e : Fin m → M0.V) :
    EvalTermAt M0 (a :> b :> e) (op(=).operator (#0 :> #2 :> ![])) b :=
  et_bvar_succ M0 (a :> b :> e) 1

lemma et_bvar3 {m : ℕ} (a b c : M0.V) (e : Fin m → M0.V) :
    EvalTermAt M0 (a :> b :> c :> e) (op(=).operator (#0 :> #3 :> ![])) c :=
  et_bvar_succ M0 (a :> b :> c :> e) 2

lemma et_bvar4 {m : ℕ} (a b c d : M0.V) (e : Fin m → M0.V) :
    EvalTermAt M0 (a :> b :> c :> d :> e) (op(=).operator (#0 :> #4 :> ![])) d :=
  et_bvar_succ M0 (a :> b :> c :> d :> e) 3

lemma et_bvar5 {m : ℕ} (a b c d f : M0.V) (e : Fin m → M0.V) :
    EvalTermAt M0 (a :> b :> c :> d :> f :> e) (op(=).operator (#0 :> #5 :> ![])) f :=
  et_bvar_succ M0 (a :> b :> c :> d :> f :> e) 4

lemma et_bvar6 {m : ℕ} (a b c d f g : M0.V) (e : Fin m → M0.V) :
    EvalTermAt M0 (a :> b :> c :> d :> f :> g :> e) (op(=).operator (#0 :> #6 :> ![])) g :=
  et_bvar_succ M0 (a :> b :> c :> d :> f :> g :> e) 5

lemma ev_nestFunc0_raw {m : ℕ} (φ : SetTheorySemisentence 1) (y : M0.V) (e : Fin m → M0.V) :
    mEv M0 (y :> e) (Semiformula.nestFormulaeFunc φ ![]) ↔ mEv M0 ![y] φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj]
  rw [mEv_imp, mEv_top, mEv_subst]
  simp only [true_imp_iff]
  refine mEv_congr M0 φ ?_
  funext i; fin_cases i; rfl

lemma et_const0 {m : ℕ} {Ψ : SetTheorySemisentence 1} {c : M0.V}
    (hΨ : DefinesConst M0 Ψ c) (e : Fin m → M0.V) :
    EvalTermAt M0 e (Semiformula.nestFormulaeFunc Ψ ![]) c := by
  intro y
  rw [ev_nestFunc0_raw]
  exact hΨ y

lemma ev_nestFunc1_raw {m : ℕ} (φ : SetTheorySemisentence 2)
    {e : Fin m → M0.V} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : M0.V}
    (h₀ : EvalTermAt M0 e Ψ₀ v₀) (y : M0.V) :
    mEv M0 (y :> e) (Semiformula.nestFormulaeFunc φ ![Ψ₀]) ↔ mEv M0 ![y, v₀] φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj]
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ d₀ : M0.V, d₀ = v₀ → mEv M0 ![y, d₀] φ).trans
    ⟨fun h => h v₀ rfl, fun h d₀ hd => hd ▸ h⟩
  refine forall_congr' fun d₀ => ?_
  rw [mEv_imp, mEv_and, mEv_top, and_true, mEv_subst, mEv_subst]
  have he0 : (fun k : Fin (m + 1) =>
      tvRaw (d₀ :> y :> e) Empty.elim
        ((#((0 : Fin 1).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 1)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rfl
  have he1 : (fun k : Fin 2 =>
      tvRaw (d₀ :> y :> e) Empty.elim
        ((#((0 : Fin (m + 1)).addNat 1) :> fun i : Fin 1 => #(i.addCast m.succ)) k)) =
      ![y, d₀] := by
    funext k; fin_cases k <;> rfl
  rw [he0, he1]
  exact imp_congr (h₀ d₀) Iff.rfl

lemma et_comp1 {m : ℕ} {φ : SetTheorySemisentence 2} {G : M0.V → M0.V}
    (hφ : ∀ y x₀ : M0.V, mEv M0 ![y, x₀] φ ↔ y = G x₀)
    {e : Fin m → M0.V} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : M0.V}
    (h₀ : EvalTermAt M0 e Ψ₀ v₀) :
    EvalTermAt M0 e (Semiformula.nestFormulaeFunc φ ![Ψ₀]) (G v₀) := by
  intro y
  rw [ev_nestFunc1_raw M0 φ h₀ y, hφ y v₀]

lemma ev_nestFunc2_raw {m : ℕ} (φ : SetTheorySemisentence 3)
    {e : Fin m → M0.V} {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : M0.V}
    (h₀ : EvalTermAt M0 e Ψ₀ v₀) (h₁ : EvalTermAt M0 e Ψ₁ v₁) (y : M0.V) :
    mEv M0 (y :> e) (Semiformula.nestFormulaeFunc φ ![Ψ₀, Ψ₁]) ↔ mEv M0 ![y, v₀, v₁] φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj]
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ d₁ d₀ : M0.V, (d₀ = v₀ ∧ d₁ = v₁) → mEv M0 ![y, d₀, d₁] φ).trans
    ⟨fun h => h v₁ v₀ ⟨rfl, rfl⟩, fun h d₁ d₀ ⟨hd0, hd1⟩ => by subst hd0 hd1; exact h⟩
  refine forall_congr' fun d₁ => ?_
  rw [mEv_all]
  refine forall_congr' fun d₀ => ?_
  dsimp only [Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  rw [mEv_imp, mEv_and, mEv_and, mEv_top, and_true, mEv_subst, mEv_subst, mEv_subst]
  have he_psi0 : (fun k : Fin (m + 1) =>
      tvRaw (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((0 : Fin 2).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 2)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases rfl (fun j => rfl) k
  have he_psi1 : (fun k : Fin (m + 1) =>
      tvRaw (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((1 : Fin 2).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 2)) k)) =
      (d₁ :> e) := by
    have h1 : ((1 : Fin 2).addCast m.succ) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    refine Fin.cases ?_ (fun j => rfl) k
    simp [h1, tvRaw]
  have he_phi : (fun k : Fin 3 =>
      tvRaw (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((0 : Fin (m + 1)).addNat 2) :> fun i : Fin 2 => #(i.addCast m.succ)) k)) =
      ![y, d₀, d₁] := by
    have h1 : ((1 : Fin 2).addCast m.succ) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    fin_cases k
    · rfl
    · rfl
    · change tvRaw (d₀ :> d₁ :> y :> e) Empty.elim (#((1 : Fin 2).addCast m.succ)) = d₁
      simp [h1, tvRaw]
  rw [he_psi0, he_psi1, he_phi]
  exact imp_congr (and_congr (h₀ d₀) (h₁ d₁)) Iff.rfl

lemma et_comp2 {m : ℕ} {φ : SetTheorySemisentence 3} {G : M0.V → M0.V → M0.V}
    (hφ : ∀ y x₀ x₁ : M0.V, mEv M0 ![y, x₀, x₁] φ ↔ y = G x₀ x₁)
    {e : Fin m → M0.V} {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : M0.V}
    (h₀ : EvalTermAt M0 e Ψ₀ v₀) (h₁ : EvalTermAt M0 e Ψ₁ v₁) :
    EvalTermAt M0 e (Semiformula.nestFormulaeFunc φ ![Ψ₀, Ψ₁]) (G v₀ v₁) := by
  intro y
  rw [ev_nestFunc2_raw M0 φ h₀ h₁ y, hφ y v₀ v₁]

lemma ev_nest1 {m : ℕ} (φ : SetTheorySemisentence 1)
    {e : Fin m → M0.V} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : M0.V}
    (h₀ : EvalTermAt M0 e Ψ₀ v₀) :
    mEv M0 e (Semiformula.nestFormulae φ ![Ψ₀]) ↔ mEv M0 ![v₀] φ := by
  dsimp only [Semiformula.nestFormulae, FFL.FirstOrder.allItr, Matrix.conj]
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ d₀ : M0.V, d₀ = v₀ → mEv M0 ![d₀] φ).trans
    ⟨fun h => h v₀ rfl, fun h d₀ hd => hd ▸ h⟩
  refine forall_congr' fun d₀ => ?_
  rw [mEv_imp, mEv_and, mEv_top, and_true, mEv_subst, mEv_subst]
  have he0 : (fun k : Fin (m + 1) =>
      tvRaw (d₀ :> e) Empty.elim
        ((#((0 : Fin 1).addCast m) :> fun j : Fin m => #(j.addNat 1)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases rfl (fun j => rfl) k
  have he1 : (fun k : Fin 1 =>
      tvRaw (d₀ :> e) Empty.elim (#(k.addCast m))) = ![d₀] := by
    funext k; fin_cases k; rfl
  rw [he0, he1]
  exact imp_congr (h₀ d₀) Iff.rfl

lemma ev_nest2 {m : ℕ} (φ : SetTheorySemisentence 2)
    {e : Fin m → M0.V} {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : M0.V}
    (h₀ : EvalTermAt M0 e Ψ₀ v₀) (h₁ : EvalTermAt M0 e Ψ₁ v₁) :
    mEv M0 e (Semiformula.nestFormulae φ ![Ψ₀, Ψ₁]) ↔ mEv M0 ![v₀, v₁] φ := by
  dsimp only [Semiformula.nestFormulae, FFL.FirstOrder.allItr, Matrix.conj]
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ d₁ d₀ : M0.V, (d₀ = v₀ ∧ d₁ = v₁) → mEv M0 ![d₀, d₁] φ).trans
    ⟨fun h => h v₁ v₀ ⟨rfl, rfl⟩, fun h d₁ d₀ ⟨hd0, hd1⟩ => by subst hd0 hd1; exact h⟩
  refine forall_congr' fun d₁ => ?_
  rw [mEv_all]
  refine forall_congr' fun d₀ => ?_
  dsimp only [Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  rw [mEv_imp, mEv_and, mEv_and, mEv_top, and_true, mEv_subst, mEv_subst, mEv_subst]
  have he0 : (fun k : Fin (m + 1) =>
      tvRaw (d₀ :> d₁ :> e) Empty.elim
        ((#((0 : Fin 2).addCast m) :> fun j : Fin m => #(j.addNat 2)) k)) =
      (d₀ :> e) := by
    funext k; refine Fin.cases rfl (fun j => rfl) k
  have he1 : (fun k : Fin (m + 1) =>
      tvRaw (d₀ :> d₁ :> e) Empty.elim
        ((#((1 : Fin 2).addCast m) :> fun j : Fin m => #(j.addNat 2)) k)) =
      (d₁ :> e) := by
    have h1 : ((1 : Fin 2).addCast m) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    refine Fin.cases ?_ (fun j => rfl) k
    simp [h1, tvRaw]
  have he_phi : (fun k : Fin 2 =>
      tvRaw (d₀ :> d₁ :> e) Empty.elim (#(k.addCast m))) = ![d₀, d₁] := by
    have h1 : ((1 : Fin 2).addCast m) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    fin_cases k
    · rfl
    · change tvRaw (d₀ :> d₁ :> e) Empty.elim (#((1 : Fin 2).addCast m)) = d₁
      simp [h1, tvRaw]
  rw [he0, he1, he_phi]
  exact imp_congr (and_congr (h₀ d₀) (h₁ d₁)) Iff.rfl

lemma ev_faf_eq {m : ℕ} {e : Fin m → M0.V}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : M0.V} (h₁ : EvalTermAt M0 e T₁ v₁) (h₂ : EvalTermAt M0 (v₁ :> e) T₂ v₂) :
    mEv M0 e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 op(=).operator (#1 :> #0 :> ![])))) ↔ v₁ = v₂ := by
  rw [mEv_all]
  constructor
  · intro h
    have hv1 := (mEv_imp M0 _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [mEv_all] at hv1
    exact (mEv_imp M0 _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
  · intro heq d₁
    rw [mEv_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [mEv_all]
    intro d₂
    rw [mEv_imp]
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    exact heq

lemma ev_faf_ne {m : ℕ} {e : Fin m → M0.V}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : M0.V} (h₁ : EvalTermAt M0 e T₁ v₁) (h₂ : EvalTermAt M0 (v₁ :> e) T₂ v₂) :
    mEv M0 e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 ∼op(=).operator (#1 :> #0 :> ![])))) ↔ v₁ ≠ v₂ := by
  rw [mEv_all]
  constructor
  · intro h
    have hv1 := (mEv_imp M0 _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [mEv_all] at hv1
    have hv2 := (mEv_imp M0 _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rwa [mEv_not, mEv_eq] at hv2
  · intro hne d₁
    rw [mEv_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [mEv_all]
    intro d₂
    rw [mEv_imp]
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    rw [mEv_not, mEv_eq]
    exact hne

lemma ev_faf_mem {m : ℕ} {e : Fin m → M0.V}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : M0.V} (h₁ : EvalTermAt M0 e T₁ v₁) (h₂ : EvalTermAt M0 (v₁ :> e) T₂ v₂) :
    mEv M0 e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 Semiformula.Operator.Mem.mem.operator (#1 :> #0 :> ![])))) ↔
      M0.mem v₁ v₂ := by
  rw [mEv_all]
  constructor
  · intro h
    have hv1 := (mEv_imp M0 _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [mEv_all] at hv1
    exact (mEv_imp M0 _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
  · intro hmem d₁
    rw [mEv_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [mEv_all]
    intro d₂
    rw [mEv_imp]
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    exact hmem

lemma ev_faf_notMem {m : ℕ} {e : Fin m → M0.V}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : M0.V} (h₁ : EvalTermAt M0 e T₁ v₁) (h₂ : EvalTermAt M0 (v₁ :> e) T₂ v₂) :
    mEv M0 e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 ∼Semiformula.Operator.Mem.mem.operator (#1 :> #0 :> ![])))) ↔
      ¬ M0.mem v₁ v₂ := by
  rw [mEv_all]
  constructor
  · intro h
    have hv1 := (mEv_imp M0 _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [mEv_all] at hv1
    have hv2 := (mEv_imp M0 _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rwa [mEv_not, mEv_mem] at hv2
  · intro hnm d₁
    rw [mEv_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [mEv_all]
    intro d₂
    rw [mEv_imp]
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    rw [mEv_not, mEv_mem]
    exact hnm

lemma ev_faf_ball {m : ℕ} {e : Fin m → M0.V}
    {T₁ : SetTheorySemisentence (m + 1)} {v₁ : M0.V}
    (h₁ : EvalTermAt M0 e T₁ v₁) (φ : SetTheorySemisentence (m + 2)) :
    mEv M0 e (∀¹ (T₁ 🡒 Semiformula.ballMem (#0) φ)) ↔
      ∀ x : M0.V, M0.mem x v₁ → mEv M0 (x :> v₁ :> e) φ := by
  rw [mEv_all]
  constructor
  · intro h x hx
    have hv1 := (mEv_imp M0 _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [mEv_ballMem] at hv1
    exact hv1 x hx
  · intro h d₁
    rw [mEv_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [mEv_ballMem]
    exact h

lemma ev_faf_bexs {m : ℕ} {e : Fin m → M0.V}
    {T₁ : SetTheorySemisentence (m + 1)} {v₁ : M0.V}
    (h₁ : EvalTermAt M0 e T₁ v₁) (φ : SetTheorySemisentence (m + 2)) :
    mEv M0 e (∀¹ (T₁ 🡒 Semiformula.bexsMem (#0) φ)) ↔
      ∃ x : M0.V, M0.mem x v₁ ∧ mEv M0 (x :> v₁ :> e) φ := by
  rw [mEv_all]
  constructor
  · intro h
    have hv1 := (mEv_imp M0 _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [mEv_bexsMem] at hv1
    exact hv1
  · intro h d₁
    rw [mEv_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [mEv_bexsMem]
    exact h

lemma dc_isω : DefinesConst M0 SetTheory.isω (vnOmegaV M0) := by
  intro w
  unfold SetTheory.isω
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ x : M0.V, M0.mem x w ↔
      ∀ I : M0.V, (M0.mem (emptyV M0) I ∧ ∀ y : M0.V, M0.mem y I → M0.mem (insertV M0 y y) I) →
        M0.mem x I).trans ?_
  · refine forall_congr' fun x => ?_
    rw [mEv_iff, mEv_mem, mEv_all]
    refine iff_congr Iff.rfl (forall_congr' fun I => ?_)
    rw [mEv_imp, mEv_mem]
    exact imp_congr ((mEv_subst1 M0 _ _ _).trans (ev_IsInductive M0 I)) Iff.rfl
  · constructor
    · intro h
      apply extV M0
      intro x
      rw [h x, mem_vnOmegaV_iff]
    · rintro rfl x
      rw [mem_vnOmegaV_iff]

lemma ev_range (r R : M0.V) :
    mEv M0 ![r, R] SetTheory.range.dfn ↔ r = relRangeV M0 R := by
  unfold SetTheory.range.dfn
  change mEv M0 ![r, R] (∀¹ _) ↔ _
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ y : M0.V, M0.mem y r ↔ ∃ x : M0.V, M0.mem (kpairV M0 x y) R).trans ?_
  · refine forall_congr' fun y => ?_
    rw [mEv_iff]
    refine iff_congr (ev_faf_mem M0 (et_bvar1 M0 y _) (et_bvar3 M0 _ y r _)) ?_
    rw [mEv_exs]
    refine exists_congr fun x => ?_
    exact ev_faf_mem M0
      (et_comp2 M0 (ev_kpair M0) (et_bvar1 M0 x _) (et_bvar2 M0 x y _))
      (et_bvar5 M0 _ x y r R _)
  · constructor
    · intro h
      apply extV M0
      intro y
      rw [h y, mem_relRangeV]
    · rintro rfl y
      rw [mem_relRangeV]

lemma ev_function (F Y X : M0.V) :
    mEv M0 ![F, Y, X] SetTheory.function.dfn ↔ F = funsV M0 X Y := by
  unfold SetTheory.function.dfn
  change mEv M0 ![F, Y, X] (∀¹ _) ↔ _
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ f : M0.V, M0.mem f F ↔ M0.mem f (funsV M0 X Y)).trans ?_
  · refine forall_congr' fun f => ?_
    rw [mEv_iff]
    refine iff_congr (ev_faf_mem M0 (et_bvar1 M0 f _) (et_bvar3 M0 _ f F _)) ?_
    rw [mEv_and, mem_funsV]
    refine and_congr ?_ ?_
    · rw [ev_nest2 M0 SetTheory.isSubsetOf (et_bvar1 M0 f _)
        (et_comp2 M0 (ev_prod M0) (et_bvar4 M0 f F Y X _) (et_bvar3 M0 f F Y _)), ev_isSubsetOf]
    · rw [ev_faf_ball M0 (et_bvar4 M0 f F Y X _)]
      refine forall₂_congr fun x _ => ?_
      rw [mEv_existsUnique]
      refine existsUnique_congr fun y => ?_
      exact ev_faf_mem M0
        (et_comp2 M0 (ev_kpair M0) (et_bvar2 M0 y x _) (et_bvar1 M0 y _))
        (et_bvar5 M0 _ y x _ f _)
  · constructor
    · intro h; exact extV M0 h
    · rintro rfl f; rfl

lemma ev_value (v f x : M0.V) :
    mEv M0 ![v, f, x] SetTheory.value.dfn ↔ v = zfcAppV M0 f x := by
  unfold SetTheory.value.dfn
  change mEv M0 ![v, f, x] (∀¹ _) ↔ _
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ z : M0.V, M0.mem z v ↔
      M0.mem z (sUnionV M0 (relRangeV M0 f)) ∧ ∃ y : M0.V, M0.mem z y ∧ M0.mem (kpairV M0 x y) f).trans ?_
  · refine forall_congr' fun z => ?_
    rw [mEv_iff]
    refine iff_congr (ev_faf_mem M0 (et_bvar1 M0 z _) (et_bvar3 M0 _ z v _)) ?_
    rw [mEv_and]
    refine and_congr ?_ ?_
    · exact ev_faf_mem M0 (et_bvar1 M0 z _)
        (et_comp1 M0 (ev_sUnion M0) (et_comp1 M0 (ev_range M0) (et_bvar4 M0 _ z v f _)))
    · rw [mEv_exs]
      refine exists_congr fun y => ?_
      rw [mEv_and]
      refine and_congr
        (ev_faf_mem M0 (et_bvar2 M0 y z _) (et_bvar2 M0 _ y _))
        (ev_faf_mem M0 (et_comp2 M0 (ev_kpair M0) (et_bvar5 M0 y z v f x _) (et_bvar1 M0 y _))
          (et_bvar5 M0 _ y z v f _))
  · constructor
    · intro h
      apply extV M0
      intro z
      rw [h z, mem_zfcAppV]
    · rintro rfl z
      rw [mem_zfcAppV]

/- `Constant14` evaluations -/

lemma dc_zero : DefinesConst M0 Constant14.zero (emptyV M0) := by
  intro z
  unfold Constant14.zero
  exact (mEv_subst1 M0 _ _ _).trans (ev_isEmpty M0 z)

lemma dc_numeral (k : ℕ) : DefinesConst M0 (Constant14.numeral k) (vnNatV M0 k) := by
  induction k with
  | zero => exact dc_zero M0
  | succ k ih =>
    intro y
    unfold Constant14.numeral vnNatV
    exact et_comp1 M0 (ev_succ M0) ih y

lemma dc_setPair {Ψ₁ Ψ₂ : SetTheorySemisentence 1} {v₁ v₂ : M0.V}
    (h₁ : DefinesConst M0 Ψ₁ v₁) (h₂ : DefinesConst M0 Ψ₂ v₂) :
    DefinesConst M0 (Constant14.setPair Ψ₁ Ψ₂) (kpairV M0 v₁ v₂) := by
  intro y
  unfold Constant14.setPair
  have h := et_comp2 M0 (ev_kpair M0) (h₁ ·) (h₂ ·) y
  rwa [mEv_e1] at h

lemma dc_setTriple {Ψ₁ Ψ₂ Ψ₃ : SetTheorySemisentence 1} {v₁ v₂ v₃ : M0.V}
    (h₁ : DefinesConst M0 Ψ₁ v₁) (h₂ : DefinesConst M0 Ψ₂ v₂) (h₃ : DefinesConst M0 Ψ₃ v₃) :
    DefinesConst M0 (Constant14.setTriple Ψ₁ Ψ₂ Ψ₃) (kpairV M0 v₁ (kpairV M0 v₂ v₃)) :=
  dc_setPair M0 h₁ (dc_setPair M0 h₂ h₃)

lemma dc_finiteSet_map {α : Type*} (l : List α)
    (fForm : α → SetTheorySemisentence 1) (fVal : α → M0.V)
    (hf : ∀ a, DefinesConst M0 (fForm a) (fVal a)) :
    DefinesConst M0 (Constant14.finiteSet (l.map fForm)) (listToV M0 (l.map fVal)) := by
  induction l with
  | nil => exact dc_zero M0
  | cons a as ih =>
    intro y
    simp only [List.map_cons, Constant14.finiteSet, listToV]
    have h := et_comp2 M0 (ev_insert M0) (hf a ·) (ih ·) y
    rwa [mEv_e1] at h

lemma dc_integers : DefinesConst M0 Constant14.integers (intSetV M0) := by
  intro y
  unfold Constant14.integers intSetV
  exact ev_faf_eq M0 (et_bvar1 M0 y _)
    (et_comp2 M0 (ev_prod M0) (et_const0 M0 (dc_numeral M0 2) _) (et_const0 M0 (dc_isω M0) _))

lemma dc_integerZero : DefinesConst M0 Constant14.integerZero (encodeIntV M0 0) := by
  intro y
  unfold Constant14.integerZero
  exact ev_faf_eq M0 (et_bvar1 M0 y _)
    (et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_numeral M0 0) _) (et_const0 M0 (dc_numeral M0 0) _))

lemma ev_integerSucc_of_mem {w : M0.V} (hw : M0.mem w (intSetV M0)) (w' : M0.V) :
    mEv M0 ![w', w] Constant14.integerSucc.dfn ↔
      ((pi1V M0 w = vnNatV M0 0 ∧
          w' = kpairV M0 (vnNatV M0 0) (insertV M0 (pi2V M0 w) (pi2V M0 w))) ∨
        (pi1V M0 w = vnNatV M0 1 ∧
          ((pi2V M0 w = vnNatV M0 0 ∧ w' = encodeIntV M0 0) ∨
            ∃ m : M0.V, M0.mem m (vnOmegaV M0) ∧ pi2V M0 w = insertV M0 m m ∧
              w' = kpairV M0 (vnNatV M0 1) m))) := by
  unfold Constant14.integerSucc.dfn
  rw [mEv_or, mEv_and, mEv_and]
  rw [ev_faf_mem M0 (et_bvar2 M0 w' w _) (et_const0 M0 (dc_integers M0) _),
      ev_faf_notMem M0 (et_bvar2 M0 w' w _) (et_const0 M0 (dc_integers M0) _)]
  simp only [hw, not_true_eq_false, false_and, or_false, true_and]
  rw [mEv_or, mEv_and, mEv_and, mEv_or, mEv_and]
  refine or_congr
    (and_congr
      (ev_faf_eq M0 (et_comp1 M0 (ev_pi1 M0) (et_bvar2 M0 w' w _)) (et_const0 M0 (dc_numeral M0 0) _))
      (ev_faf_eq M0 (et_bvar1 M0 w' _)
        (et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_numeral M0 0) _)
          (et_comp1 M0 (ev_succ M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar3 M0 _ w' w _))))))
    (and_congr
      (ev_faf_eq M0 (et_comp1 M0 (ev_pi1 M0) (et_bvar2 M0 w' w _)) (et_const0 M0 (dc_numeral M0 1) _))
      (or_congr
        (and_congr
          (ev_faf_eq M0 (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 w' w _)) (et_const0 M0 (dc_numeral M0 0) _))
          (ev_faf_eq M0 (et_bvar1 M0 w' _) (et_const0 M0 (dc_integerZero M0) _)))
        ?_))
  rw [ev_faf_bexs M0 (et_const0 M0 (dc_isω M0) _)]
  refine exists_congr fun m => and_congr_right fun _ => ?_
  rw [mEv_and]
  exact and_congr
    (ev_faf_eq M0 (et_comp1 M0 (ev_pi2 M0) (et_bvar4 M0 m (vnOmegaV M0) w' w _))
      (et_comp1 M0 (ev_succ M0) (et_bvar2 M0 _ m _)))
    (ev_faf_eq M0 (et_bvar3 M0 m (vnOmegaV M0) w' _)
      (et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_numeral M0 1) _) (et_bvar2 M0 _ m _)))

lemma ev_integerSucc_encode (z : ℤ) (w' : M0.V) :
    mEv M0 ![w', encodeIntV M0 z] Constant14.integerSucc.dfn ↔ w' = encodeIntV M0 (z + 1) := by
  rw [ev_integerSucc_of_mem M0 (encodeIntV_mem M0 z)]
  have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
  have h10 : vnNatV M0 1 ≠ vnNatV M0 0 := h01.symm
  cases z with
  | ofNat k =>
    simp only [encodeIntV, pi1V_kpairV, pi2V_kpairV, h01, false_and, or_false, true_and]
    rfl
  | negSucc k =>
    simp only [encodeIntV, pi1V_kpairV, pi2V_kpairV, h10, false_and, false_or, true_and]
    cases k with
    | zero =>
      have hno : ¬ ∃ m : M0.V, M0.mem m (vnOmegaV M0) ∧
          vnNatV M0 0 = insertV M0 m m ∧ w' = kpairV M0 (vnNatV M0 1) m := by
        rintro ⟨m, _, hm, _⟩
        have : M0.mem m (vnNatV M0 0) := hm ▸ (mem_insertV M0).mpr (Or.inl rfl)
        exact not_mem_emptyV M0 m this
      simp only [true_and, hno, or_false]
      rfl
    | succ k =>
      have hne0 : vnNatV M0 (k + 1) ≠ vnNatV M0 0 := fun h => absurd (vnNatV_inj M0 h) (by omega)
      simp only [hne0, false_and, false_or]
      constructor
      · rintro ⟨m, _, hsucc, rfl⟩
        have hm : vnNatV M0 k = m := succV_inj M0 hsucc
        subst hm
        rfl
      · rintro rfl
        exact ⟨vnNatV M0 k, vnNatV_mem_vnOmegaV M0 k, rfl, rfl⟩

lemma ev_integerPred_encode (z : ℤ) (w' : M0.V) :
    mEv M0 ![w', encodeIntV M0 z] Constant14.integerPred.dfn ↔ w' = encodeIntV M0 (z - 1) := by
  unfold Constant14.integerPred.dfn
  rw [mEv_or, mEv_and, mEv_and, mEv_and]
  rw [ev_faf_mem M0 (et_bvar2 M0 w' (encodeIntV M0 z) _) (et_const0 M0 (dc_integers M0) _),
      ev_faf_mem M0 (et_bvar1 M0 w' _) (et_const0 M0 (dc_integers M0) _),
      ev_nest2 M0 Constant14.integerSucc.dfn (et_bvar2 M0 w' (encodeIntV M0 z) _) (et_bvar1 M0 w' _),
      ev_faf_notMem M0 (et_bvar2 M0 w' (encodeIntV M0 z) _) (et_const0 M0 (dc_integers M0) _)]
  simp only [encodeIntV_mem M0 z, not_true_eq_false, false_and, or_false, true_and]
  constructor
  · rintro ⟨hw', hsucc⟩
    rw [ev_integerSucc_of_mem M0 hw'] at hsucc
    obtain ⟨a, ha, r, hr, rfl⟩ := (mem_prodV M0).mp hw'
    rw [pi1V_kpairV, pi2V_kpairV] at hsucc
    have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
    rcases hsucc with ⟨rfl, hzeq⟩ | ⟨rfl, ⟨rfl, hzeq⟩ | ⟨m, _, hr_eq, hzeq⟩⟩
    · cases z with
      | ofNat k =>
        have hk := (kpairV_inj M0 hzeq).2
        cases k with
        | zero =>
          have : M0.mem r (vnNatV M0 0) := hk ▸ (mem_insertV M0).mpr (Or.inl rfl)
          exact (not_mem_emptyV M0 r this).elim
        | succ k' =>
          have hrk : vnNatV M0 k' = r := succV_inj M0 hk
          subst r
          change encodeIntV M0 (Int.ofNat k') = _
          exact congrArg (encodeIntV M0) (by simp only [Int.ofNat_eq_natCast]; omega)
      | negSucc k =>
        exact (h01.symm (kpairV_inj M0 hzeq).1).elim
    · have hz0 : z = 0 := encodeIntV_inj M0 hzeq
      subst hz0
      rfl
    · cases z with
      | ofNat k =>
        exact (h01 (kpairV_inj M0 hzeq).1).elim
      | negSucc k =>
        have hmk : vnNatV M0 k = m := (kpairV_inj M0 hzeq).2
        subst m
        rw [hr_eq]
        change encodeIntV M0 (Int.negSucc (k + 1)) = _
        exact congrArg (encodeIntV M0) (by omega)
  · rintro rfl
    refine ⟨encodeIntV_mem M0 (z - 1), ?_⟩
    rw [ev_integerSucc_encode M0 (z - 1) (encodeIntV M0 z)]
    congr 1
    omega

lemma dc_configSet (N : ℕ) : DefinesConst M0 (Constant14.configSet N) (cfgSetV M0 N) := by
  intro y
  unfold Constant14.configSet cfgSetV
  exact ev_faf_eq M0 (et_bvar1 M0 y _)
    (et_comp2 M0 (ev_prod M0) (et_const0 M0 (dc_numeral M0 N) _)
      (et_comp2 M0 (ev_prod M0) (et_const0 M0 (dc_integers M0) _)
        (et_comp2 M0 (ev_function M0) (et_const0 M0 (dc_numeral M0 2) _) (et_const0 M0 (dc_integers M0) _))))

def entryForm (t : ℕ × ℕ × ℕ × ℕ × ℕ) : SetTheorySemisentence 1 :=
  Constant14.transitionEntry t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2

noncomputable def entryVal (t : ℕ × ℕ × ℕ × ℕ × ℕ) : M0.V :=
  kpairV M0 (kpairV M0 (vnNatV M0 t.1) (vnNatV M0 t.2.1))
    (kpairV M0 (vnNatV M0 t.2.2.1) (kpairV M0 (vnNatV M0 t.2.2.2.1) (vnNatV M0 t.2.2.2.2)))

lemma dc_entryForm (t : ℕ × ℕ × ℕ × ℕ × ℕ) :
    DefinesConst M0 (entryForm t) (entryVal M0 t) := by
  unfold entryForm Constant14.transitionEntry entryVal
  exact dc_setPair M0 (dc_setPair M0 (dc_numeral M0 _) (dc_numeral M0 _))
    (dc_setTriple M0 (dc_numeral M0 _) (dc_numeral M0 _) (dc_numeral M0 _))

def transTuples {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (List.ofFn fun q : Fin n =>
    List.ofFn fun sym : Fin 2 =>
      let o := Constant14.transitionCode M q sym
      (q.val, sym.val, o.1, o.2.1, o.2.2)).flatten ++
  List.ofFn fun sym : Fin 2 =>
    (n, sym.val, n, sym.val, Constant14.directionCode none)

noncomputable def instrTableV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : M0.V :=
  listToV M0 ((transTuples M).map (entryVal M0))

lemma dc_instructionTable {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    DefinesConst M0 (Constant14.instructionTable M) (instrTableV M0 M) := by
  unfold Constant14.instructionTable instrTableV
  have hmap : (transTuples M).map entryForm = Constant14.transitionEntries M := by
    simp [transTuples, Constant14.transitionEntries, entryForm, List.map_flatten,
      List.map_ofFn, Function.comp_def]
  rw [← hmap]
  exact dc_finiteSet_map M0 (transTuples M) entryForm (entryVal M0) (dc_entryForm M0)

def transLookup {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (qCode symCode : ℕ) :
    ℕ × ℕ × ℕ :=
  if hq : qCode < n then
    if hs : symCode < 2 then
      Constant14.transitionCode M ⟨qCode, hq⟩ ⟨symCode, hs⟩
    else (n, 0, 1)
  else (n, symCode, 1)

lemma transitionCode_bounds {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
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

lemma instrTableV_app {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (qCode symCode : ℕ) (hq : qCode < n + 1) (hs : symCode < 2) :
    zfcAppV M0 (instrTableV M0 M) (kpairV M0 (vnNatV M0 qCode) (vnNatV M0 symCode)) =
      let o := transLookup M qCode symCode
      kpairV M0 (vnNatV M0 o.1) (kpairV M0 (vnNatV M0 o.2.1) (vnNatV M0 o.2.2)) := by
  have hmem_iff : ∀ p : M0.V, M0.mem p (instrTableV M0 M) ↔
      (∃ (q : Fin n) (sym : Fin 2),
        let o := Constant14.transitionCode M q sym
        p = entryVal M0 (q.val, sym.val, o.1, o.2.1, o.2.2)) ∨
      (∃ sym : Fin 2, p = entryVal M0 (n, sym.val, n, sym.val, 1)) := by
    intro p
    unfold instrTableV
    rw [mem_listToV, List.mem_map]
    simp only [transTuples, List.mem_append, List.mem_flatten, List.mem_ofFn, Constant14.directionCode]
    constructor
    · rintro ⟨t, (⟨l, ⟨q, rfl⟩, ht⟩ | ⟨sym, rfl⟩), rfl⟩
      · obtain ⟨sym, rfl⟩ := List.mem_ofFn.mp ht
        exact Or.inl ⟨q, sym, rfl⟩
      · exact Or.inr ⟨sym, rfl⟩
    · rintro (⟨q, sym, rfl⟩ | ⟨sym, rfl⟩)
      · exact ⟨_, Or.inl ⟨_, ⟨q, rfl⟩, List.mem_ofFn.mpr ⟨sym, rfl⟩⟩, rfl⟩
      · exact ⟨_, Or.inr ⟨sym, rfl⟩, rfl⟩
  let o := transLookup M qCode symCode
  apply zfcAppV_of_unique M0
  intro y
  rw [hmem_iff]
  constructor
  · rintro (⟨q, sym, heq⟩ | ⟨sym, heq⟩)
    · obtain ⟨h1, rfl⟩ := kpairV_inj M0 heq
      obtain ⟨hq1, hs1⟩ := kpairV_inj M0 h1
      have hqc : qCode = q.val := vnNatV_inj M0 hq1
      have hsc : symCode = sym.val := vnNatV_inj M0 hs1
      subst hqc hsc
      dsimp only [o, transLookup]
      rw [dif_pos q.isLt, dif_pos sym.isLt]
    · obtain ⟨h1, rfl⟩ := kpairV_inj M0 heq
      obtain ⟨hq1, hs1⟩ := kpairV_inj M0 h1
      have hqc : qCode = n := vnNatV_inj M0 hq1
      have hsc : symCode = sym.val := vnNatV_inj M0 hs1
      subst qCode symCode
      dsimp only [o, transLookup]
      rw [dif_neg (Nat.lt_irrefl n)]
  · rintro rfl
    by_cases hqn : qCode < n
    · left
      refine ⟨⟨qCode, hqn⟩, ⟨symCode, hs⟩, ?_⟩
      dsimp only [o, transLookup]
      rw [dif_pos hqn, dif_pos hs]; rfl
    · have hqe : qCode = n := by omega
      subst qCode
      right
      refine ⟨⟨symCode, hs⟩, ?_⟩
      dsimp only [o, transLookup]
      rw [dif_neg (Nat.lt_irrefl n)]; rfl

lemma dc_emptyTape : DefinesConst M0 Constant14.emptyTape (emptyTapeV M0) := by
  intro f
  unfold Constant14.emptyTape
  rw [mEv_and]
  rw [ev_faf_mem M0 (et_bvar1 M0 f _)
        (et_comp2 M0 (ev_function M0) (et_const0 M0 (dc_numeral M0 2) _) (et_const0 M0 (dc_integers M0) _)),
      ev_faf_ball M0 (et_const0 M0 (dc_integers M0) _)]
  refine (and_congr Iff.rfl (forall₂_congr fun i _ =>
      (?_ : _ ↔ zfcAppV M0 f i = vnNatV M0 0))).trans ?_
  · exact ev_faf_eq M0
      (et_comp2 M0 (ev_value M0) (et_bvar3 M0 i (intSetV M0) f _) (et_bvar1 M0 i _))
      (et_const0 M0 (dc_numeral M0 0) _)
  · constructor
    · rintro ⟨hf, hall⟩
      refine funsV_ext M0 hf (emptyTapeV_mem_funs M0) fun u hu => ?_
      rw [hall u hu, emptyTapeV_app M0 hu]
    · rintro rfl
      exact ⟨emptyTapeV_mem_funs M0, fun u hu => emptyTapeV_app M0 hu⟩

/- ## Section 5: `nextStepV`, Halting Trace Simulation, and `model_satisfies_halts` -/

lemma exists_nextStepV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ∃ F : M0.V, ∀ e : M0.V, M0.mem e F ↔
      ∃ z : M0.V, M0.mem z (cfgSetV M0 (n + 1)) ∧
        ∃ z' : M0.V, M0.mem z' (cfgSetV M0 (n + 1)) ∧
          e = kpairV M0 z z' ∧
          mEv M0 ![z', z] (Constant14.nextConfig (n + 1) (Constant14.instructionTable M)) := by
  let ambient := prodV M0 (cfgSetV M0 (n + 1)) (cfgSetV M0 (n + 1))
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.bexsMem (&0)
      (Semiformula.bexsMem (&0)
        ((Rew.subst ![#2, #1, #0] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋏
          (Rew.subst ![#0, #1] ▹
            Rewriting.emb (Constant14.nextConfig (n + 1) (Constant14.instructionTable M)))))
  obtain ⟨F, hF⟩ := sepV M0 ambient φ (fun _ => cfgSetV M0 (n + 1))
  refine ⟨F, fun e => ?_⟩
  rw [hF e]
  have hφ : evalM M0.mem ![e] (fun _ => cfgSetV M0 (n + 1)) φ ↔
      ∃ z : M0.V, M0.mem z (cfgSetV M0 (n + 1)) ∧
        ∃ z' : M0.V, M0.mem z' (cfgSetV M0 (n + 1)) ∧
          e = kpairV M0 z z' ∧
          mEv M0 ![z', z] (Constant14.nextConfig (n + 1) (Constant14.instructionTable M)) := by
    dsimp only [φ]
    rw [evalM_bexsMem]
    refine exists_congr fun z => and_congr Iff.rfl ?_
    rw [evalM_bexsMem]
    refine exists_congr fun z' => and_congr Iff.rfl ?_
    rw [evalM_and]
    refine and_congr ?_ ?_
    · change evalM M0.mem (z' :> z :> e :> ![]) _
        ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#2, #1, #0]) ↔ _
      rw [evalM_subst, evalM_emb]
      refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).trans (ev_kpair M0 e z z')
      funext i; fin_cases i <;> rfl
    · change evalM M0.mem (z' :> z :> e :> ![]) _
        ((Rewriting.emb (Constant14.nextConfig (n + 1) (Constant14.instructionTable M))) ⇜ ![#0, #1]) ↔ _
      rw [evalM_subst, evalM_emb]
      refine evalRaw_congr Eq M0.mem _ ?_ rfl
      funext i; fin_cases i <;> rfl
  rw [hφ]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rcases h with ⟨z, hz, z', hz', rfl, _⟩
  exact (kpairV_mem_prodV M0).mpr ⟨hz, hz'⟩

noncomputable def nextStepV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : M0.V :=
  (exists_nextStepV M0 M).choose

lemma mem_nextStepV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) {e : M0.V} :
    M0.mem e (nextStepV M0 M) ↔
      ∃ z : M0.V, M0.mem z (cfgSetV M0 (n + 1)) ∧
        ∃ z' : M0.V, M0.mem z' (cfgSetV M0 (n + 1)) ∧
          e = kpairV M0 z z' ∧
          mEv M0 ![z', z] (Constant14.nextConfig (n + 1) (Constant14.instructionTable M)) :=
  (exists_nextStepV M0 M).choose_spec e

lemma dc_nextStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    DefinesConst M0 (Constant14.nextStep (n + 1) (Constant14.instructionTable M)) (nextStepV M0 M) := by
  intro p
  unfold Constant14.nextStep
  change mEv M0 ![p] (∀¹ _) ↔ _
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ e : M0.V, M0.mem e p ↔ M0.mem e (nextStepV M0 M)).trans
    ⟨fun h => extV M0 h, fun h e => by rw [h]⟩
  refine forall_congr' fun e => ?_
  rw [mEv_iff, mem_nextStepV]
  refine iff_congr (ev_faf_mem M0 (et_bvar1 M0 e _) (et_bvar3 M0 _ e p _)) ?_
  rw [ev_faf_bexs M0 (et_const0 M0 (dc_configSet M0 (n + 1)) _)]
  refine exists_congr fun z => and_congr_right fun _ => ?_
  rw [ev_faf_bexs M0 (et_const0 M0 (dc_configSet M0 (n + 1)) _)]
  refine exists_congr fun z' => and_congr_right fun _ => ?_
  rw [mEv_and]
  exact and_congr
    (ev_faf_eq M0 (et_bvar5 M0 z' _ z _ e _)
      (et_comp2 M0 (ev_kpair M0) (et_bvar4 M0 _ z' _ z _) (et_bvar2 M0 _ z' _)))
    (ev_nest2 M0 (Constant14.nextConfig (n + 1) (Constant14.instructionTable M))
      (et_bvar1 M0 z' _) (et_bvar3 M0 z' _ z _))

abbrev ExtCfg (n : ℕ) := Option (Fin n) × ℤ × Tape (Fin 2)

def extInit (n : ℕ) [NeZero n] : ExtCfg n := (some 0, 0, Tape.mk₁ [])

def extStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : ExtCfg n → ExtCfg n
  | (none, pos, T) => (none, pos, T)
  | (some q, pos, T) =>
    match M q T.head with
    | none => (none, pos, T)
    | some (q', Stmt.write sym d) =>
      let pos' := match d with
        | Dir.left => pos - 1
        | Dir.right => pos + 1
      (q', pos', (T.write sym).move d)

lemma blank_tape_nth (i : ℤ) : (Tape.mk₁ ([] : List (Fin 2))).nth i = 0 := by
  cases i with
  | ofNat k =>
    cases k <;> simp [Tape.mk₁, Tape.mk₂, Tape.nth, Tape.mk', Fin.default_eq_zero]
  | negSucc k =>
    simp [Tape.mk₁, Tape.mk₂, Tape.nth, Tape.mk', Fin.default_eq_zero]

noncomputable def simStepTape {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (c : ExtCfg n) (g : M0.V) : M0.V :=
  match c with
  | (none, _, _) => g
  | (some q, pos, T) =>
    match M q T.head with
    | none => g
    | some (_, Stmt.write sym _) =>
      updateTapeV M0 g (encodeIntV M0 pos) (vnNatV M0 sym.val)

noncomputable def simTape {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : ℕ → M0.V
  | 0 => emptyTapeV M0
  | k + 1 => simStepTape M0 M ((extStep M)^[k] (extInit n)) (simTape M k)

lemma simTape_spec {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (k : ℕ) :
    let c := (extStep M)^[k] (extInit n)
    M0.mem (simTape M0 M k) (funsV M0 (intSetV M0) (vnNatV M0 2)) ∧
      ∀ m : ℤ, zfcAppV M0 (simTape M0 M k) (encodeIntV M0 m) =
        vnNatV M0 (c.2.2.nth (m - c.2.1)).val := by
  induction k with
  | zero =>
    refine ⟨emptyTapeV_mem_funs M0, fun m => ?_⟩
    rw [simTape, emptyTapeV_app M0 (encodeIntV_mem M0 m)]
    change vnNatV M0 0 = vnNatV M0 ((Tape.mk₁ ([] : List (Fin 2))).nth (m - 0)).val
    rw [blank_tape_nth]
    rfl
  | succ k ih =>
    rcases hext : (extStep M)^[k] (extInit n) with ⟨qOpt, pos, T⟩
    rw [hext] at ih
    dsimp only at ih
    obtain ⟨hg, happ⟩ := ih
    dsimp only
    rw [Function.iterate_succ_apply', hext, simTape, hext]
    cases qOpt with
    | none =>
      exact ⟨hg, happ⟩
    | some q =>
      dsimp only [extStep, simStepTape]
      cases hMq : M q T.head with
      | none =>
        exact ⟨hg, happ⟩
      | some out =>
        rcases out with ⟨q', ⟨sym, d⟩⟩
        dsimp only
        have hg' : M0.mem (updateTapeV M0 (simTape M0 M k) (encodeIntV M0 pos) (vnNatV M0 sym.val))
            (funsV M0 (intSetV M0) (vnNatV M0 2)) :=
          updateTapeV_mem_funs M0 hg (encodeIntV_mem M0 pos) (vnNatV_lt_mem M0 sym.isLt)
        refine ⟨hg', fun m => ?_⟩
        rw [updateTapeV_app M0 hg (encodeIntV_mem M0 pos) (vnNatV_lt_mem M0 sym.isLt) (encodeIntV_mem M0 m)]
        cases d with
        | left =>
          dsimp only
          rw [Tape.move_left_nth]
          have hidx : m - (pos - 1) - 1 = m - pos := by omega
          rw [hidx, Tape.write_nth]
          by_cases hmp : m = pos
          · subst hmp
            rw [if_pos rfl, sub_self, if_pos rfl]
          · have hne1 : encodeIntV M0 m ≠ encodeIntV M0 pos := fun h => hmp (encodeIntV_inj M0 h)
            have hne2 : m - pos ≠ 0 := by omega
            rw [if_neg hne1, if_neg hne2, happ m]
        | right =>
          dsimp only
          rw [Tape.move_right_nth]
          have hidx : m - (pos + 1) + 1 = m - pos := by omega
          rw [hidx, Tape.write_nth]
          by_cases hmp : m = pos
          · subst hmp
            rw [if_pos rfl, sub_self, if_pos rfl]
          · have hne1 : encodeIntV M0 m ≠ encodeIntV M0 pos := fun h => hmp (encodeIntV_inj M0 h)
            have hne2 : m - pos ≠ 0 := by omega
            rw [if_neg hne1, if_neg hne2, happ m]

noncomputable def simCfgV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (k : ℕ) : M0.V :=
  let c := (extStep M)^[k] (extInit n)
  kpairV M0 (vnNatV M0 (Constant14.stateCode c.1))
    (kpairV M0 (encodeIntV M0 c.2.1) (simTape M0 M k))

lemma simCfgV_mem {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (k : ℕ) :
    M0.mem (simCfgV M0 M k) (cfgSetV M0 (n + 1)) := by
  unfold simCfgV cfgSetV
  refine (kpairV_mem_prodV M0).mpr ⟨?_, (kpairV_mem_prodV M0).mpr ⟨encodeIntV_mem M0 _, (simTape_spec M0 M k).1⟩⟩
  apply vnNatV_lt_mem
  cases ((extStep M)^[k] (extInit n)).1 with
  | none => exact Nat.lt_succ_self n
  | some q => exact Nat.lt_succ_of_lt q.isLt

lemma dc_initialConfig {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    DefinesConst M0 Constant14.initialConfig (simCfgV M0 M 0) := by
  intro z
  unfold Constant14.initialConfig
  rw [ev_faf_eq M0 (et_bvar1 M0 z _)
    (et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_numeral M0 0) _)
      (et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_integerZero M0) _) (et_const0 M0 (dc_emptyTape M0) _)))]
  rfl

lemma ev_nextConfig_simCfg {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (k : ℕ) (z' : M0.V) :
    mEv M0 ![z', simCfgV M0 M k]
      (Constant14.nextConfig (n + 1) (Constant14.instructionTable M)) ↔
      z' = simCfgV M0 M (k + 1) := by
  let z0 := simCfgV M0 M k
  have hz0 : M0.mem z0 (cfgSetV M0 (n + 1)) := simCfgV_mem M0 M k
  have hz1 : M0.mem (simCfgV M0 M (k + 1)) (cfgSetV M0 (n + 1)) := simCfgV_mem M0 M (k + 1)
  obtain ⟨hg0, happ0⟩ := simTape_spec M0 M k
  rcases hext : (extStep M)^[k] (extInit n) with ⟨qOpt, pos, T⟩
  rw [hext] at happ0
  dsimp only at happ0
  let qCode := Constant14.stateCode qOpt
  have hq : qCode < n + 1 := by
    dsimp only [qCode]
    cases qOpt with
    | none => exact Nat.lt_succ_self n
    | some q => exact Nat.lt_succ_of_lt q.isLt
  have hz0_eq : z0 = kpairV M0 (vnNatV M0 qCode) (kpairV M0 (encodeIntV M0 pos) (simTape M0 M k)) := by
    dsimp only [z0, simCfgV, qCode]; rw [hext]
  have hsym : zfcAppV M0 (simTape M0 M k) (encodeIntV M0 pos) = vnNatV M0 T.head.val := by
    have h := happ0 pos
    rw [sub_self] at h
    exact h
  let o := transLookup M qCode T.head.val
  have hob : o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
    dsimp only [o, transLookup]
    by_cases hqn : qCode < n
    · rw [dif_pos hqn, dif_pos T.head.isLt]
      exact transitionCode_bounds M ⟨qCode, hqn⟩ T.head
    · rw [dif_neg hqn]
      dsimp only
      exact ⟨Nat.lt_succ_self n, T.head.isLt, by decide⟩
  let tVal := kpairV M0 (vnNatV M0 o.1) (kpairV M0 (vnNatV M0 o.2.1) (vnNatV M0 o.2.2))
  have htVal_eq : zfcAppV M0 (instrTableV M0 M)
      (kpairV M0 (pi1V M0 z0) (zfcAppV M0 (pi2V M0 (pi2V M0 z0)) (pi1V M0 (pi2V M0 z0)))) = tVal := by
    rw [hz0_eq, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, hsym]
    exact instrTableV_app M0 M qCode T.head.val hq T.head.isLt
  -- Compute exact next state, head position, and tape
  have hnext_eq :
      let pos' : ℤ := if o.2.2 = 0 then pos - 1 else if o.2.2 = 1 then pos else pos + 1
      simCfgV M0 M (k + 1) =
        kpairV M0 (vnNatV M0 o.1) (kpairV M0 (encodeIntV M0 pos') (simTape M0 M (k + 1))) ∧
      (zfcAppV M0 (simTape M0 M (k + 1)) (encodeIntV M0 pos) = vnNatV M0 o.2.1 ∧
       ∀ u : M0.V, M0.mem u (intSetV M0) → u ≠ encodeIntV M0 pos →
         zfcAppV M0 (simTape M0 M (k + 1)) u = zfcAppV M0 (simTape M0 M k) u) := by
    dsimp only [simCfgV]
    rw [Function.iterate_succ_apply', hext, simTape, hext]
    cases qOpt with
    | none =>
      have ho : o = (n, T.head.val, 1) := by
        dsimp only [o, qCode, Constant14.stateCode, transLookup]
        rw [dif_neg (Nat.lt_irrefl n)]
      rw [ho]
      dsimp only [extStep, simStepTape, Constant14.stateCode]
      refine ⟨by simp, hsym, fun _ _ _ => rfl⟩
    | some q =>
      have ho : o = Constant14.transitionCode M q T.head := by
        dsimp only [o, qCode, Constant14.stateCode, transLookup]
        rw [dif_pos q.isLt, dif_pos T.head.isLt]
      rw [ho]
      rcases hMq : M q T.head with _ | ⟨q', ⟨sym, d⟩⟩
      · rw [Constant14.transitionCode, extStep, simStepTape, hMq]
        dsimp only [Constant14.directionCode, Constant14.stateCode]
        refine ⟨by simp, hsym, fun _ _ _ => rfl⟩
      · cases d with
        | left =>
          rw [Constant14.transitionCode, extStep, simStepTape, hMq]
          dsimp only [Constant14.directionCode]
          refine ⟨by simp, ?_, ?_⟩
          · rw [updateTapeV_app M0 hg0 (encodeIntV_mem M0 pos) (vnNatV_lt_mem M0 sym.isLt) (encodeIntV_mem M0 pos),
              if_pos rfl]
          · intro u hu hne
            rw [updateTapeV_app M0 hg0 (encodeIntV_mem M0 pos) (vnNatV_lt_mem M0 sym.isLt) hu,
              if_neg hne]
        | right =>
          rw [Constant14.transitionCode, extStep, simStepTape, hMq]
          dsimp only [Constant14.directionCode]
          refine ⟨by simp, ?_, ?_⟩
          · rw [updateTapeV_app M0 hg0 (encodeIntV_mem M0 pos) (vnNatV_lt_mem M0 sym.isLt) (encodeIntV_mem M0 pos),
              if_pos rfl]
          · intro u hu hne
            rw [updateTapeV_app M0 hg0 (encodeIntV_mem M0 pos) (vnNatV_lt_mem M0 sym.isLt) hu,
              if_neg hne]
  let pos' : ℤ := if o.2.2 = 0 then pos - 1 else if o.2.2 = 1 then pos else pos + 1
  obtain ⟨hcfg1_eq, htap1_pos, htap1_rest⟩ := hnext_eq
  -- Evaluate `Constant14.nextConfig` formula
  unfold Constant14.nextConfig
  rw [mEv_and, mEv_and]
  rw [ev_faf_mem M0 (et_bvar2 M0 z' z0 _) (et_const0 M0 (dc_configSet M0 (n + 1)) _),
      ev_faf_mem M0 (et_bvar1 M0 z' _) (et_const0 M0 (dc_configSet M0 (n + 1)) _)]
  simp only [hz0, true_and]
  rw [mEv_exs]
  refine (and_congr Iff.rfl (exists_congr fun t => (?_ : _ ↔
      (t = tVal ∧
       pi1V M0 z' = pi1V M0 t ∧
       ((pi2V M0 (pi2V M0 t) = vnNatV M0 0 ∧
           mEv M0 ![pi1V M0 (pi2V M0 z'), pi1V M0 (pi2V M0 z0)] Constant14.integerPred.dfn) ∨
         (pi2V M0 (pi2V M0 t) = vnNatV M0 1 ∧ pi1V M0 (pi2V M0 z') = pi1V M0 (pi2V M0 z0)) ∨
         (pi2V M0 (pi2V M0 t) = vnNatV M0 2 ∧
           mEv M0 ![pi1V M0 (pi2V M0 z'), pi1V M0 (pi2V M0 z0)] Constant14.integerSucc.dfn)) ∧
       zfcAppV M0 (pi2V M0 (pi2V M0 z')) (pi1V M0 (pi2V M0 z0)) = pi1V M0 (pi2V M0 t) ∧
       ∀ u : M0.V, M0.mem u (intSetV M0) → u ≠ pi1V M0 (pi2V M0 z0) →
         zfcAppV M0 (pi2V M0 (pi2V M0 z')) u = zfcAppV M0 (pi2V M0 (pi2V M0 z0)) u)))).trans ?_
  · rw [mEv_and, mEv_and, mEv_and, mEv_and]
    refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
    · rw [ev_faf_eq M0 (et_bvar1 M0 t _)
        (et_comp2 M0 (ev_value M0) (et_const0 M0 (dc_instructionTable M0 M) _)
          (et_comp2 M0 (ev_kpair M0)
            (et_comp1 M0 (ev_pi1 M0) (et_bvar4 M0 _ t z' z0 _))
            (et_comp2 M0 (ev_value M0)
              (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar4 M0 _ t z' z0 _)))
              (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar4 M0 _ t z' z0 _)))))),
        htVal_eq]
    · exact ev_faf_eq M0
        (et_comp1 M0 (ev_pi1 M0) (et_bvar2 M0 t z' _))
        (et_comp1 M0 (ev_pi1 M0) (et_bvar2 M0 _ t _))
    · rw [mEv_or, mEv_or, mEv_and, mEv_and, mEv_and]
      refine or_congr
        (and_congr
          (ev_faf_eq M0 (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar1 M0 t _)))
            (et_const0 M0 (dc_numeral M0 0) _))
          (ev_nest2 M0 Constant14.integerPred.dfn
            (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 t z' _)))
            (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar3 M0 t z' z0 _)))))
        (or_congr
          (and_congr
            (ev_faf_eq M0 (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar1 M0 t _)))
              (et_const0 M0 (dc_numeral M0 1) _))
            (ev_faf_eq M0
              (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 t z' _)))
              (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar4 M0 _ t z' z0 _)))))
          (and_congr
            (ev_faf_eq M0 (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar1 M0 t _)))
              (et_const0 M0 (dc_numeral M0 2) _))
            (ev_nest2 M0 Constant14.integerSucc.dfn
              (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 t z' _)))
              (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar3 M0 t z' z0 _))))))
    · exact ev_faf_eq M0
        (et_comp2 M0 (ev_value M0)
          (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 t z' _)))
          (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar3 M0 t z' z0 _))))
        (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 _ t _)))
    · rw [ev_faf_ball M0 (et_const0 M0 (dc_integers M0) _)]
      refine forall₂_congr fun u _ => ?_
      rw [mEv_imp]
      exact imp_congr
        (ev_faf_ne M0 (et_bvar1 M0 u _)
          (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar6 M0 _ u (intSetV M0) t z' z0 _))))
        (ev_faf_eq M0
          (et_comp2 M0 (ev_value M0)
            (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar4 M0 u (intSetV M0) t z' _)))
            (et_bvar1 M0 u _))
          (et_comp2 M0 (ev_value M0)
            (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar6 M0 _ u (intSetV M0) t z' z0 _)))
            (et_bvar2 M0 _ u _)))
  · constructor
    · rintro ⟨hz', t, rfl, hq_eq, hdir, hwr, hrest⟩
      obtain ⟨s2, _, p_tail, hp_tail, rfl⟩ := (mem_prodV M0).mp hz'
      obtain ⟨p2, _, g2, hg2, rfl⟩ := (mem_prodV M0).mp hp_tail
      rw [hz0_eq] at hdir hwr hrest
      dsimp only [tVal] at hq_eq hdir hwr
      rw [pi1V_kpairV, pi1V_kpairV] at hq_eq
      rw [pi2V_kpairV, pi2V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV] at hdir
      rw [pi2V_kpairV, pi2V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV] at hwr
      simp only [pi2V_kpairV, pi1V_kpairV] at hrest
      rw [hcfg1_eq, hq_eq]
      congr 1; congr 1
      · have hd2 := hob.2.2
        interval_cases hdv : o.2.2
        · have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          have h02 : vnNatV M0 0 ≠ vnNatV M0 2 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          simp only [true_and, h01, h02, false_and, or_false] at hdir
          rw [ev_integerPred_encode] at hdir
          simpa [pos', hdv] using hdir
        · have h10 : vnNatV M0 1 ≠ vnNatV M0 0 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          have h12 : vnNatV M0 1 ≠ vnNatV M0 2 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          simp only [true_and, h10, h12, false_and, false_or, or_false] at hdir
          simpa [pos', hdv] using hdir
        · have h20 : vnNatV M0 2 ≠ vnNatV M0 0 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          have h21 : vnNatV M0 2 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          simp only [true_and, h20, h21, false_and, false_or] at hdir
          rw [ev_integerSucc_encode] at hdir
          simpa [pos', hdv] using hdir
      · refine funsV_ext M0 hg2 (simTape_spec M0 M (k + 1)).1 fun u hu => ?_
        by_cases hup : u = encodeIntV M0 pos
        · subst hup; rw [hwr, htap1_pos]
        · rw [hrest u hu hup, htap1_rest u hu hup]
    · rintro rfl
      refine ⟨hz1, tVal, rfl, ?_, ?_, ?_, ?_⟩
      · rw [hcfg1_eq]; dsimp only [tVal]; rw [pi1V_kpairV, pi1V_kpairV]
      · rw [hcfg1_eq, hz0_eq]; dsimp only [tVal]
        rw [pi2V_kpairV, pi2V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV]
        have hd2 := hob.2.2
        interval_cases hdv : o.2.2
        · left; refine ⟨rfl, ?_⟩
          rw [ev_integerPred_encode]; simp
        · right; left; refine ⟨rfl, ?_⟩
          simp
        · right; right; refine ⟨rfl, ?_⟩
          rw [ev_integerSucc_encode]; simp
      · rw [hcfg1_eq, hz0_eq]; dsimp only [tVal]
        rw [pi2V_kpairV, pi2V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV]
        exact htap1_pos
      · intro u hu hne
        rw [hz0_eq, pi2V_kpairV, pi1V_kpairV] at hne
        rw [hcfg1_eq, hz0_eq]
        simp only [pi2V_kpairV]
        exact htap1_rest u hu hne

lemma zfcAppV_nextStepV_simCfg {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (k : ℕ) :
    zfcAppV M0 (nextStepV M0 M) (simCfgV M0 M k) = simCfgV M0 M (k + 1) := by
  apply zfcAppV_of_unique M0
  intro y
  rw [mem_nextStepV]
  constructor
  · rintro ⟨z, _, z', _, heq, hnc⟩
    obtain ⟨rfl, rfl⟩ := kpairV_inj M0 heq
    exact (ev_nextConfig_simCfg M0 M k y).mp hnc
  · rintro rfl
    exact ⟨simCfgV M0 M k, simCfgV_mem M0 M k, simCfgV M0 M (k + 1), simCfgV_mem M0 M (k + 1),
      rfl, (ev_nextConfig_simCfg M0 M k (simCfgV M0 M (k + 1))).mpr rfl⟩

lemma multiStep_agrees_extStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (k : ℕ) :
    match M.multiStep (Machine.init []) k with
    | none => ((extStep M)^[k] (extInit n)).1 = none
    | some cfg => ((extStep M)^[k] (extInit n)).1 = cfg.q ∧
                  ((extStep M)^[k] (extInit n)).2.2 = cfg.tape := by
  induction k with
  | zero =>
    simp [Machine.multiStep_zero, Machine.init, extInit, Fin.default_eq_zero]
  | succ k ih =>
    rw [Machine.multiStep_succ, Function.iterate_succ_apply']
    cases hmk : M.multiStep (Machine.init []) k with
    | none =>
      rw [hmk] at ih
      dsimp only at ih ⊢
      rcases hext : (extStep M)^[k] (extInit n) with ⟨qOpt, pos, T⟩
      rw [hext] at ih; dsimp only at ih; subst ih
      rfl
    | some cfg =>
      rw [hmk] at ih
      dsimp only [Option.bind_some] at ih ⊢
      rcases cfg with ⟨qOpt, Tk⟩
      rcases hext : (extStep M)^[k] (extInit n) with ⟨c1, pos, cT⟩
      rw [hext] at ih; dsimp only at ih
      rcases ih with ⟨rfl, rfl⟩
      cases c1 with
      | none =>
        simp [Machine.step, extStep]
      | some qk =>
        dsimp only [Machine.step, extStep]
        cases hMq : M qk cT.head with
        | none =>
          simp
        | some out =>
          rcases out with ⟨qNext, ⟨sym, d⟩⟩
          simp

theorem model_satisfies_halts {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (h : ∃ N : ℕ, M.multiStep (Machine.init []) N = none) :
    evalM M0.mem Fin.elim0 Empty.elim (Constant14.halts M) := by
  obtain ⟨N, hN⟩ := h
  have hnone : ((extStep M)^[N] (extInit n)).1 = none := by
    have h1 := multiStep_agrees_extStep M N
    rw [hN] at h1
    exact h1
  let cN := (extStep M)^[N] (extInit n)
  let mVal := encodeIntV M0 cN.2.1
  let gVal := simTape M0 M N
  have htarget_eq : kpairV M0 (vnNatV M0 n) (kpairV M0 mVal gVal) = simCfgV M0 M N := by
    dsimp only [simCfgV, mVal, gVal, cN]
    rw [hnone]
    rfl
  change mEv M0 (Fin.elim0 : Fin 0 → M0.V) (Constant14.halts M)
  rw [mEv_e0 M0 (Fin.elim0 : Fin 0 → M0.V) ![]]
  unfold Constant14.halts
  rw [ev_faf_bexs M0 (et_const0 M0 (dc_integers M0) ![])]
  refine ⟨mVal, encodeIntV_mem M0 _, ?_⟩
  rw [ev_faf_bexs M0
    (et_comp2 M0 (ev_function M0) (et_const0 M0 (dc_numeral M0 2) _) (et_const0 M0 (dc_integers M0) _))]
  refine ⟨gVal, (simTape_spec M0 M N).1, ?_⟩
  have htarget : EvalTermAt M0 (gVal :> funsV M0 (intSetV M0) (vnNatV M0 2) :> mVal :> intSetV M0 :> ![])
      (Semiformula.nestFormulaeFunc SetTheory.kpair.dfn
        (Semiformula.nestFormulaeFunc (Constant14.numeral n) ![] :>
          Semiformula.nestFormulaeFunc SetTheory.kpair.dfn
            (op(=).operator (#0 :> #3 :> ![]) :> op(=).operator (#0 :> #1 :> ![]) :> ![]) :> ![]))
      (simCfgV M0 M N) := by
    rw [← htarget_eq]
    exact et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_numeral M0 n) _)
      (et_comp2 M0 (ev_kpair M0) (et_bvar3 M0 gVal _ mVal _) (et_bvar1 M0 gVal _))
  rw [mEv_all]
  intro t
  rw [mEv_imp]
  intro ht
  have ht_eq : t = simCfgV M0 M N := (htarget t).mp ht
  subst ht_eq
  rw [mEv_all]
  intro O
  rw [mEv_imp]
  intro hO_nest
  rw [ev_nestFunc2_raw M0 Constant14.orbit
    (et_const0 M0 (dc_nextStep M0 M) _) (et_const0 M0 (dc_initialConfig M0 M) _) O] at hO_nest
  unfold Constant14.orbit at hO_nest
  rw [mEv_and] at hO_nest
  have hO_mem := hO_nest.2
  rw [mEv_all] at hO_mem
  have hO_t := hO_mem (simCfgV M0 M N)
  rw [mEv_iff,
      ev_faf_mem M0 (et_bvar1 M0 (simCfgV M0 M N) _) (et_bvar3 M0 _ (simCfgV M0 M N) O _)] at hO_t
  refine hO_t.mpr ?_
  rw [mEv_all]
  intro A
  rw [mEv_imp, mEv_and]
  rintro ⟨hA0_raw, hAstep_raw⟩
  have hA0 : M0.mem (simCfgV M0 M 0) A :=
    (ev_faf_mem M0 (et_bvar5 M0 A (simCfgV M0 M N) O (nextStepV M0 M) (simCfgV M0 M 0) _)
      (et_bvar2 M0 _ A _)).mp hA0_raw
  rw [ev_faf_ball M0 (et_bvar1 M0 A _)] at hAstep_raw
  have hAstep : ∀ y : M0.V, M0.mem y A → M0.mem (zfcAppV M0 (nextStepV M0 M) y) A := by
    intro y hy
    exact (ev_faf_mem M0
      (et_comp2 M0 (ev_value M0) (et_bvar6 M0 y A A (simCfgV M0 M N) O (nextStepV M0 M) _) (et_bvar1 M0 y _))
      (et_bvar4 M0 _ y A A _)).mp (hAstep_raw y hy)
  have hAk : ∀ k : ℕ, M0.mem (simCfgV M0 M k) A := by
    intro k
    induction k with
    | zero => exact hA0
    | succ k ih =>
      rw [← zfcAppV_nextStepV_simCfg M0 M k]
      exact hAstep _ ih
  exact (ev_faf_mem M0 (et_bvar2 M0 A (simCfgV M0 M N) _) (et_bvar2 M0 _ A _)).mpr (hAk N)

end WithModel

end C14Stage2

theorem C14Stage2.zfc_proves_halts {n : ℕ} [NeZero n] (M : Turing.BusyBeaver.Machine (Fin 2) (Fin n))
    (h : ∃ N : ℕ, M.multiStep (Turing.BusyBeaver.Machine.init []) N = none) :
    FFL.Entailment.Provable FFL.FirstOrder.SetTheory.ZermeloFraenkelChoice (Constant14.halts M) :=
  C14Completeness.zfc_complete (Constant14.halts M) fun V mem hZFC =>
    C14Stage2.model_satisfies_halts ⟨V, mem, hZFC⟩ M h

theorem OMA.solution : OMA.R_Constant14_c14_ge_4_R1.H1 := by
  intro n hn M _ hM
  obtain ⟨k, hk⟩ := (Turing.BusyBeaver.Machine.isHalting_iff_exists_haltsAt M).mp hM
  exact C14Stage2.zfc_proves_halts M ⟨k + 1, hk⟩
