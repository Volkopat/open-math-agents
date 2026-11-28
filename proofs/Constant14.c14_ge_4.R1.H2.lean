import OMAReductions.R_Constant14_c14_ge_4_R1
import Mathlib.Tactic

-- Step Constant14.c14_ge_4.R1.H2: hypothesis H2 of reduction Constant14.c14_ge_4.R1
-- Credit: @KevinBigham
-- Credit: @steveDOTdigital (BeaverBound finite-automata BB(3) decider tree from proofs/BusyBeaver.BB_3.lean)
-- Powered by friendship, good vibes, and Lean 4 kernel verification.


/-!
# Stage 1: Gödel's Completeness Theorem for `FFL.FirstOrder.Derivation` over `ℒₛₑₜ`
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


end WithModel

end C14Stage2


namespace BeaverBound

open Turing Turing.BusyBeaver

abbrev Symbol := Fin 2
abbrev Key (n : ℕ) := Fin n × Symbol
abbrev MachineOf (n : ℕ) [NeZero n] := Machine Symbol (Fin n)

structure Move (n : ℕ) where
  state : Fin n
  write : Symbol
  left : Bool
  deriving DecidableEq

structure Position (n : ℕ) where
  state : Fin n
  ls : List Symbol
  head : Symbol
  rs : List Symbol
  deriving DecidableEq

def start (n : ℕ) [NeZero n] : Position n := ⟨0, [], 0, []⟩

def push (a : Symbol) (xs : List Symbol) : List Symbol :=
  if a = 0 ∧ xs = [] then [] else a :: xs

def Position.move (c : Position n) (m : Move n) : Position n :=
  if m.left then ⟨m.state, c.ls.tail, c.ls.headI, push m.write c.rs⟩
  else ⟨m.state, push m.write c.ls, c.rs.headI, c.rs.tail⟩

def Move.flip (m : Move n) : Move n := { m with left := !m.left }

def Position.flip (c : Position n) : Position n := ⟨c.state, c.rs, c.head, c.ls⟩

theorem flip_move (c : Position n) (m : Move n) :
    (c.move m).flip = c.flip.move m.flip := by
  cases m with
  | mk q a d => cases d <;> rfl

theorem mk_push (a : Symbol) (xs : List Symbol) :
    ListBlank.mk (push a xs) = (ListBlank.mk xs).cons a := by
  unfold push
  split
  · rename_i h
    rcases h with ⟨rfl, rfl⟩
    exact (ListBlank.cons_head_tail (ListBlank.mk ([] : List Symbol))).symm
  · exact (ListBlank.cons_mk a xs).symm

def Position.view [NeZero n] (c : Position n) : Cfg Symbol (Fin n) :=
  ⟨some c.state, ⟨c.head, ListBlank.mk c.ls, ListBlank.mk c.rs⟩⟩

theorem view_start (n : ℕ) [NeZero n] : (start n).view = Machine.init [] := rfl

def Move.command (m : Move n) : Option (Option (Fin n) × Stmt Symbol) :=
  some (some m.state, Stmt.write m.write (if m.left then Dir.left else Dir.right))

def ongoing [NeZero n] (M : MachineOf n) (k : Key n) : Option (Move n) :=
  match M k.1 k.2 with
  | some (some q, ⟨b, .left⟩) => some ⟨q, b, true⟩
  | some (some q, ⟨b, .right⟩) => some ⟨q, b, false⟩
  | _ => none

theorem ongoing_command [NeZero n] (M : MachineOf n) (k : Key n) (m : Move n)
    (h : ongoing M k = some m) : M k.1 k.2 = m.command := by
  rcases m with ⟨q, a, d⟩
  unfold ongoing at h
  split at h <;> simp_all [Move.command, Move.mk.injEq]

theorem step_move [NeZero n] (M : MachineOf n) (c : Position n) (m : Move n)
    (h : ongoing M (c.state, c.head) = some m) :
    M.step c.view = some (c.move m).view := by
  have he := ongoing_command M (c.state, c.head) m h
  change M c.state c.head = m.command at he
  cases m with
  | mk q a d =>
    cases d <;> simp [Position.view, Machine.step, he, Move.command, Position.move,
      Tape.write, Tape.move, mk_push]

theorem step_stop [NeZero n] (M : MachineOf n) (c : Position n)
    (h : ongoing M (c.state, c.head) = none) : M.HaltsAfter c.view 1 := by
  unfold ongoing at h
  split at h
  all_goals try contradiction
  cases hc : M c.state c.head with
  | none => simp [Machine.HaltsAfter, Machine.multiStep_succ, Position.view, Machine.step, hc]
  | some pair =>
    obtain ⟨q, b, d⟩ := pair
    cases q with
    | none => simp [Machine.HaltsAfter, Machine.multiStep_succ, Position.view, Machine.step, hc]
    | some q => cases d <;> simp_all

theorem multi_succ_front [NeZero n] (M : MachineOf n) (c : Cfg Symbol (Fin n)) (k : ℕ) :
    M.multiStep c (k+1) = (M.step c).bind (fun c' => M.multiStep c' k) := by
  induction k with
  | zero => rw [Machine.multiStep_one]; cases M.step c <;> rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, ih]
    cases h : M.step c with
    | none => rfl
    | some d => simp [Machine.multiStep_succ]

abbrev Program (n : ℕ) := List (Key n × Move n)

def Program.get : Program n → Key n → Option (Move n)
  | [], _ => none
  | (a, m) :: rest, k => if k = a then some m else Program.get rest k

def Program.flip (tb : Program n) : Program n := tb.map fun (k, m) => (k, m.flip)

theorem get_flip (tb : Program n) (k : Key n) : tb.flip.get k = (tb.get k).map Move.flip := by
  induction tb with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨k', m⟩ := x
    by_cases h : k = k' <;> simp [Program.flip, Program.get, h] at ih ⊢
    exact ih


def Matches [NeZero n] (M : MachineOf n) (tb : Program n) : Prop :=
  ∀ k m, tb.get k = some m → ongoing M k = some m

theorem matches_empty [NeZero n] (M : MachineOf n) : Matches M [] := by
  intro k m h
  contradiction

theorem matches_add [NeZero n] {M : MachineOf n} {tb : Program n} {k : Key n} {m : Move n}
    (hm : Matches M tb) (h : ongoing M k = some m) : Matches M ((k, m) :: tb) := by
  intro k' m' hh
  by_cases e : k' = k
  · subst k'
    simp [Program.get] at hh
    simpa [← hh] using h
  · apply hm k' m'
    simpa [Program.get, e] using hh


end BeaverBound

namespace BeaverBound

open Turing Turing.BusyBeaver

-- A DFA reads a left half-tape from the far end toward the head. Its initial
-- state is fixed by the blank symbol, so appending blank cells changes nothing.
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
  unfold push
  split
  · rename_i h
    rcases h with ⟨rfl, rfl⟩
    exact D.blank.symm
  · rfl

theorem TapeDFA.read_pop (D : TapeDFA) (xs : List Symbol) :
    D.next xs.headI (D.read xs.tail) = D.read xs := by
  cases xs
  · exact D.blank
  · rfl

-- Each NFA state records a control state and a left DFA state. The extra state
-- is accepting. The NFA reads the other half of the tape, starting at the head.
structure Certificate (n : ℕ) where
  mirror : Bool
  dfa : TapeDFA
  edges : ℕ
  blankReach : ℕ

abbrev Node (cert : Certificate n) := Option (Fin n × Fin cert.dfa.size)

def nodeId (cert : Certificate n) : Node cert → ℕ
  | none => n * cert.dfa.size
  | some (q, l) => q.val * cert.dfa.size + l.val

def Certificate.edge (cert : Certificate n) (p : Node cert) (a : Symbol)
    (q : Node cert) : Bool :=
  match p with
  | none => q.isNone
  | some _ => cert.edges.testBit ((2 * nodeId cert p + a.val) *
      (n * cert.dfa.size + 1) + nodeId cert q)

def Certificate.onBlank (cert : Certificate n) (p : Node cert) : Bool :=
  cert.blankReach.testBit (nodeId cert p)

def unpack (n val : ℕ) : Certificate n :=
  let extra := val / 2 % 8
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := val / 16 / dfaBase
  let width := n * size + 1
  let initialBase := 2 ^ width
  ⟨val % 2 == 1, ⟨extra, val / 16 % dfaBase⟩, payload / initialBase, payload % initialBase⟩

def nodes (cert : Certificate n) : List (Node cert) :=
  none :: (List.finRange n).flatMap fun q =>
    (List.finRange cert.dfa.size).map fun l => some (q, l)

theorem allFin {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (a : Fin n) : p a = true := (List.all_eq_true.mp h) a (by simp)

theorem allNodes {cert : Certificate n} {p : Node cert → Bool}
    (h : (nodes cert).all p = true) (a : Node cert) : p a = true := by
  refine (List.all_eq_true.mp h) a ?_
  rcases a with _ | ⟨q, l⟩
  · simp [nodes]
  · simp [nodes]

def checkBlank (cert : Certificate n) [NeZero n] : Bool :=
  cert.onBlank (some (0, 0)) && !cert.onBlank none &&
    (nodes cert).all (fun p => if cert.onBlank p then
      (nodes cert).all fun q => !cert.edge p 0 q || cert.onBlank q
    else true)

def checkAt (tb : Program n) (cert : Certificate n) (q : Fin n) (a : Symbol)
    (l : Fin cert.dfa.size) : Bool :=
  let p : Node cert := some (q, l)
  match tb.get (q, a) with
  | none => cert.edge p a none
  | some m =>
    if m.left then
      (List.finRange cert.dfa.size).all fun l' => (List.finRange 2).all fun a' =>
        if cert.dfa.next a' l' = l then
          (nodes cert).all fun s => if cert.edge (some (m.state, l')) a' s then
            (nodes cert).all fun t => !cert.edge s m.write t || cert.edge p a t
          else true
        else true
    else cert.edge p a (some (m.state, cert.dfa.next m.write l))

def checkMachine (tb : Program n) (cert : Certificate n) : Bool :=
  (List.finRange n).all fun q => (List.finRange 2).all fun a =>
    (List.finRange cert.dfa.size).all fun l => checkAt tb cert q a l


def checkCertificate [NeZero n] (tb : Program n) (val : ℕ) : Bool :=
  let C := unpack n val
  checkBlank C && checkMachine (if C.mirror then tb.flip else tb) C


end BeaverBound

namespace BeaverBound

open Turing Turing.BusyBeaver

def firstMissing (tb : Program n) : ℕ → Position n → Option (Key n)
  | 0, _ => none
  | fuel + 1, c =>
    match tb.get (c.state, c.head) with
    | none => some (c.state, c.head)
    | some m => firstMissing tb fuel (c.move m)

theorem firstMissing_stops [NeZero n] {M : MachineOf n} {tb : Program n}
    (hm : Matches M tb) (fuel : ℕ) (c : Position n) {k : Key n}
    (h : firstMissing tb fuel c = some k) (halt : ongoing M k = none) : M.HaltsAfter c.view fuel := by
  induction fuel generalizing c with
  | zero => simp [firstMissing] at h
  | succ fuel ih =>
    cases ht : tb.get (c.state, c.head) with
    | none =>
      simp [firstMissing, ht] at h
      subst k
      exact Machine.multiStep_eq_none_mono (step_stop M c halt) (by omega)
    | some m =>
      have htail : firstMissing tb fuel (c.move m) = some k := by
        simpa [firstMissing, ht] using h
      unfold Machine.HaltsAfter
      rw [multi_succ_front, step_move M c m (hm _ _ ht), Option.bind_some]
      exact ih _ htail

def holes (tb : Program n) : Finset (Key n) :=
  Finset.univ.filter fun k => tb.get k = none

theorem missing_is_hole {tb : Program n} {c : Position n} {k : Key n} {fuel : ℕ}
    (h : firstMissing tb fuel c = some k) : k ∈ holes tb := by
  induction fuel generalizing c with
  | zero => simp [firstMissing] at h
  | succ fuel ih =>
    cases he : tb.get (c.state, c.head) with
    | none =>
      simp [firstMissing, he] at h
      subst k
      simp [holes, he]
    | some m =>
      exact ih (by simpa [firstMissing, he] using h)

theorem holes_add (tb : Program n) (k : Key n) (m : Move n) :
    holes ((k, m) :: tb) = (holes tb).erase k := by
  ext k'
  simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  rw [Program.get]
  by_cases e : k' = k <;> simp [e]


def moves (n : ℕ) : List (Move n) := (List.finRange n).flatMap fun q =>
  (List.finRange 2).flatMap fun a => [⟨q, a, false⟩, ⟨q, a, true⟩]

theorem mem_moves (m : Move n) : m ∈ moves n := by
  obtain ⟨q, a, d⟩ := m
  rw [moves, List.mem_flatMap]
  refine ⟨q, by simp, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨a, by simp, ?_⟩
  cases d <;> simp

def checkTree [NeZero n] (limit : ℕ) : ℕ → Program n → List ℕ → Option (List ℕ)
  | 0, _, certs => some certs
  | fuel + 1, tb, certs =>
    match firstMissing tb limit (start n) with
    | none => match certs with
      | [] => none
      | v :: rest => if checkCertificate tb v then some rest else none
    | some k => (moves n).foldlM (fun rest m => checkTree limit fuel ((k, m) :: tb) rest) certs

theorem succeeds_each {α β : Type*} {items : List α} {f : β → α → Option β}
    {a b : β} (h : items.foldlM f a = some b) {i : α} (hi : i ∈ items) :
    ∃ x y, f x i = some y := by
  induction items generalizing a with
  | nil => simp at hi
  | cons head tail ih =>
    rw [List.foldlM_cons] at h
    cases hh : f a head with
    | none => simp [hh] at h
    | some mid =>
      simp only [hh] at h
      rcases List.mem_cons.mp hi with rfl | ht
      · exact ⟨_, _, hh⟩
      · exact ih h ht


end BeaverBound

namespace BeaverBound

open Turing Turing.BusyBeaver

section Symmetry

variable {n : ℕ} [NeZero n]

def orient (mirror : Bool) (d : Dir) : Dir :=
  if mirror then match d with
  | .left => .right
  | .right => .left
  else d

def orientTape (mirror : Bool) (t : Tape Symbol) : Tape Symbol :=
  if mirror then ⟨t.head, t.right, t.left⟩ else t

def orientCfg (e : Fin n ≃ Fin n) (mirror : Bool) (c : Cfg Symbol (Fin n)) : Cfg Symbol (Fin n) :=
  ⟨c.q.map e, orientTape mirror c.tape⟩

def reindex (M : MachineOf n) (e : Fin n ≃ Fin n) (mirror : Bool) : MachineOf n :=
  fun q a => (M (e.symm q) a).map fun (s, b) => (s.map e, ⟨b.symbol, orient mirror b.dir⟩)

theorem reindex_step (M : MachineOf n) (e : Fin n ≃ Fin n) (mirror : Bool)
    (c : Cfg Symbol (Fin n)) : (reindex M e mirror).step (orientCfg e mirror c) =
      (M.step c).map (orientCfg e mirror) := by
  obtain ⟨q, ⟨a, l, r⟩⟩ := c
  cases q with
  | none => rfl
  | some p =>
    cases mirror <;>
      simp only [Machine.step, orientCfg, orientTape, Bool.false_eq_true, if_false, if_true,
        Option.map_some, reindex, Equiv.symm_apply_apply]
    all_goals
      cases h : M p a with
      | none => rfl
      | some entry =>
        rcases entry with ⟨p', b, d⟩
        cases d <;> rfl

theorem reindex_init (e : Fin n ≃ Fin n) (h0 : e 0 = 0) (mirror : Bool) :
    orientCfg e mirror (Machine.init []) = Machine.init [] := by
  cases mirror <;> simpa [orientCfg, orientTape, Machine.init, Tape.mk₁, Tape.mk₂, Tape.mk']
    using h0

theorem reindex_multi (M : MachineOf n) (e : Fin n ≃ Fin n) (mirror : Bool)
    (c : Cfg Symbol (Fin n)) (k : ℕ) :
    (reindex M e mirror).multiStep (orientCfg e mirror c) k =
      (M.multiStep c k).map (orientCfg e mirror) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
    cases he : M.multiStep c k with
    | none => rfl
    | some c' => exact reindex_step M e mirror c'

theorem reindex_haltsAfter (M : MachineOf n) (e : Fin n ≃ Fin n) (h0 : e 0 = 0)
    (mirror : Bool) (k : ℕ) : (reindex M e mirror).HaltsAfter (Machine.init []) k ↔
      M.HaltsAfter (Machine.init []) k := by
  unfold Machine.HaltsAfter
  conv_lhs => rw [← reindex_init e h0 mirror, reindex_multi]
  exact Option.map_eq_none_iff


omit [NeZero n] in
theorem orient_command (m : Move n) (e : Fin n ≃ Fin n) :
    m.command.map (fun (q, b) => (q.map e, ⟨b.symbol, orient m.left b.dir⟩)) =
      (Move.mk (e m.state) m.write false).command := by
  rcases m with ⟨q, b, d⟩
  cases d <;> rfl

theorem first_reindex {M : MachineOf n} (e : Fin n ≃ Fin n) (h0 : e 0 = 0) (m : Move n)
    (h : ongoing M (0, 0) = some m) :
    ongoing (reindex M e m.left) (0, 0) = some ⟨e m.state, m.write, false⟩ := by
  have he : e.symm 0 = (0 : Fin n) := e.symm_apply_eq.mpr h0.symm
  have hcmd := ongoing_command M (0, 0) m h
  change M 0 0 = m.command at hcmd
  have hr : reindex M e m.left 0 0 = (Move.mk (e m.state) m.write false).command := by
    unfold reindex
    rw [he, hcmd, orient_command]
  simp [ongoing, hr, Move.command]

end Symmetry

end BeaverBound

namespace C14H2

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver C14Completeness C14Stage2
open scoped Classical

/- ## Part 1: Finite Conjunction Helper and `vnOmegaV` Ordinal Theory -/

def bigAnd {ξ : Type*} {m : ℕ} : List (Semiformula ℒₛₑₜ ξ m) → Semiformula ℒₛₑₜ ξ m
  | [] => ⊤
  | φ :: φs => φ ⋏ bigAnd φs

lemma evalM_bigAnd {V : Type} {mem : V → V → Prop} {ξ : Type*} {m : ℕ}
    (e : Fin m → V) (ε : ξ → V) (l : List (Semiformula ℒₛₑₜ ξ m)) :
    evalM mem e ε (bigAnd l) ↔ ∀ φ ∈ l, evalM mem e ε φ := by
  induction l with
  | nil => simp [bigAnd, evalM_top]
  | cons φ φs ih =>
    simp only [bigAnd, evalM_and, ih, List.mem_cons, forall_eq_or_imp]

section ModelBridge

variable (M0 : ZFCModel)

lemma vnOmegaV_inductive :
    M0.mem (emptyV M0) (vnOmegaV M0) ∧
      ∀ y : M0.V, M0.mem y (vnOmegaV M0) → M0.mem (insertV M0 y y) (vnOmegaV M0) := by
  constructor
  · rw [mem_vnOmegaV_iff]; exact fun _ hI => hI.1
  · intro y hy
    rw [mem_vnOmegaV_iff] at hy ⊢
    exact fun I hI => hI.2 y (hy I hI)

lemma vnOmegaV_ind (φ : SetTheorySemiproposition 1) (ε : ℕ → M0.V)
    (h0 : evalM M0.mem ![emptyV M0] ε φ)
    (hs : ∀ y : M0.V, M0.mem y (vnOmegaV M0) → evalM M0.mem ![y] ε φ →
      evalM M0.mem ![insertV M0 y y] ε φ) :
    ∀ x : M0.V, M0.mem x (vnOmegaV M0) → evalM M0.mem ![x] ε φ := by
  obtain ⟨I, hI⟩ := sepV M0 (vnOmegaV M0) φ ε
  have hI_ind : M0.mem (emptyV M0) I ∧ ∀ y : M0.V, M0.mem y I → M0.mem (insertV M0 y y) I := by
    refine ⟨(hI _).mpr ⟨(vnOmegaV_inductive M0).1, h0⟩, fun y hy => ?_⟩
    obtain ⟨hyω, hyφ⟩ := (hI y).mp hy
    exact (hI _).mpr ⟨(vnOmegaV_inductive M0).2 y hyω, hs y hyω hyφ⟩
  intro x hx
  exact ((hI x).mp ((mem_vnOmegaV_iff M0).mp hx I hI_ind)).2

lemma vnOmegaV_zero_or_succ {r : M0.V} (hr : M0.mem r (vnOmegaV M0)) :
    r = emptyV M0 ∨ ∃ m : M0.V, M0.mem m (vnOmegaV M0) ∧ r = insertV M0 m m := by
  let φ : SetTheorySemiproposition 1 :=
    (Rew.subst ![#0] ▹ Rewriting.emb SetTheory.isEmpty) ⋎
      Semiformula.bexsMem (&0) (Rew.subst ![#1, #0] ▹ Rewriting.emb SetTheory.succ.dfn)
  have hφ : ∀ x : M0.V, evalM M0.mem ![x] (fun _ => vnOmegaV M0) φ ↔
      x = emptyV M0 ∨ ∃ m : M0.V, M0.mem m (vnOmegaV M0) ∧ x = insertV M0 m m := by
    intro x
    dsimp only [φ]
    rw [evalM_or, evalM_bexsMem]
    refine or_congr ?_ (exists_congr fun m => and_congr Iff.rfl ?_)
    · change evalM M0.mem ![x] _ ((Rewriting.emb SetTheory.isEmpty) ⇜ ![#0]) ↔ _
      rw [evalM_subst, evalM_emb]
      refine (evalRaw_congr Eq M0.mem SetTheory.isEmpty ?_ rfl).trans (ev_isEmpty M0 x)
      funext i; fin_cases i; rfl
    · change evalM M0.mem (m :> x :> ![]) _ ((Rewriting.emb SetTheory.succ.dfn) ⇜ ![#1, #0]) ↔ _
      rw [evalM_subst, evalM_emb]
      refine (evalRaw_congr Eq M0.mem SetTheory.succ.dfn ?_ rfl).trans (ev_succ M0 x m)
      funext i; fin_cases i <;> rfl
  exact (hφ r).mp (vnOmegaV_ind M0 φ (fun _ => vnOmegaV M0)
    ((hφ _).mpr (Or.inl rfl))
    (fun y hy _ => (hφ _).mpr (Or.inr ⟨y, hy, rfl⟩))
    r hr)

lemma vnOmegaV_trans_mem {x y : M0.V} (hx : M0.mem x (vnOmegaV M0)) (hyx : M0.mem y x) :
    M0.mem y (vnOmegaV M0) ∧ ∀ z : M0.V, M0.mem z y → M0.mem z x := by
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.ballMem (#0)
      (Semiformula.rel Language.Set.Rel.mem ![#0, &0] ⋏
        Semiformula.ballMem (#0) (Semiformula.rel Language.Set.Rel.mem ![#0, #2]))
  have hφ : ∀ u : M0.V, evalM M0.mem ![u] (fun _ => vnOmegaV M0) φ ↔
      ∀ y : M0.V, M0.mem y u → M0.mem y (vnOmegaV M0) ∧ ∀ z : M0.V, M0.mem z y → M0.mem z u := by
    intro u
    dsimp only [φ]
    rw [evalM_ballMem]
    refine forall₂_congr fun y _ => ?_
    rw [evalM_and, evalM_ballMem]
    rfl
  have hall := (hφ x).mp (vnOmegaV_ind M0 φ (fun _ => vnOmegaV M0)
    ((hφ _).mpr fun y hy => (not_mem_emptyV M0 y hy).elim)
    (fun u hu ih => (hφ _).mpr fun y hy => by
      rcases (mem_insertV M0).mp hy with rfl | hyu
      · exact ⟨hu, fun z hz => (mem_insertV M0).mpr (Or.inr hz)⟩
      · obtain ⟨hyω, htrans⟩ := ((hφ u).mp ih) y hyu
        exact ⟨hyω, fun z hz => (mem_insertV M0).mpr (Or.inr (htrans z hz))⟩)
    x hx)
  exact hall y hyx

lemma vnOmegaV_zero_le {y : M0.V} (hy : M0.mem y (vnOmegaV M0)) :
    y = emptyV M0 ∨ M0.mem (emptyV M0) y := by
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.rel Language.Set.Rel.eq ![#0, &0] ⋎
      Semiformula.rel Language.Set.Rel.mem ![&0, #0]
  have hφ : ∀ u : M0.V, evalM M0.mem ![u] (fun _ => emptyV M0) φ ↔
      u = emptyV M0 ∨ M0.mem (emptyV M0) u := by
    intro u; dsimp only [φ]; rw [evalM_or]; rfl
  exact (hφ y).mp (vnOmegaV_ind M0 φ (fun _ => emptyV M0)
    ((hφ _).mpr (Or.inl rfl))
    (fun u _ ih => (hφ _).mpr (Or.inr ((mem_insertV M0).mpr
      (by rcases (hφ u).mp ih with rfl | h0; exact Or.inl rfl; exact Or.inr h0))))
    y hy)

lemma vnOmegaV_succ_le_of_mem {x y : M0.V}
    (_hx : M0.mem x (vnOmegaV M0)) (hy : M0.mem y (vnOmegaV M0)) (hxy : M0.mem x y) :
    M0.mem (insertV M0 x x) y ∨ insertV M0 x x = y := by
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.rel Language.Set.Rel.mem ![&0, #0] 🡒
      (Semiformula.rel Language.Set.Rel.mem ![&1, #0] ⋎
        Semiformula.rel Language.Set.Rel.eq ![&1, #0])
  let ε : ℕ → M0.V := fun k => if k = 0 then x else insertV M0 x x
  have hφ : ∀ u : M0.V, evalM M0.mem ![u] ε φ ↔
      (M0.mem x u → M0.mem (insertV M0 x x) u ∨ insertV M0 x x = u) := by
    intro u; dsimp only [φ]; rw [evalM_imp, evalM_or]; rfl
  exact ((hφ y).mp (vnOmegaV_ind M0 φ ε
    ((hφ _).mpr fun h => (not_mem_emptyV M0 x h).elim)
    (fun u _ ih => (hφ _).mpr fun hxu => by
      rcases (mem_insertV M0).mp hxu with rfl | hxu'
      · exact Or.inr rfl
      · left
        rcases ((hφ u).mp ih) hxu' with h1 | h2
        · exact (mem_insertV M0).mpr (Or.inr h1)
        · exact (mem_insertV M0).mpr (Or.inl h2))
    y hy)) hxy

lemma vnOmegaV_trichotomy {x y : M0.V}
    (hx : M0.mem x (vnOmegaV M0)) (hy : M0.mem y (vnOmegaV M0)) :
    M0.mem x y ∨ x = y ∨ M0.mem y x := by
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.ballMem (&0)
      (Semiformula.rel Language.Set.Rel.mem ![#1, #0] ⋎
        Semiformula.rel Language.Set.Rel.eq ![#1, #0] ⋎
        Semiformula.rel Language.Set.Rel.mem ![#0, #1])
  have hφ : ∀ u : M0.V, evalM M0.mem ![u] (fun _ => vnOmegaV M0) φ ↔
      ∀ v : M0.V, M0.mem v (vnOmegaV M0) → M0.mem u v ∨ u = v ∨ M0.mem v u := by
    intro u; dsimp only [φ]; rw [evalM_ballMem]
    refine forall₂_congr fun v _ => ?_
    rw [evalM_or, evalM_or]; rfl
  exact ((hφ x).mp (vnOmegaV_ind M0 φ (fun _ => vnOmegaV M0)
    ((hφ _).mpr fun v hv => by
      rcases vnOmegaV_zero_le M0 hv with rfl | h0
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl h0)
    (fun u hu ih => (hφ _).mpr fun v hv => by
      rcases ((hφ u).mp ih) v hv with huv | rfl | hvu
      · rcases vnOmegaV_succ_le_of_mem M0 hu hv huv with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ((mem_insertV M0).mpr (Or.inl rfl)))
      · exact Or.inr (Or.inr ((mem_insertV M0).mpr (Or.inr hvu))))
    x hx)) y hy

/- ## Part 2: Total `intSuccV`, `intPredV`, `intLtV`, `intNegV` on `intSetV M0` -/

lemma exists_intSuccV {u : M0.V} (hu : M0.mem u (intSetV M0)) :
    ∃ u' : M0.V, M0.mem u' (intSetV M0) ∧
      ∀ w : M0.V, mEv M0 ![w, u] Constant14.integerSucc.dfn ↔ w = u' := by
  obtain ⟨a, ha, r, hr, rfl⟩ := (mem_prodV M0).mp hu
  obtain ⟨s, hs, rfl⟩ := (mem_vnNatV_iff M0).mp ha
  have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
  interval_cases s
  · refine ⟨kpairV M0 (vnNatV M0 0) (insertV M0 r r),
      (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 0 < 2), (vnOmegaV_inductive M0).2 r hr⟩,
      fun w => ?_⟩
    rw [ev_integerSucc_of_mem M0 hu, pi1V_kpairV, pi2V_kpairV]
    simp [h01]
  · rcases vnOmegaV_zero_or_succ M0 hr with rfl | ⟨m, hm, rfl⟩
    · refine ⟨encodeIntV M0 0, encodeIntV_mem M0 0, fun w => ?_⟩
      rw [ev_integerSucc_of_mem M0 hu, pi1V_kpairV, pi2V_kpairV]
      have hno : ¬ ∃ m : M0.V, M0.mem m (vnOmegaV M0) ∧
          emptyV M0 = insertV M0 m m ∧ w = kpairV M0 (vnNatV M0 1) m := by
        rintro ⟨m, _, hm, _⟩
        exact not_mem_emptyV M0 m (hm ▸ (mem_insertV M0).mpr (Or.inl rfl))
      have h0eq : (emptyV M0 = vnNatV M0 0) ↔ True := iff_true_intro rfl
      simp only [eq_false h01.symm, h0eq, false_and, false_or, true_and, hno, or_false]
    · refine ⟨kpairV M0 (vnNatV M0 1) m,
        (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 1 < 2), hm⟩, fun w => ?_⟩
      rw [ev_integerSucc_of_mem M0 hu, pi1V_kpairV, pi2V_kpairV]
      have hne0 : insertV M0 m m ≠ vnNatV M0 0 := by
        intro h
        change insertV M0 m m = emptyV M0 at h
        exact not_mem_emptyV M0 m (h ▸ (mem_insertV M0).mpr (Or.inl rfl))
      simp only [h01.symm, false_and, false_or, true_and, hne0]
      constructor
      · rintro ⟨m', _, hsucc, rfl⟩
        have hmm : m = m' := succV_inj M0 hsucc
        subst hmm; rfl
      · rintro rfl
        exact ⟨m, hm, rfl, rfl⟩

noncomputable def intSuccV (u : M0.V) : M0.V :=
  if hu : M0.mem u (intSetV M0) then (exists_intSuccV M0 hu).choose else emptyV M0

lemma intSuccV_mem {u : M0.V} (hu : M0.mem u (intSetV M0)) :
    M0.mem (intSuccV M0 u) (intSetV M0) := by
  unfold intSuccV; rw [dif_pos hu]; exact (exists_intSuccV M0 hu).choose_spec.1

lemma ev_integerSucc_iff {u : M0.V} (hu : M0.mem u (intSetV M0)) (w : M0.V) :
    mEv M0 ![w, u] Constant14.integerSucc.dfn ↔ w = intSuccV M0 u := by
  unfold intSuccV; rw [dif_pos hu]; exact (exists_intSuccV M0 hu).choose_spec.2 w

lemma exists_intPredV {u : M0.V} (hu : M0.mem u (intSetV M0)) :
    ∃ u' : M0.V, M0.mem u' (intSetV M0) ∧ intSuccV M0 u' = u := by
  obtain ⟨a, ha, r, hr, rfl⟩ := (mem_prodV M0).mp hu
  obtain ⟨s, hs, rfl⟩ := (mem_vnNatV_iff M0).mp ha
  have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
  interval_cases s
  · rcases vnOmegaV_zero_or_succ M0 hr with rfl | ⟨m, hm, rfl⟩
    · refine ⟨encodeIntV M0 (-1), encodeIntV_mem M0 (-1), ?_⟩
      symm
      rw [← ev_integerSucc_iff M0 (encodeIntV_mem M0 (-1)), ev_integerSucc_encode]
      rfl
    · let u' := kpairV M0 (vnNatV M0 0) m
      have hu' : M0.mem u' (intSetV M0) :=
        (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 0 < 2), hm⟩
      refine ⟨u', hu', ?_⟩
      symm
      rw [← ev_integerSucc_iff M0 hu', ev_integerSucc_of_mem M0 hu']
      left
      simp [u', pi1V_kpairV, pi2V_kpairV]
  · let u' := kpairV M0 (vnNatV M0 1) (insertV M0 r r)
    have hu' : M0.mem u' (intSetV M0) :=
      (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 1 < 2), (vnOmegaV_inductive M0).2 r hr⟩
    refine ⟨u', hu', ?_⟩
    symm
    rw [← ev_integerSucc_iff M0 hu', ev_integerSucc_of_mem M0 hu']
    right
    refine ⟨by simp [u', pi1V_kpairV], Or.inr ⟨r, hr, by simp [u', pi2V_kpairV], rfl⟩⟩

lemma intSuccV_inj {u₁ u₂ : M0.V} (h₁ : M0.mem u₁ (intSetV M0)) (h₂ : M0.mem u₂ (intSetV M0))
    (heq : intSuccV M0 u₁ = intSuccV M0 u₂) : u₁ = u₂ := by
  have hs1 : mEv M0 ![intSuccV M0 u₂, u₁] Constant14.integerSucc.dfn :=
    (ev_integerSucc_iff M0 h₁ _).mpr heq.symm
  have hs2 : mEv M0 ![intSuccV M0 u₂, u₂] Constant14.integerSucc.dfn :=
    (ev_integerSucc_iff M0 h₂ _).mpr rfl
  rw [ev_integerSucc_of_mem M0 h₁] at hs1
  rw [ev_integerSucc_of_mem M0 h₂] at hs2
  obtain ⟨a₁, ha₁, r₁, hr₁, rfl⟩ := (mem_prodV M0).mp h₁
  obtain ⟨a₂, ha₂, r₂, hr₂, rfl⟩ := (mem_prodV M0).mp h₂
  rw [pi1V_kpairV, pi2V_kpairV] at hs1 hs2
  have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
  rcases hs1 with ⟨rfl, hw1⟩ | ⟨rfl, ⟨rfl, hw1⟩ | ⟨m₁, _, hr1, hw1⟩⟩ <;>
    rcases hs2 with ⟨rfl, hw2⟩ | ⟨rfl, ⟨rfl, hw2⟩ | ⟨m₂, _, hr2, hw2⟩⟩
  · have hsucc := (kpairV_inj M0 (hw1.symm.trans hw2)).2
    rw [succV_inj M0 hsucc]
  · have hsucc := (kpairV_inj M0 (hw1.symm.trans hw2)).2
    change insertV M0 r₁ r₁ = emptyV M0 at hsucc
    exact (not_mem_emptyV M0 r₁ (hsucc ▸ (mem_insertV M0).mpr (Or.inl rfl))).elim
  · exact (h01 (kpairV_inj M0 (hw1.symm.trans hw2)).1).elim
  · have hsucc := (kpairV_inj M0 (hw1.symm.trans hw2)).2
    change emptyV M0 = insertV M0 r₂ r₂ at hsucc
    exact (not_mem_emptyV M0 r₂ (hsucc.symm ▸ (mem_insertV M0).mpr (Or.inl rfl))).elim
  · rfl
  · exact (h01 (kpairV_inj M0 (hw1.symm.trans hw2)).1).elim
  · exact (h01.symm (kpairV_inj M0 (hw1.symm.trans hw2)).1).elim
  · exact (h01.symm (kpairV_inj M0 (hw1.symm.trans hw2)).1).elim
  · have hm : m₁ = m₂ := (kpairV_inj M0 (hw1.symm.trans hw2)).2
    subst hm; rw [hr1, hr2]

noncomputable def intPredV (u : M0.V) : M0.V :=
  if hu : M0.mem u (intSetV M0) then (exists_intPredV M0 hu).choose else emptyV M0

lemma intPredV_mem {u : M0.V} (hu : M0.mem u (intSetV M0)) :
    M0.mem (intPredV M0 u) (intSetV M0) := by
  unfold intPredV; rw [dif_pos hu]; exact (exists_intPredV M0 hu).choose_spec.1

lemma intSuccV_intPredV {u : M0.V} (hu : M0.mem u (intSetV M0)) :
    intSuccV M0 (intPredV M0 u) = u := by
  unfold intPredV; rw [dif_pos hu]; exact (exists_intPredV M0 hu).choose_spec.2

lemma intPredV_intSuccV {u : M0.V} (hu : M0.mem u (intSetV M0)) :
    intPredV M0 (intSuccV M0 u) = u :=
  intSuccV_inj M0 (intPredV_mem M0 (intSuccV_mem M0 hu)) hu (intSuccV_intPredV M0 (intSuccV_mem M0 hu))

lemma ev_integerPred_iff {u : M0.V} (hu : M0.mem u (intSetV M0)) (w : M0.V) :
    mEv M0 ![w, u] Constant14.integerPred.dfn ↔ w = intPredV M0 u := by
  unfold Constant14.integerPred.dfn
  rw [mEv_or, mEv_and, mEv_and, mEv_and]
  rw [ev_faf_mem M0 (et_bvar2 M0 w u _) (et_const0 M0 (dc_integers M0) _),
      ev_faf_mem M0 (et_bvar1 M0 w _) (et_const0 M0 (dc_integers M0) _),
      ev_nest2 M0 Constant14.integerSucc.dfn (et_bvar2 M0 w u _) (et_bvar1 M0 w _),
      ev_faf_notMem M0 (et_bvar2 M0 w u _) (et_const0 M0 (dc_integers M0) _)]
  simp only [hu, not_true_eq_false, false_and, or_false, true_and]
  constructor
  · rintro ⟨hw, hsucc⟩
    rw [ev_integerSucc_iff M0 hw] at hsucc
    exact intSuccV_inj M0 hw (intPredV_mem M0 hu) (hsucc.symm.trans (intSuccV_intPredV M0 hu).symm)
  · rintro rfl
    refine ⟨intPredV_mem M0 hu, ?_⟩
    rw [ev_integerSucc_iff M0 (intPredV_mem M0 hu), intSuccV_intPredV M0 hu]

/- ## Part 3: Order `intLtV`, Negation `intNegV`, Total `nextStepV`, and `not_halts_of_invariant` -/

def intLtV (u v : M0.V) : Prop :=
  (pi1V M0 u = vnNatV M0 1 ∧ pi1V M0 v = vnNatV M0 0) ∨
  (pi1V M0 u = vnNatV M0 0 ∧ pi1V M0 v = vnNatV M0 0 ∧ M0.mem (pi2V M0 u) (pi2V M0 v)) ∨
  (pi1V M0 u = vnNatV M0 1 ∧ pi1V M0 v = vnNatV M0 1 ∧ M0.mem (pi2V M0 v) (pi2V M0 u))

def intLeV (u v : M0.V) : Prop := u = v ∨ intLtV M0 u v

def intLtFormula : SetTheorySemisentence 2 :=
  f“u v. (!SetTheory.kpair.π₁.dfn u = !(Constant14.numeral 1) ∧
          !SetTheory.kpair.π₁.dfn v = !(Constant14.numeral 0)) ∨
         (!SetTheory.kpair.π₁.dfn u = !(Constant14.numeral 0) ∧
          !SetTheory.kpair.π₁.dfn v = !(Constant14.numeral 0) ∧
          !SetTheory.kpair.π₂.dfn u ∈ !SetTheory.kpair.π₂.dfn v) ∨
         (!SetTheory.kpair.π₁.dfn u = !(Constant14.numeral 1) ∧
          !SetTheory.kpair.π₁.dfn v = !(Constant14.numeral 1) ∧
          !SetTheory.kpair.π₂.dfn v ∈ !SetTheory.kpair.π₂.dfn u)”

lemma ev_intLt (u v : M0.V) : mEv M0 ![u, v] intLtFormula ↔ intLtV M0 u v := by
  unfold intLtFormula intLtV
  rw [mEv_or, mEv_or, mEv_and, mEv_and, mEv_and, mEv_and, mEv_and]
  refine or_congr
    (and_congr
      (ev_faf_eq M0 (et_comp1 M0 (ev_pi1 M0) (et_bvar1 M0 u _)) (et_const0 M0 (dc_numeral M0 1) _))
      (ev_faf_eq M0 (et_comp1 M0 (ev_pi1 M0) (et_bvar2 M0 u v _)) (et_const0 M0 (dc_numeral M0 0) _)))
    (or_congr
      (and_congr
        (ev_faf_eq M0 (et_comp1 M0 (ev_pi1 M0) (et_bvar1 M0 u _)) (et_const0 M0 (dc_numeral M0 0) _))
        (and_congr
          (ev_faf_eq M0 (et_comp1 M0 (ev_pi1 M0) (et_bvar2 M0 u v _)) (et_const0 M0 (dc_numeral M0 0) _))
          (ev_faf_mem M0 (et_comp1 M0 (ev_pi2 M0) (et_bvar1 M0 u _))
            (et_comp1 M0 (ev_pi2 M0) (et_bvar3 M0 _ u v _)))))
      (and_congr
        (ev_faf_eq M0 (et_comp1 M0 (ev_pi1 M0) (et_bvar1 M0 u _)) (et_const0 M0 (dc_numeral M0 1) _))
        (and_congr
          (ev_faf_eq M0 (et_comp1 M0 (ev_pi1 M0) (et_bvar2 M0 u v _)) (et_const0 M0 (dc_numeral M0 1) _))
          (ev_faf_mem M0 (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 u v _))
            (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 _ u _))))))

lemma intLtV_irrefl (u : M0.V) : ¬ intLtV M0 u u := by
  have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
  rintro (⟨h1, h0⟩ | ⟨_, _, hm⟩ | ⟨_, _, hm⟩)
  · exact h01 (h0.symm.trans h1)
  · exact irreflV M0 _ hm
  · exact irreflV M0 _ hm

lemma intLtV_asymm {u v : M0.V} (huv : intLtV M0 u v) (hvu : intLtV M0 v u) : False := by
  have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
  rcases huv with ⟨h1, h2⟩ | ⟨h1, h2, hm⟩ | ⟨h1, h2, hm⟩ <;>
    rcases hvu with ⟨g1, g2⟩ | ⟨g1, g2, gm⟩ | ⟨g1, g2, gm⟩
  · exact h01 (h2.symm.trans g1)
  · exact h01 (g2.symm.trans h1)
  · exact h01 (h2.symm.trans g1)
  · exact h01 (h2.symm.trans g1)
  · exact asymmV M0 hm gm
  · exact h01 (h1.symm.trans g2)
  · exact h01 (g2.symm.trans h1)
  · exact h01 (g1.symm.trans h2)
  · exact asymmV M0 hm gm

lemma intLtV_trans {u v w : M0.V} (hu : M0.mem u (intSetV M0))
    (hv : M0.mem v (intSetV M0)) (hw : M0.mem w (intSetV M0))
    (huv : intLtV M0 u v) (hvw : intLtV M0 v w) : intLtV M0 u w := by
  obtain ⟨_, _, ru, hru, rfl⟩ := (mem_prodV M0).mp hu
  obtain ⟨_, _, rv, hrv, rfl⟩ := (mem_prodV M0).mp hv
  obtain ⟨_, _, rw_, hrw, rfl⟩ := (mem_prodV M0).mp hw
  simp only [intLtV, pi1V_kpairV, pi2V_kpairV] at huv hvw ⊢
  have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
  rcases huv with ⟨h1, h2⟩ | ⟨h1, h2, hm⟩ | ⟨h1, h2, hm⟩ <;>
    rcases hvw with ⟨g1, g2⟩ | ⟨g1, g2, gm⟩ | ⟨g1, g2, gm⟩
  · exact (h01 (h2.symm.trans g1)).elim
  · exact Or.inl ⟨h1, g2⟩
  · exact (h01 (h2.symm.trans g1)).elim
  · exact (h01 (h2.symm.trans g1)).elim
  · exact Or.inr (Or.inl ⟨h1, g2, (vnOmegaV_trans_mem M0 hrw gm).2 _ hm⟩)
  · exact (h01 (h2.symm.trans g1)).elim
  · exact Or.inl ⟨h1, g2⟩
  · exact (h01 (g1.symm.trans h2)).elim
  · exact Or.inr (Or.inr ⟨h1, g2, (vnOmegaV_trans_mem M0 hru hm).2 _ gm⟩)

lemma intLtV_trichotomy {u v : M0.V} (hu : M0.mem u (intSetV M0)) (hv : M0.mem v (intSetV M0)) :
    intLtV M0 u v ∨ u = v ∨ intLtV M0 v u := by
  obtain ⟨au, hau, ru, hru, rfl⟩ := (mem_prodV M0).mp hu
  obtain ⟨av, hav, rv, hrv, rfl⟩ := (mem_prodV M0).mp hv
  obtain ⟨su, hsu, rfl⟩ := (mem_vnNatV_iff M0).mp hau
  obtain ⟨sv, hsv, rfl⟩ := (mem_vnNatV_iff M0).mp hav
  simp only [intLtV, pi1V_kpairV, pi2V_kpairV]
  interval_cases su <;> interval_cases sv
  · rcases vnOmegaV_trichotomy M0 hru hrv with h | rfl | h
    · exact Or.inl (Or.inr (Or.inl ⟨rfl, rfl, h⟩))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
  · rcases vnOmegaV_trichotomy M0 hru hrv with h | rfl | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩)))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (Or.inr (Or.inr ⟨rfl, rfl, h⟩))

lemma intLtV_self_intSuccV {u : M0.V} (hu : M0.mem u (intSetV M0)) :
    intLtV M0 u (intSuccV M0 u) := by
  have hs := (ev_integerSucc_iff M0 hu (intSuccV M0 u)).mpr rfl
  rw [ev_integerSucc_of_mem M0 hu] at hs
  obtain ⟨a, ha, r, hr, rfl⟩ := (mem_prodV M0).mp hu
  rw [pi1V_kpairV, pi2V_kpairV] at hs
  rcases hs with ⟨rfl, heq⟩ | ⟨rfl, ⟨rfl, heq⟩ | ⟨m, _, rfl, heq⟩⟩
  · rw [heq]; right; left
    simp only [pi1V_kpairV, pi2V_kpairV, true_and]
    exact (mem_insertV M0).mpr (Or.inl rfl)
  · rw [heq]; left
    simp only [encodeIntV, pi1V_kpairV, and_self]
  · rw [heq]; right; right
    simp only [pi1V_kpairV, pi2V_kpairV, true_and]
    exact (mem_insertV M0).mpr (Or.inl rfl)

lemma intLtV_iff_intLeV_intSuccV {u v : M0.V}
    (hu : M0.mem u (intSetV M0)) (hv : M0.mem v (intSetV M0)) :
    intLtV M0 u v ↔ intLeV M0 (intSuccV M0 u) v := by
  constructor
  · intro huv
    have hsu := intSuccV_mem M0 hu
    rcases intLtV_trichotomy M0 hsu hv with hlt | heq | hgt
    · exact Or.inr hlt
    · exact Or.inl heq
    · exfalso
      have hs := (ev_integerSucc_iff M0 hu (intSuccV M0 u)).mpr rfl
      rw [ev_integerSucc_of_mem M0 hu] at hs
      obtain ⟨au, hau, ru, hru, rfl⟩ := (mem_prodV M0).mp hu
      obtain ⟨av, hav, rv, hrv, rfl⟩ := (mem_prodV M0).mp hv
      rw [pi1V_kpairV, pi2V_kpairV] at hs
      have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
      rcases hs with ⟨rfl, heq⟩ | ⟨rfl, ⟨rfl, heq⟩ | ⟨m, hm, rfl, heq⟩⟩
      · rw [heq] at hgt
        simp only [intLtV, pi1V_kpairV, pi2V_kpairV, eq_false h01, false_and, and_false,
          or_false, false_or, true_and] at huv hgt
        obtain ⟨hav0, h1⟩ := huv
        rw [hav0] at hgt
        simp only [eq_false h01, false_and, false_or, true_and] at hgt
        rcases (mem_insertV M0).mp hgt with rfl | h3
        · exact irreflV M0 _ h1
        · exact asymmV M0 h1 h3
      · rw [heq] at hgt
        simp only [intLtV, encodeIntV, pi1V_kpairV, pi2V_kpairV, eq_false h01, eq_false h01.symm,
          false_and, and_false, or_false, false_or, true_and] at huv hgt
        rcases huv with hav0 | ⟨hav1, h1⟩
        · rw [hav0] at hgt
          simp only [eq_false h01, false_and, false_or, true_and] at hgt
          exact not_mem_emptyV M0 _ hgt
        · exact not_mem_emptyV M0 _ h1
      · rw [heq] at hgt
        simp only [intLtV, pi1V_kpairV, pi2V_kpairV, eq_false h01.symm, false_and,
          and_false, false_or, true_and] at huv hgt
        rcases huv with hav0 | ⟨hav1, h1⟩
        · rw [hav0] at hgt
          simp only [eq_false h01, false_and] at hgt
        · rw [hav1] at hgt
          simp only [true_and] at hgt
          rcases (mem_insertV M0).mp h1 with rfl | h3
          · exact irreflV M0 _ hgt
          · exact asymmV M0 hgt h3
  · rintro (rfl | hlt)
    · exact intLtV_self_intSuccV M0 hu
    · exact intLtV_trans M0 hu (intSuccV_mem M0 hu) hv (intLtV_self_intSuccV M0 hu) hlt

lemma intLtV_intPredV_self {u : M0.V} (hu : M0.mem u (intSetV M0)) :
    intLtV M0 (intPredV M0 u) u := by
  have h := intLtV_self_intSuccV M0 (intPredV_mem M0 hu)
  rwa [intSuccV_intPredV M0 hu] at h

/- Generic `constFunV` and `updateFunV` on arbitrary `(X, Y)` -/

lemma exists_constFunV (X Y c : M0.V) (hc : M0.mem c Y) :
    ∃ g : M0.V, ∀ p : M0.V, M0.mem p g ↔ ∃ u : M0.V, M0.mem u X ∧ p = kpairV M0 u c := by
  let ambient := prodV M0 X Y
  let φ : SetTheorySemiproposition 1 :=
    ∃¹ (Rew.subst ![#1, #0, &0] ▹ Rewriting.emb SetTheory.kpair.dfn)
  obtain ⟨g, hg⟩ := sepV M0 ambient φ (fun _ => c)
  refine ⟨g, fun p => ?_⟩
  rw [hg p]
  have hφ : evalM M0.mem ![p] (fun _ => c) φ ↔ ∃ u : M0.V, p = kpairV M0 u c := by
    dsimp only [φ]
    rw [evalM_exs]
    refine exists_congr fun u => ?_
    change evalM M0.mem (u :> p :> ![]) _ ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#1, #0, &0]) ↔ _
    rw [evalM_subst, evalM_emb]
    refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).trans (ev_kpair M0 p u c)
    funext i; fin_cases i <;> rfl
  rw [hφ]
  constructor
  · rintro ⟨hp, u, rfl⟩
    exact ⟨u, ((kpairV_mem_prodV M0).mp hp).1, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(kpairV_mem_prodV M0).mpr ⟨hu, hc⟩, u, rfl⟩

noncomputable def constFunV (X Y c : M0.V) (hc : M0.mem c Y) : M0.V :=
  (exists_constFunV M0 X Y c hc).choose

lemma mem_constFunV {X Y c p : M0.V} (hc : M0.mem c Y) :
    M0.mem p (constFunV M0 X Y c hc) ↔ ∃ u : M0.V, M0.mem u X ∧ p = kpairV M0 u c :=
  (exists_constFunV M0 X Y c hc).choose_spec p

lemma constFunV_mem_funs {X Y c : M0.V} (hc : M0.mem c Y) :
    M0.mem (constFunV M0 X Y c hc) (funsV M0 X Y) := by
  rw [mem_funsV]
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨u, hu, rfl⟩ := (mem_constFunV M0 hc).mp hp
    exact (kpairV_mem_prodV M0).mpr ⟨hu, hc⟩
  · intro u hu
    refine ⟨c, (mem_constFunV M0 hc).mpr ⟨u, hu, rfl⟩, fun y hy => ?_⟩
    obtain ⟨_, _, heq⟩ := (mem_constFunV M0 hc).mp hy
    exact (kpairV_inj M0 heq).2

lemma constFunV_app {X Y c u : M0.V} (hc : M0.mem c Y) (hu : M0.mem u X) :
    zfcAppV M0 (constFunV M0 X Y c hc) u = c :=
  zfcAppV_of_mem_funs M0 (constFunV_mem_funs M0 hc) hu ((mem_constFunV M0 hc).mpr ⟨u, hu, rfl⟩)

lemma exists_updateFunV (X Y g pos val : M0.V) :
    ∃ g' : M0.V, ∀ p : M0.V, M0.mem p g' ↔
      M0.mem p (prodV M0 X Y) ∧
      (p = kpairV M0 pos val ∨ (M0.mem p g ∧ ∀ v : M0.V, p ≠ kpairV M0 pos v)) := by
  let ambient := prodV M0 X Y
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

noncomputable def updateFunV (X Y g pos val : M0.V) : M0.V :=
  (exists_updateFunV M0 X Y g pos val).choose

lemma mem_updateFunV {X Y p g pos val : M0.V} :
    M0.mem p (updateFunV M0 X Y g pos val) ↔
      M0.mem p (prodV M0 X Y) ∧
      (p = kpairV M0 pos val ∨ (M0.mem p g ∧ ∀ v : M0.V, p ≠ kpairV M0 pos v)) :=
  (exists_updateFunV M0 X Y g pos val).choose_spec p

lemma updateFunV_mem_funs {X Y g pos val : M0.V}
    (hg : M0.mem g (funsV M0 X Y)) (hpos : M0.mem pos X) (hval : M0.mem val Y) :
    M0.mem (updateFunV M0 X Y g pos val) (funsV M0 X Y) := by
  obtain ⟨hsub, huniq⟩ := (mem_funsV M0).mp hg
  rw [mem_funsV]
  refine ⟨fun p hp => ((mem_updateFunV M0).mp hp).1, fun u hu => ?_⟩
  by_cases hup : u = pos
  · subst hup
    refine ⟨val, (mem_updateFunV M0).mpr ⟨(kpairV_mem_prodV M0).mpr ⟨hpos, hval⟩, Or.inl rfl⟩, ?_⟩
    intro y hy
    rcases ((mem_updateFunV M0).mp hy).2 with heq | ⟨_, hne⟩
    · exact (kpairV_inj M0 heq).2
    · exact (hne y rfl).elim
  · obtain ⟨y0, hy0, hyeq⟩ := huniq u hu
    refine ⟨y0, ?_, ?_⟩
    · exact (mem_updateFunV M0).mpr
        ⟨hsub _ hy0, Or.inr ⟨hy0, fun v heq => hup (kpairV_inj M0 heq).1⟩⟩
    · intro y hy
      rcases ((mem_updateFunV M0).mp hy).2 with heq | ⟨hyg, _⟩
      · exact (hup (kpairV_inj M0 heq).1).elim
      · exact hyeq y hyg

lemma updateFunV_app {X Y g pos val u : M0.V}
    (hg : M0.mem g (funsV M0 X Y)) (hpos : M0.mem pos X) (hval : M0.mem val Y)
    (hu : M0.mem u X) :
    zfcAppV M0 (updateFunV M0 X Y g pos val) u = if u = pos then val else zfcAppV M0 g u := by
  have hf := updateFunV_mem_funs M0 hg hpos hval
  by_cases hup : u = pos
  · subst hup
    rw [if_pos rfl]
    exact zfcAppV_of_mem_funs M0 hf hpos
      ((mem_updateFunV M0).mpr ⟨(kpairV_mem_prodV M0).mpr ⟨hpos, hval⟩, Or.inl rfl⟩)
  · rw [if_neg hup]
    obtain ⟨hsub, huniq⟩ := (mem_funsV M0).mp hg
    obtain ⟨y0, hy0, _⟩ := huniq u hu
    have happ_g : zfcAppV M0 g u = y0 := zfcAppV_of_mem_funs M0 hg hu hy0
    rw [happ_g]
    exact zfcAppV_of_mem_funs M0 hf hu
      ((mem_updateFunV M0).mpr ⟨hsub _ hy0, Or.inr ⟨hy0, fun v heq => hup (kpairV_inj M0 heq).1⟩⟩)

/- ## Part 4: `intNegV`, `flipTapeV`, Total `nextStepV`, and `HasNonHaltingInvariant` -/

def intNegFormula : SetTheorySemisentence 2 :=
  f“y u.
    (!SetTheory.kpair.π₁.dfn u = !(Constant14.numeral 0) ∧
      !SetTheory.kpair.π₂.dfn u = !(Constant14.numeral 0) ∧
      y = !Constant14.integerZero) ∨
    (!SetTheory.kpair.π₁.dfn u = !(Constant14.numeral 0) ∧
      ∃ m ∈ !SetTheory.isω,
        !SetTheory.kpair.π₂.dfn u = !SetTheory.succ.dfn m ∧
        y = !SetTheory.kpair.dfn (!(Constant14.numeral 1)) m) ∨
    (!SetTheory.kpair.π₁.dfn u = !(Constant14.numeral 1) ∧
      y = !SetTheory.kpair.dfn (!(Constant14.numeral 0))
        (!SetTheory.succ.dfn (!SetTheory.kpair.π₂.dfn u)))”

lemma ev_intNegFormula (y u : M0.V) :
    mEv M0 ![y, u] intNegFormula ↔
      (pi1V M0 u = vnNatV M0 0 ∧ pi2V M0 u = vnNatV M0 0 ∧ y = encodeIntV M0 0) ∨
      (pi1V M0 u = vnNatV M0 0 ∧
        ∃ m : M0.V, M0.mem m (vnOmegaV M0) ∧ pi2V M0 u = insertV M0 m m ∧
          y = kpairV M0 (vnNatV M0 1) m) ∨
      (pi1V M0 u = vnNatV M0 1 ∧
        y = kpairV M0 (vnNatV M0 0) (insertV M0 (pi2V M0 u) (pi2V M0 u))) := by
  unfold intNegFormula
  rw [mEv_or, mEv_or, mEv_and, mEv_and, mEv_and, mEv_and]
  refine or_congr
    (and_congr
      (ev_faf_eq M0 (et_comp1 M0 (ev_pi1 M0) (et_bvar2 M0 y u _)) (et_const0 M0 (dc_numeral M0 0) _))
      (and_congr
        (ev_faf_eq M0 (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 y u _)) (et_const0 M0 (dc_numeral M0 0) _))
        (ev_faf_eq M0 (et_bvar1 M0 y _) (et_const0 M0 (dc_integerZero M0) _))))
    (or_congr
      (and_congr
        (ev_faf_eq M0 (et_comp1 M0 (ev_pi1 M0) (et_bvar2 M0 y u _)) (et_const0 M0 (dc_numeral M0 0) _))
        ?_)
      (and_congr
        (ev_faf_eq M0 (et_comp1 M0 (ev_pi1 M0) (et_bvar2 M0 y u _)) (et_const0 M0 (dc_numeral M0 1) _))
        (ev_faf_eq M0 (et_bvar1 M0 y _)
          (et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_numeral M0 0) _)
            (et_comp1 M0 (ev_succ M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar3 M0 _ y u _)))))))
  rw [ev_faf_bexs M0 (et_const0 M0 (dc_isω M0) _)]
  refine exists_congr fun m => and_congr_right fun _ => ?_
  rw [mEv_and]
  exact and_congr
    (ev_faf_eq M0 (et_comp1 M0 (ev_pi2 M0) (et_bvar4 M0 m (vnOmegaV M0) y u _))
      (et_comp1 M0 (ev_succ M0) (et_bvar2 M0 _ m _)))
    (ev_faf_eq M0 (et_bvar3 M0 m (vnOmegaV M0) y _)
      (et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_numeral M0 1) _) (et_bvar2 M0 _ m _)))

lemma exists_intNegV {u : M0.V} (hu : M0.mem u (intSetV M0)) :
    ∃ y : M0.V, M0.mem y (intSetV M0) ∧ ∀ w : M0.V, mEv M0 ![w, u] intNegFormula ↔ w = y := by
  obtain ⟨a, ha, r, hr, rfl⟩ := (mem_prodV M0).mp hu
  obtain ⟨s, hs, rfl⟩ := (mem_vnNatV_iff M0).mp ha
  have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
  interval_cases s
  · rcases vnOmegaV_zero_or_succ M0 hr with rfl | ⟨m, hm, rfl⟩
    · refine ⟨encodeIntV M0 0, encodeIntV_mem M0 0, fun w => ?_⟩
      rw [ev_intNegFormula, pi1V_kpairV, pi2V_kpairV]
      have hno : ¬ ∃ m : M0.V, M0.mem m (vnOmegaV M0) ∧
          emptyV M0 = insertV M0 m m ∧ w = kpairV M0 (vnNatV M0 1) m := by
        rintro ⟨m, _, hm, _⟩
        exact not_mem_emptyV M0 m (hm ▸ (mem_insertV M0).mpr (Or.inl rfl))
      have h0eq : (emptyV M0 = vnNatV M0 0) ↔ True := iff_true_intro rfl
      simp only [eq_false h01, h0eq, false_and, true_and, hno, or_false]
    · refine ⟨kpairV M0 (vnNatV M0 1) m,
        (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 1 < 2), hm⟩, fun w => ?_⟩
      rw [ev_intNegFormula, pi1V_kpairV, pi2V_kpairV]
      have hne0 : insertV M0 m m ≠ vnNatV M0 0 := fun h => by
        change insertV M0 m m = emptyV M0 at h
        exact not_mem_emptyV M0 m (h ▸ (mem_insertV M0).mpr (Or.inl rfl))
      simp only [h01, hne0, false_and, false_or, or_false, true_and]
      constructor
      · rintro ⟨m', _, hsucc, rfl⟩
        have hmm : m = m' := succV_inj M0 hsucc
        subst hmm; rfl
      · rintro rfl
        exact ⟨m, hm, rfl, rfl⟩
  · refine ⟨kpairV M0 (vnNatV M0 0) (insertV M0 r r),
      (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 0 < 2), (vnOmegaV_inductive M0).2 r hr⟩,
      fun w => ?_⟩
    rw [ev_intNegFormula, pi1V_kpairV, pi2V_kpairV]
    simp [h01.symm]

noncomputable def intNegV (u : M0.V) : M0.V :=
  if hu : M0.mem u (intSetV M0) then (exists_intNegV M0 hu).choose else emptyV M0

lemma intNegV_mem {u : M0.V} (hu : M0.mem u (intSetV M0)) :
    M0.mem (intNegV M0 u) (intSetV M0) := by
  unfold intNegV; rw [dif_pos hu]; exact (exists_intNegV M0 hu).choose_spec.1

lemma ev_intNeg_iff {u : M0.V} (hu : M0.mem u (intSetV M0)) (w : M0.V) :
    mEv M0 ![w, u] intNegFormula ↔ w = intNegV M0 u := by
  unfold intNegV; rw [dif_pos hu]; exact (exists_intNegV M0 hu).choose_spec.2 w

lemma intNegV_zero : intNegV M0 (encodeIntV M0 0) = encodeIntV M0 0 := by
  symm
  rw [← ev_intNeg_iff M0 (encodeIntV_mem M0 0), ev_intNegFormula]
  left; simp [encodeIntV, pi1V_kpairV, pi2V_kpairV]

lemma intNegV_invol {u : M0.V} (hu : M0.mem u (intSetV M0)) :
    intNegV M0 (intNegV M0 u) = u := by
  have h1 := (ev_intNeg_iff M0 hu (intNegV M0 u)).mpr rfl
  rw [ev_intNegFormula] at h1
  obtain ⟨a, ha, r, hr, rfl⟩ := (mem_prodV M0).mp hu
  rw [pi1V_kpairV, pi2V_kpairV] at h1
  rcases h1 with ⟨rfl, rfl, heq⟩ | ⟨rfl, m, hm, rfl, heq⟩ | ⟨rfl, heq⟩
  · rw [heq, intNegV_zero]; rfl
  · rw [heq]
    symm
    have hmem : M0.mem (kpairV M0 (vnNatV M0 1) m) (intSetV M0) :=
      (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 1 < 2), hm⟩
    rw [← ev_intNeg_iff M0 hmem, ev_intNegFormula]
    right; right; simp [pi1V_kpairV, pi2V_kpairV]
  · rw [heq]
    symm
    have hmem : M0.mem (kpairV M0 (vnNatV M0 0) (insertV M0 r r)) (intSetV M0) :=
      (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 0 < 2), (vnOmegaV_inductive M0).2 r hr⟩
    rw [← ev_intNeg_iff M0 hmem, ev_intNegFormula]
    right; left
    exact ⟨pi1V_kpairV M0 _ _, r, hr, pi2V_kpairV M0 _ _, rfl⟩

lemma intNegV_intSuccV {u : M0.V} (hu : M0.mem u (intSetV M0)) :
    intNegV M0 (intSuccV M0 u) = intPredV M0 (intNegV M0 u) := by
  have hs := (ev_integerSucc_iff M0 hu (intSuccV M0 u)).mpr rfl
  rw [ev_integerSucc_of_mem M0 hu] at hs
  obtain ⟨a, ha, r, hr, rfl⟩ := (mem_prodV M0).mp hu
  rw [pi1V_kpairV, pi2V_kpairV] at hs
  rcases hs with ⟨rfl, hsu⟩ | ⟨rfl, ⟨rfl, hsu⟩ | ⟨m, hm, rfl, hsu⟩⟩
  · have hneg_s : intNegV M0 (intSuccV M0 (kpairV M0 (vnNatV M0 0) r)) =
        kpairV M0 (vnNatV M0 1) r := by
      rw [hsu]; symm
      have hm' : M0.mem (kpairV M0 (vnNatV M0 0) (insertV M0 r r)) (intSetV M0) :=
        (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 0 < 2), (vnOmegaV_inductive M0).2 r hr⟩
      rw [← ev_intNeg_iff M0 hm', ev_intNegFormula]
      right; left; exact ⟨pi1V_kpairV M0 _ _, r, hr, pi2V_kpairV M0 _ _, rfl⟩
    rw [hneg_s]
    rw [← ev_integerPred_iff M0 (intNegV_mem M0 hu)]
    have hnu := (ev_intNeg_iff M0 hu (intNegV M0 (kpairV M0 (vnNatV M0 0) r))).mpr rfl
    rw [ev_intNegFormula, pi1V_kpairV, pi2V_kpairV] at hnu
    have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
    rcases hnu with ⟨_, rfl, hneq⟩ | ⟨_, m, hm, rfl, hneq⟩ | ⟨h1, _⟩
    · rw [hneq, ev_integerPred_encode]; rfl
    · rw [hneq, ev_integerPred_iff M0
        ((kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 1 < 2), hm⟩)]
      symm
      apply intSuccV_inj M0
        (intPredV_mem M0 ((kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 1 < 2), hm⟩))
        ((kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 1 < 2), (vnOmegaV_inductive M0).2 m hm⟩)
      rw [intSuccV_intPredV M0 ((kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 1 < 2), hm⟩)]
      have hm2 : M0.mem (kpairV M0 (vnNatV M0 1) (insertV M0 m m)) (intSetV M0) :=
        (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 1 < 2), (vnOmegaV_inductive M0).2 m hm⟩
      rw [← ev_integerSucc_iff M0 hm2, ev_integerSucc_of_mem M0 hm2]
      right; exact ⟨pi1V_kpairV M0 _ _, Or.inr ⟨m, hm, pi2V_kpairV M0 _ _, rfl⟩⟩
    · exact (h01 h1).elim
  · rw [hsu, intNegV_zero]
    have hneg_u : intNegV M0 (kpairV M0 (vnNatV M0 1) (vnNatV M0 0)) = encodeIntV M0 1 := by
      symm; rw [← ev_intNeg_iff M0 hu, ev_intNegFormula]
      right; right; simp [encodeIntV, vnNatV, pi1V_kpairV, pi2V_kpairV]
    rw [hneg_u]
    rw [← ev_integerPred_iff M0 (encodeIntV_mem M0 1), ev_integerPred_encode]
    rfl
  · have hneg_s : intNegV M0 (intSuccV M0 (kpairV M0 (vnNatV M0 1) (insertV M0 m m))) =
        kpairV M0 (vnNatV M0 0) (insertV M0 m m) := by
      rw [hsu]; symm
      have hm1 : M0.mem (kpairV M0 (vnNatV M0 1) m) (intSetV M0) :=
        (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 1 < 2), hm⟩
      rw [← ev_intNeg_iff M0 hm1, ev_intNegFormula]
      right; right; simp [pi1V_kpairV, pi2V_kpairV]
    have hneg_u : intNegV M0 (kpairV M0 (vnNatV M0 1) (insertV M0 m m)) =
        kpairV M0 (vnNatV M0 0) (insertV M0 (insertV M0 m m) (insertV M0 m m)) := by
      symm; rw [← ev_intNeg_iff M0 hu, ev_intNegFormula]
      right; right; simp [pi1V_kpairV, pi2V_kpairV]
    rw [hneg_s, hneg_u]
    have hm1 : M0.mem (kpairV M0 (vnNatV M0 0) (insertV M0 m m)) (intSetV M0) :=
      (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 0 < 2), (vnOmegaV_inductive M0).2 m hm⟩
    have hm2 : M0.mem (kpairV M0 (vnNatV M0 0) (insertV M0 (insertV M0 m m) (insertV M0 m m))) (intSetV M0) :=
      (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 0 < 2),
        (vnOmegaV_inductive M0).2 _ ((vnOmegaV_inductive M0).2 m hm)⟩
    apply intSuccV_inj M0 hm1 (intPredV_mem M0 hm2)
    rw [intSuccV_intPredV M0 hm2]
    symm
    rw [← ev_integerSucc_iff M0 hm1, ev_integerSucc_of_mem M0 hm1]
    left; simp [pi1V_kpairV, pi2V_kpairV]

lemma intNegV_intPredV {u : M0.V} (hu : M0.mem u (intSetV M0)) :
    intNegV M0 (intPredV M0 u) = intSuccV M0 (intNegV M0 u) := by
  have h1 := intNegV_intSuccV M0 (intPredV_mem M0 hu)
  rw [intSuccV_intPredV M0 hu] at h1
  have h2 := congrArg (intSuccV M0) h1
  rw [intSuccV_intPredV M0 (intNegV_mem M0 (intPredV_mem M0 hu))] at h2
  exact h2.symm

lemma exists_flipTapeV (g : M0.V) :
    ∃ g' : M0.V, ∀ p : M0.V, M0.mem p g' ↔
      M0.mem p (prodV M0 (intSetV M0) (vnNatV M0 2)) ∧
      ∃ u : M0.V, M0.mem u (intSetV M0) ∧
        ∃ v : M0.V, M0.mem v (vnNatV M0 2) ∧
          p = kpairV M0 u v ∧ M0.mem (kpairV M0 (intNegV M0 u) v) g := by
  let ambient := prodV M0 (intSetV M0) (vnNatV M0 2)
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.bexsMem (&1)
      (Semiformula.bexsMem (&2)
        ((Rew.subst ![#2, #1, #0] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋏
          (∃¹ ((Rew.subst ![#0, #2] ▹ Rewriting.emb intNegFormula) ⋏
            (∃¹ ((Rew.subst ![#0, #1, #2] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋏
              Semiformula.rel Language.Set.Rel.mem ![#0, &0]))))))
  let ε : ℕ → M0.V := fun k => if k = 0 then g else if k = 1 then intSetV M0 else vnNatV M0 2
  obtain ⟨g', hg'⟩ := sepV M0 ambient φ ε
  refine ⟨g', fun p => ?_⟩
  rw [hg' p]
  refine and_congr Iff.rfl ?_
  dsimp only [φ]
  rw [evalM_bexsMem]
  refine exists_congr fun u => and_congr_right fun hu => ?_
  rw [evalM_bexsMem]
  refine exists_congr fun v => and_congr Iff.rfl ?_
  rw [evalM_and]
  refine and_congr ?_ ?_
  · change evalM M0.mem (v :> u :> p :> ![]) ε
      ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#2, #1, #0]) ↔ _
    rw [evalM_subst, evalM_emb]
    refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).trans (ev_kpair M0 p u v)
    funext i; fin_cases i <;> rfl
  · rw [evalM_exs]
    constructor
    · rintro ⟨u', hu', q, hq, hqmem⟩
      change evalM M0.mem (u' :> v :> u :> p :> ![]) ε
        ((Rewriting.emb intNegFormula) ⇜ ![#0, #2]) at hu'
      rw [evalM_subst, evalM_emb] at hu'
      have hu'_eq : u' = intNegV M0 u := (ev_intNeg_iff M0 hu u').mp (by
        refine (evalRaw_congr Eq M0.mem intNegFormula ?_ rfl).mp hu'
        funext i; fin_cases i <;> rfl)
      subst hu'_eq
      change evalM M0.mem (q :> intNegV M0 u :> v :> u :> p :> ![]) ε
        ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #1, #2]) at hq
      rw [evalM_subst, evalM_emb] at hq
      have hq_eq : q = kpairV M0 (intNegV M0 u) v := (ev_kpair M0 q _ v).mp (by
        refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mp hq
        funext i; fin_cases i <;> rfl)
      subst hq_eq
      exact hqmem
    · intro hmem
      refine ⟨intNegV M0 u, ?_, kpairV M0 (intNegV M0 u) v, ?_, hmem⟩
      · change evalM M0.mem (intNegV M0 u :> v :> u :> p :> ![]) ε
          ((Rewriting.emb intNegFormula) ⇜ ![#0, #2])
        rw [evalM_subst, evalM_emb]
        refine (evalRaw_congr Eq M0.mem intNegFormula ?_ rfl).mpr ((ev_intNeg_iff M0 hu _).mpr rfl)
        funext i; fin_cases i <;> rfl
      · change evalM M0.mem (kpairV M0 (intNegV M0 u) v :> intNegV M0 u :> v :> u :> p :> ![]) ε
          ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #1, #2])
        rw [evalM_subst, evalM_emb]
        refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mpr
          ((ev_kpair M0 (kpairV M0 (intNegV M0 u) v) (intNegV M0 u) v).mpr rfl)
        funext i; fin_cases i <;> rfl

noncomputable def flipTapeV (g : M0.V) : M0.V := (exists_flipTapeV M0 g).choose

lemma mem_flipTapeV {g p : M0.V} :
    M0.mem p (flipTapeV M0 g) ↔
      M0.mem p (prodV M0 (intSetV M0) (vnNatV M0 2)) ∧
      ∃ u : M0.V, M0.mem u (intSetV M0) ∧
        ∃ v : M0.V, M0.mem v (vnNatV M0 2) ∧
          p = kpairV M0 u v ∧ M0.mem (kpairV M0 (intNegV M0 u) v) g :=
  (exists_flipTapeV M0 g).choose_spec p

lemma flipTapeV_mem_funs {g : M0.V} (hg : M0.mem g (funsV M0 (intSetV M0) (vnNatV M0 2))) :
    M0.mem (flipTapeV M0 g) (funsV M0 (intSetV M0) (vnNatV M0 2)) := by
  obtain ⟨hsub, huniq⟩ := (mem_funsV M0).mp hg
  rw [mem_funsV]
  refine ⟨fun p hp => ((mem_flipTapeV M0).mp hp).1, fun u hu => ?_⟩
  obtain ⟨v, hv, hvuniq⟩ := huniq (intNegV M0 u) (intNegV_mem M0 hu)
  have hv2 : M0.mem v (vnNatV M0 2) := ((kpairV_mem_prodV M0).mp (hsub _ hv)).2
  refine ⟨v, (mem_flipTapeV M0).mpr ⟨(kpairV_mem_prodV M0).mpr ⟨hu, hv2⟩, u, hu, v, hv2, rfl, hv⟩, ?_⟩
  intro y hy
  obtain ⟨_, u', _, v', _, heq, hmem⟩ := (mem_flipTapeV M0).mp hy
  obtain ⟨rfl, rfl⟩ := kpairV_inj M0 heq
  exact hvuniq y hmem

lemma flipTapeV_app {g u : M0.V} (hg : M0.mem g (funsV M0 (intSetV M0) (vnNatV M0 2)))
    (hu : M0.mem u (intSetV M0)) :
    zfcAppV M0 (flipTapeV M0 g) u = zfcAppV M0 g (intNegV M0 u) := by
  obtain ⟨hsub, huniq⟩ := (mem_funsV M0).mp hg
  obtain ⟨v, hv, _⟩ := huniq (intNegV M0 u) (intNegV_mem M0 hu)
  have hv2 : M0.mem v (vnNatV M0 2) := ((kpairV_mem_prodV M0).mp (hsub _ hv)).2
  rw [zfcAppV_of_mem_funs M0 hg (intNegV_mem M0 hu) hv]
  exact zfcAppV_of_mem_funs M0 (flipTapeV_mem_funs M0 hg) hu
    ((mem_flipTapeV M0).mpr ⟨(kpairV_mem_prodV M0).mpr ⟨hu, hv2⟩, u, hu, v, hv2, rfl, hv⟩)

/- Total `nextStepV` on ALL of `cfgSetV M0 (n + 1)` and `not_halts_of_invariant` -/

lemma ev_nextConfig_total {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (qCode : ℕ) (hq : qCode < n + 1) (pos g : M0.V)
    (hpos : M0.mem pos (intSetV M0)) (hg : M0.mem g (funsV M0 (intSetV M0) (vnNatV M0 2)))
    (symCode : ℕ) (hs : symCode < 2) (hsym : zfcAppV M0 g pos = vnNatV M0 symCode)
    (z' : M0.V) :
    let z0 := kpairV M0 (vnNatV M0 qCode) (kpairV M0 pos g)
    let o := transLookup M qCode symCode
    let pos' := if o.2.2 = 0 then intPredV M0 pos else if o.2.2 = 1 then pos else intSuccV M0 pos
    let g' := updateTapeV M0 g pos (vnNatV M0 o.2.1)
    mEv M0 ![z', z0] (Constant14.nextConfig (n + 1) (Constant14.instructionTable M)) ↔
      z' = kpairV M0 (vnNatV M0 o.1) (kpairV M0 pos' g') := by
  intro z0 o pos' g'
  have hob : o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
    dsimp only [o, transLookup]
    by_cases hqn : qCode < n
    · rw [dif_pos hqn, dif_pos hs]
      exact transitionCode_bounds M ⟨qCode, hqn⟩ ⟨symCode, hs⟩
    · rw [dif_neg hqn]; dsimp only; exact ⟨Nat.lt_succ_self n, hs, by decide⟩
  have hz0 : M0.mem z0 (cfgSetV M0 (n + 1)) :=
    (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 hq, (kpairV_mem_prodV M0).mpr ⟨hpos, hg⟩⟩
  have hpos' : M0.mem pos' (intSetV M0) := by
    dsimp only [pos']; split_ifs
    · exact intPredV_mem M0 hpos
    · exact hpos
    · exact intSuccV_mem M0 hpos
  have hg' : M0.mem g' (funsV M0 (intSetV M0) (vnNatV M0 2)) :=
    updateTapeV_mem_funs M0 hg hpos (vnNatV_lt_mem M0 hob.2.1)
  have hz1 : M0.mem (kpairV M0 (vnNatV M0 o.1) (kpairV M0 pos' g')) (cfgSetV M0 (n + 1)) :=
    (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 hob.1, (kpairV_mem_prodV M0).mpr ⟨hpos', hg'⟩⟩
  let tVal := kpairV M0 (vnNatV M0 o.1) (kpairV M0 (vnNatV M0 o.2.1) (vnNatV M0 o.2.2))
  have htVal_eq : zfcAppV M0 (instrTableV M0 M)
      (kpairV M0 (pi1V M0 z0) (zfcAppV M0 (pi2V M0 (pi2V M0 z0)) (pi1V M0 (pi2V M0 z0)))) = tVal := by
    dsimp only [z0, tVal]
    rw [pi1V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, hsym]
    exact instrTableV_app M0 M qCode symCode hq hs
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
      dsimp only [z0, tVal] at hq_eq hdir hwr hrest
      rw [pi1V_kpairV, pi1V_kpairV] at hq_eq
      rw [pi2V_kpairV, pi2V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV] at hdir
      rw [pi2V_kpairV, pi2V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV] at hwr
      simp only [pi2V_kpairV, pi1V_kpairV] at hrest
      rw [hq_eq]
      congr 1; congr 1
      · have hd2 := hob.2.2
        interval_cases hdv : o.2.2
        · have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          have h02 : vnNatV M0 0 ≠ vnNatV M0 2 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          simp only [true_and, h01, h02, false_and, or_false] at hdir
          rw [ev_integerPred_iff M0 hpos] at hdir
          simpa [pos', hdv] using hdir
        · have h10 : vnNatV M0 1 ≠ vnNatV M0 0 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          have h12 : vnNatV M0 1 ≠ vnNatV M0 2 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          simp only [true_and, h10, h12, false_and, false_or, or_false] at hdir
          simpa [pos', hdv] using hdir
        · have h20 : vnNatV M0 2 ≠ vnNatV M0 0 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          have h21 : vnNatV M0 2 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          simp only [true_and, h20, h21, false_and, false_or] at hdir
          rw [ev_integerSucc_iff M0 hpos] at hdir
          simpa [pos', hdv] using hdir
      · refine funsV_ext M0 hg2 hg' fun u hu => ?_
        rw [updateTapeV_app M0 hg hpos (vnNatV_lt_mem M0 hob.2.1) hu]
        by_cases hup : u = pos
        · subst hup; rw [if_pos rfl, hwr]
        · rw [if_neg hup, hrest u hu hup]
    · rintro rfl
      refine ⟨hz1, tVal, rfl, ?_, ?_, ?_, ?_⟩
      · dsimp only [tVal]; rw [pi1V_kpairV, pi1V_kpairV]
      · dsimp only [z0, tVal]
        rw [pi2V_kpairV, pi2V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV]
        have hd2 := hob.2.2
        interval_cases hdv : o.2.2
        · left; refine ⟨rfl, ?_⟩
          rw [ev_integerPred_iff M0 hpos]; simp [pos', hdv]
        · right; left; refine ⟨rfl, ?_⟩
          simp [pos', hdv]
        · right; right; refine ⟨rfl, ?_⟩
          rw [ev_integerSucc_iff M0 hpos]; simp [pos', hdv]
      · dsimp only [z0, tVal]
        rw [pi2V_kpairV, pi2V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV]
        rw [updateTapeV_app M0 hg hpos (vnNatV_lt_mem M0 hob.2.1) hpos, if_pos rfl]
      · intro u hu hne
        dsimp only [z0] at hne ⊢
        rw [pi2V_kpairV, pi1V_kpairV] at hne
        simp only [pi2V_kpairV]
        rw [updateTapeV_app M0 hg hpos (vnNatV_lt_mem M0 hob.2.1) hu, if_neg hne]

lemma nextStepV_mem_funs {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    M0.mem (nextStepV M0 M) (funsV M0 (cfgSetV M0 (n + 1)) (cfgSetV M0 (n + 1))) := by
  rw [mem_funsV]
  refine ⟨?_, ?_⟩
  · intro e he
    obtain ⟨z, hz, z', hz', rfl, _⟩ := (mem_nextStepV M0 M).mp he
    exact (kpairV_mem_prodV M0).mpr ⟨hz, hz'⟩
  · intro z hz
    obtain ⟨s, hs, p_tail, hp_tail, rfl⟩ := (mem_prodV M0).mp hz
    obtain ⟨qCode, hq, rfl⟩ := (mem_vnNatV_iff M0).mp hs
    obtain ⟨pos, hpos, g, hg, rfl⟩ := (mem_prodV M0).mp hp_tail
    obtain ⟨symCode, hsym_lt, hsym⟩ := (mem_vnNatV_iff M0).mp (zfcAppV_mem_codomain M0 hg hpos)
    let o := transLookup M qCode symCode
    have hob : o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
      dsimp only [o, transLookup]
      by_cases hqn : qCode < n
      · rw [dif_pos hqn, dif_pos hsym_lt]
        exact transitionCode_bounds M ⟨qCode, hqn⟩ ⟨symCode, hsym_lt⟩
      · rw [dif_neg hqn]; dsimp only; exact ⟨Nat.lt_succ_self n, hsym_lt, by decide⟩
    let pos' := if o.2.2 = 0 then intPredV M0 pos else if o.2.2 = 1 then pos else intSuccV M0 pos
    let g' := updateTapeV M0 g pos (vnNatV M0 o.2.1)
    let z' := kpairV M0 (vnNatV M0 o.1) (kpairV M0 pos' g')
    have hz' : M0.mem z' (cfgSetV M0 (n + 1)) := by
      refine (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 hob.1, (kpairV_mem_prodV M0).mpr ⟨?_, ?_⟩⟩
      · dsimp only [pos']; split_ifs
        · exact intPredV_mem M0 hpos
        · exact hpos
        · exact intSuccV_mem M0 hpos
      · exact updateTapeV_mem_funs M0 hg hpos (vnNatV_lt_mem M0 hob.2.1)
    refine ⟨z', ?_, ?_⟩
    · exact (mem_nextStepV M0 M).mpr ⟨_, hz, z', hz', rfl,
        (ev_nextConfig_total M0 M qCode hq pos g hpos hg symCode hsym_lt hsym z').mpr rfl⟩
    · intro y hy
      obtain ⟨z1, _, z2, _, heq, hnc⟩ := (mem_nextStepV M0 M).mp hy
      obtain ⟨rfl, rfl⟩ := kpairV_inj M0 heq
      exact (ev_nextConfig_total M0 M qCode hq pos g hpos hg symCode hsym_lt hsym y).mp hnc

lemma zfcAppV_nextStepV_cfg {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (qCode : ℕ) (hq : qCode < n + 1) (pos g : M0.V)
    (hpos : M0.mem pos (intSetV M0)) (hg : M0.mem g (funsV M0 (intSetV M0) (vnNatV M0 2)))
    (symCode : ℕ) (hs : symCode < 2) (hsym : zfcAppV M0 g pos = vnNatV M0 symCode) :
    let o := transLookup M qCode symCode
    let pos' := if o.2.2 = 0 then intPredV M0 pos else if o.2.2 = 1 then pos else intSuccV M0 pos
    zfcAppV M0 (nextStepV M0 M) (kpairV M0 (vnNatV M0 qCode) (kpairV M0 pos g)) =
      kpairV M0 (vnNatV M0 o.1) (kpairV M0 pos' (updateTapeV M0 g pos (vnNatV M0 o.2.1))) := by
  intro o pos'
  apply zfcAppV_of_unique M0
  intro y
  rw [mem_nextStepV]
  constructor
  · rintro ⟨z, _, z', _, heq, hnc⟩
    obtain ⟨rfl, rfl⟩ := kpairV_inj M0 heq
    exact (ev_nextConfig_total M0 M qCode hq pos g hpos hg symCode hs hsym y).mp hnc
  · rintro rfl
    have hob : o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
      dsimp only [o, transLookup]
      by_cases hqn : qCode < n
      · rw [dif_pos hqn, dif_pos hs]
        exact transitionCode_bounds M ⟨qCode, hqn⟩ ⟨symCode, hs⟩
      · rw [dif_neg hqn]; dsimp only; exact ⟨Nat.lt_succ_self n, hs, by decide⟩
    have hz0 : M0.mem (kpairV M0 (vnNatV M0 qCode) (kpairV M0 pos g)) (cfgSetV M0 (n + 1)) :=
      (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 hq, (kpairV_mem_prodV M0).mpr ⟨hpos, hg⟩⟩
    have hz1 : M0.mem (kpairV M0 (vnNatV M0 o.1) (kpairV M0 pos' (updateTapeV M0 g pos (vnNatV M0 o.2.1))))
        (cfgSetV M0 (n + 1)) := by
      refine (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 hob.1, (kpairV_mem_prodV M0).mpr ⟨?_, ?_⟩⟩
      · dsimp only [pos']; split_ifs
        · exact intPredV_mem M0 hpos
        · exact hpos
        · exact intSuccV_mem M0 hpos
      · exact updateTapeV_mem_funs M0 hg hpos (vnNatV_lt_mem M0 hob.2.1)
    exact ⟨_, hz0, _, hz1, rfl,
      (ev_nextConfig_total M0 M qCode hq pos g hpos hg symCode hs hsym _).mpr rfl⟩

lemma ev_IsFunction (f : M0.V) :
    mEv M0 ![f] SetTheory.IsFunction.dfn ↔ ∃ X Y : M0.V, M0.mem f (funsV M0 X Y) := by
  unfold SetTheory.IsFunction.dfn
  change mEv M0 ![f] (∃¹ ∃¹ _) ↔ _
  rw [mEv_exs]
  refine exists_congr fun X => ?_
  rw [mEv_exs]
  refine exists_congr fun Y => ?_
  exact ev_faf_mem M0 (et_bvar3 M0 Y X f _)
    (et_comp2 M0 (ev_function M0) (et_bvar2 M0 _ Y _) (et_bvar3 M0 _ Y X _))

def HasNonHaltingInvariant {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : Prop :=
  ∃ A : M0.V,
    M0.mem (simCfgV M0 M 0) A ∧
    (∀ y : M0.V, M0.mem y A → M0.mem (zfcAppV M0 (nextStepV M0 M) y) A) ∧
    (∀ y : M0.V, M0.mem y A → pi1V M0 y ≠ vnNatV M0 n)

lemma not_halts_of_invariant {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (hInv : HasNonHaltingInvariant M0 M) :
    ¬ evalM M0.mem Fin.elim0 Empty.elim (Constant14.halts M) := by
  obtain ⟨A, hA0, hAstep, hAnohalt⟩ := hInv
  let Fstep := nextStepV M0 M
  let x0 := simCfgV M0 M 0
  -- Construct `O` by separation on `A`
  let φO : SetTheorySemiproposition 1 :=
    ∀¹ ((Semiformula.rel Language.Set.Rel.mem ![&1, #0] ⋏
         Semiformula.ballMem (#0)
           (∃¹ ((Rew.subst ![#0, &0, #1] ▹ Rewriting.emb SetTheory.value.dfn) ⋏
             Semiformula.rel Language.Set.Rel.mem ![#0, #2]))) 🡒
        Semiformula.rel Language.Set.Rel.mem ![#1, #0])
  let ε : ℕ → M0.V := fun k => if k = 0 then Fstep else x0
  obtain ⟨O, hO⟩ := sepV M0 A φO ε
  have hO_iff : ∀ z : M0.V, M0.mem z O ↔
      ∀ B : M0.V, (M0.mem x0 B ∧ ∀ y : M0.V, M0.mem y B → M0.mem (zfcAppV M0 Fstep y) B) →
        M0.mem z B := by
    intro z
    rw [hO z]
    have hφ : evalM M0.mem ![z] ε φO ↔
        ∀ B : M0.V, (M0.mem x0 B ∧ ∀ y : M0.V, M0.mem y B → M0.mem (zfcAppV M0 Fstep y) B) →
          M0.mem z B := by
      dsimp only [φO]
      rw [evalM_all]
      refine forall_congr' fun B => ?_
      rw [evalM_imp, evalM_and, evalM_ballMem]
      refine imp_congr (and_congr Iff.rfl (forall₂_congr fun y _ => ?_)) Iff.rfl
      rw [evalM_exs]
      constructor
      · rintro ⟨v, hv1, hv2⟩
        change evalM M0.mem (v :> y :> B :> z :> ![]) ε
          ((Rewriting.emb SetTheory.value.dfn) ⇜ ![#0, &0, #1]) at hv1
        rw [evalM_subst, evalM_emb] at hv1
        have hveq : v = zfcAppV M0 Fstep y := (ev_value M0 v Fstep y).mp (by
          refine (evalRaw_congr Eq M0.mem SetTheory.value.dfn ?_ rfl).mp hv1
          funext i; fin_cases i <;> rfl)
        rwa [hveq] at hv2
      · intro hmem
        refine ⟨zfcAppV M0 Fstep y, ?_, hmem⟩
        change evalM M0.mem (zfcAppV M0 Fstep y :> y :> B :> z :> ![]) ε
          ((Rewriting.emb SetTheory.value.dfn) ⇜ ![#0, &0, #1])
        rw [evalM_subst, evalM_emb]
        refine (evalRaw_congr Eq M0.mem SetTheory.value.dfn ?_ rfl).mpr ((ev_value M0 _ Fstep y).mpr rfl)
        funext i; fin_cases i <;> rfl
    rw [hφ]
    exact ⟨And.right, fun hall => ⟨hall A ⟨hA0, hAstep⟩, hall⟩⟩
  have hO_orbit : mEv M0 ![O, Fstep, x0] Constant14.orbit := by
    unfold Constant14.orbit
    rw [mEv_and]
    refine ⟨?_, ?_⟩
    · rw [ev_nest1 M0 SetTheory.IsFunction.dfn (et_bvar2 M0 O Fstep _), ev_IsFunction]
      exact ⟨cfgSetV M0 (n + 1), cfgSetV M0 (n + 1), nextStepV_mem_funs M0 M⟩
    · rw [mEv_all]
      intro z
      rw [mEv_iff, ev_faf_mem M0 (et_bvar1 M0 z _) (et_bvar3 M0 _ z O _), mEv_all, hO_iff z]
      refine forall_congr' fun B => ?_
      rw [mEv_imp, mEv_and]
      refine imp_congr (and_congr ?_ ?_) (ev_faf_mem M0 (et_bvar2 M0 B z _) (et_bvar2 M0 _ B _)).symm
      · exact (ev_faf_mem M0 (et_bvar5 M0 B z O Fstep x0 _) (et_bvar2 M0 _ B _)).symm
      · rw [ev_faf_ball M0 (et_bvar1 M0 B _)]
        refine forall₂_congr fun y _ => ?_
        exact (ev_faf_mem M0
          (et_comp2 M0 (ev_value M0) (et_bvar6 M0 y B B z O Fstep _) (et_bvar1 M0 y _))
          (et_bvar4 M0 _ y B B _)).symm
  intro hhalts
  change mEv M0 (Fin.elim0 : Fin 0 → M0.V) (Constant14.halts M) at hhalts
  rw [mEv_e0 M0 (Fin.elim0 : Fin 0 → M0.V) ![]] at hhalts
  unfold Constant14.halts at hhalts
  rw [ev_faf_bexs M0 (et_const0 M0 (dc_integers M0) ![])] at hhalts
  obtain ⟨m, _, hm_body⟩ := hhalts
  rw [ev_faf_bexs M0
    (et_comp2 M0 (ev_function M0) (et_const0 M0 (dc_numeral M0 2) _) (et_const0 M0 (dc_integers M0) _))] at hm_body
  obtain ⟨g, _, hg_body⟩ := hm_body
  let target := kpairV M0 (vnNatV M0 n) (kpairV M0 m g)
  have htarget : EvalTermAt M0 (g :> funsV M0 (intSetV M0) (vnNatV M0 2) :> m :> intSetV M0 :> ![])
      (Semiformula.nestFormulaeFunc SetTheory.kpair.dfn
        (Semiformula.nestFormulaeFunc (Constant14.numeral n) ![] :>
          Semiformula.nestFormulaeFunc SetTheory.kpair.dfn
            (op(=).operator (#0 :> #3 :> ![]) :> op(=).operator (#0 :> #1 :> ![]) :> ![]) :> ![]))
      target :=
    et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_numeral M0 n) _)
      (et_comp2 M0 (ev_kpair M0) (et_bvar3 M0 g _ m _) (et_bvar1 M0 g _))
  rw [mEv_all] at hg_body
  have hv1 := (mEv_imp M0 _ _ _).mp (hg_body target) ((htarget target).mpr rfl)
  rw [mEv_all] at hv1
  have hO_nest : mEv M0 (O :> target :> g :> funsV M0 (intSetV M0) (vnNatV M0 2) :> m :> intSetV M0 :> ![])
      (Semiformula.nestFormulaeFunc Constant14.orbit
        (Semiformula.nestFormulaeFunc (Constant14.nextStep (n + 1) (Constant14.instructionTable M)) ![] :>
          Semiformula.nestFormulaeFunc Constant14.initialConfig ![] :> ![])) := by
    rw [ev_nestFunc2_raw M0 Constant14.orbit
      (et_const0 M0 (dc_nextStep M0 M) _) (et_const0 M0 (dc_initialConfig M0 M) _) O]
    exact hO_orbit
  have hmem_O : M0.mem target O := (mEv_imp M0 _ _ _).mp (hv1 O) hO_nest
  have hmem_A : M0.mem target A := ((hO target).mp hmem_O).1
  exact hAnohalt target hmem_A (pi1V_kpairV M0 _ _)

end ModelBridge

end C14H2


namespace C14H2

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver C14Completeness C14Stage2 BeaverBound
open scoped Classical

/- ## Part 5: Formula Helpers and the 4 `BeaverBound` ZFC-Invariant Bridges -/

def bvarEqNum {m : ℕ} (qIdx : Fin m) (k : ℕ) : SetTheorySemiproposition m :=
  Rew.subst ![#qIdx] ▹ Rewriting.emb (Constant14.numeral k)

def appEqNum {m : ℕ} (fIdx uIdx : Fin m) (k : ℕ) : SetTheorySemiproposition m :=
  ∃¹ ((Rew.subst ![#0] ▹ Rewriting.emb (Constant14.numeral k)) ⋏
      (Rew.subst ![#0, #(fIdx.succ), #(uIdx.succ)] ▹ Rewriting.emb SetTheory.value.dfn))

def numMemApp {m : ℕ} (fIdx uIdx : Fin m) (k : ℕ) : SetTheorySemiproposition m :=
  ∃¹ ((Rew.subst ![#0] ▹ Rewriting.emb (Constant14.numeral k)) ⋏
      (∃¹ ((Rew.subst ![#0, #(fIdx.succ.succ), #(uIdx.succ.succ)] ▹ Rewriting.emb SetTheory.value.dfn) ⋏
           Semiformula.rel Language.Set.Rel.mem ![#1, #0])))

section Bridges

variable (M0 : ZFCModel)

lemma evalM_bvarEqNum {m : ℕ} (e : Fin m → M0.V) (ε : ℕ → M0.V) (qIdx : Fin m) (k : ℕ) :
    evalM M0.mem e ε (bvarEqNum qIdx k) ↔ e qIdx = vnNatV M0 k := by
  change evalM M0.mem e ε ((Rewriting.emb (Constant14.numeral k)) ⇜ ![#qIdx]) ↔ _
  rw [evalM_subst, evalM_emb]
  refine (evalRaw_congr Eq M0.mem (Constant14.numeral k) ?_ rfl).trans (dc_numeral M0 k (e qIdx))
  funext i; fin_cases i; rfl

lemma evalM_appEqNum {m : ℕ} (e : Fin m → M0.V) (ε : ℕ → M0.V) (fIdx uIdx : Fin m) (k : ℕ) :
    evalM M0.mem e ε (appEqNum fIdx uIdx k) ↔ zfcAppV M0 (e fIdx) (e uIdx) = vnNatV M0 k := by
  unfold appEqNum
  rw [evalM_exs]
  constructor
  · rintro ⟨v, hv1, hv2⟩
    change evalM M0.mem (v :> e) ε ((Rewriting.emb (Constant14.numeral k)) ⇜ ![#0]) at hv1
    rw [evalM_subst, evalM_emb] at hv1
    have hvk : v = vnNatV M0 k := (dc_numeral M0 k v).mp (by
      refine (evalRaw_congr Eq M0.mem (Constant14.numeral k) ?_ rfl).mp hv1
      funext i; fin_cases i; rfl)
    change evalM M0.mem (v :> e) ε
      ((Rewriting.emb SetTheory.value.dfn) ⇜ ![#0, #(fIdx.succ), #(uIdx.succ)]) at hv2
    rw [evalM_subst, evalM_emb] at hv2
    have hva : v = zfcAppV M0 (e fIdx) (e uIdx) := (ev_value M0 v (e fIdx) (e uIdx)).mp (by
      refine (evalRaw_congr Eq M0.mem SetTheory.value.dfn ?_ rfl).mp hv2
      funext i; fin_cases i <;> rfl)
    exact hva.symm.trans hvk
  · intro heq
    refine ⟨vnNatV M0 k, ?_, ?_⟩
    · change evalM M0.mem (vnNatV M0 k :> e) ε ((Rewriting.emb (Constant14.numeral k)) ⇜ ![#0])
      rw [evalM_subst, evalM_emb]
      refine (evalRaw_congr Eq M0.mem (Constant14.numeral k) ?_ rfl).mpr ((dc_numeral M0 k _).mpr rfl)
      funext i; fin_cases i; rfl
    · change evalM M0.mem (vnNatV M0 k :> e) ε
        ((Rewriting.emb SetTheory.value.dfn) ⇜ ![#0, #(fIdx.succ), #(uIdx.succ)])
      rw [evalM_subst, evalM_emb]
      refine (evalRaw_congr Eq M0.mem SetTheory.value.dfn ?_ rfl).mpr
        ((ev_value M0 _ (e fIdx) (e uIdx)).mpr heq.symm)
      funext i; fin_cases i <;> rfl

lemma evalM_numMemApp {m : ℕ} (e : Fin m → M0.V) (ε : ℕ → M0.V) (fIdx uIdx : Fin m) (k : ℕ) :
    evalM M0.mem e ε (numMemApp fIdx uIdx k) ↔
      M0.mem (vnNatV M0 k) (zfcAppV M0 (e fIdx) (e uIdx)) := by
  unfold numMemApp
  rw [evalM_exs]
  constructor
  · rintro ⟨c, hc1, hc2⟩
    change evalM M0.mem (c :> e) ε ((Rewriting.emb (Constant14.numeral k)) ⇜ ![#0]) at hc1
    rw [evalM_subst, evalM_emb] at hc1
    have hck : c = vnNatV M0 k := (dc_numeral M0 k c).mp (by
      refine (evalRaw_congr Eq M0.mem (Constant14.numeral k) ?_ rfl).mp hc1
      funext i; fin_cases i; rfl)
    subst hck
    change evalM M0.mem (vnNatV M0 k :> e) ε _ at hc2
    rw [evalM_exs] at hc2
    rcases hc2 with ⟨val, hval1, hval2⟩
    change evalM M0.mem (val :> vnNatV M0 k :> e) ε
      ((Rewriting.emb SetTheory.value.dfn) ⇜ ![#0, #(fIdx.succ.succ), #(uIdx.succ.succ)]) at hval1
    rw [evalM_subst, evalM_emb] at hval1
    have hva : val = zfcAppV M0 (e fIdx) (e uIdx) := (ev_value M0 val (e fIdx) (e uIdx)).mp (by
      refine (evalRaw_congr Eq M0.mem SetTheory.value.dfn ?_ rfl).mp hval1
      funext i; fin_cases i <;> rfl)
    subst hva
    exact hval2
  · intro hmem
    refine ⟨vnNatV M0 k, ?_, ?_⟩
    · change evalM M0.mem (vnNatV M0 k :> e) ε ((Rewriting.emb (Constant14.numeral k)) ⇜ ![#0])
      rw [evalM_subst, evalM_emb]
      refine (evalRaw_congr Eq M0.mem (Constant14.numeral k) ?_ rfl).mpr ((dc_numeral M0 k _).mpr rfl)
      funext i; fin_cases i; rfl
    · change evalM M0.mem (vnNatV M0 k :> e) ε _
      rw [evalM_exs]
      refine ⟨zfcAppV M0 (e fIdx) (e uIdx), ?_, hmem⟩
      change evalM M0.mem (zfcAppV M0 (e fIdx) (e uIdx) :> vnNatV M0 k :> e) ε
        ((Rewriting.emb SetTheory.value.dfn) ⇜ ![#0, #(fIdx.succ.succ), #(uIdx.succ.succ)])
      rw [evalM_subst, evalM_emb]
      refine (evalRaw_congr Eq M0.mem SetTheory.value.dfn ?_ rfl).mpr
        ((ev_value M0 _ (e fIdx) (e uIdx)).mpr rfl)
      funext i; fin_cases i <;> rfl

lemma evalM_kpair3 {m : ℕ} (e : Fin m → M0.V) (ε : ℕ → M0.V) (zIdx qIdx posIdx gIdx : Fin m) :
    evalM M0.mem e ε
      (∃¹ ((Rew.subst ![#0, #(posIdx.succ), #(gIdx.succ)] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋏
           (Rew.subst ![#(zIdx.succ), #(qIdx.succ), #0] ▹ Rewriting.emb SetTheory.kpair.dfn))) ↔
      e zIdx = kpairV M0 (e qIdx) (kpairV M0 (e posIdx) (e gIdx)) := by
  rw [evalM_exs]
  constructor
  · rintro ⟨pg, h1, h2⟩
    change evalM M0.mem (pg :> e) ε
      ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #(posIdx.succ), #(gIdx.succ)]) at h1
    rw [evalM_subst, evalM_emb] at h1
    have hpg : pg = kpairV M0 (e posIdx) (e gIdx) := (ev_kpair M0 pg (e posIdx) (e gIdx)).mp (by
      refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mp h1
      funext i; fin_cases i <;> rfl)
    subst hpg
    change evalM M0.mem (kpairV M0 (e posIdx) (e gIdx) :> e) ε
      ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#(zIdx.succ), #(qIdx.succ), #0]) at h2
    rw [evalM_subst, evalM_emb] at h2
    exact (ev_kpair M0 (e zIdx) (e qIdx) _).mp (by
      refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mp h2
      funext i; fin_cases i <;> rfl)
  · intro heq
    refine ⟨kpairV M0 (e posIdx) (e gIdx), ?_, ?_⟩
    · change evalM M0.mem (kpairV M0 (e posIdx) (e gIdx) :> e) ε
        ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #(posIdx.succ), #(gIdx.succ)])
      rw [evalM_subst, evalM_emb]
      refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mpr
        ((ev_kpair M0 (kpairV M0 (e posIdx) (e gIdx)) (e posIdx) (e gIdx)).mpr rfl)
      funext i; fin_cases i <;> rfl
    · change evalM M0.mem (kpairV M0 (e posIdx) (e gIdx) :> e) ε
        ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#(zIdx.succ), #(qIdx.succ), #0])
      rw [evalM_subst, evalM_emb]
      refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mpr
        ((ev_kpair M0 (e zIdx) (e qIdx) (kpairV M0 (e posIdx) (e gIdx))).mpr heq)
      funext i; fin_cases i <;> rfl

lemma transLookup_of_ongoing {n : ℕ} [NeZero n] {M : Machine (Fin 2) (Fin n)}
    {q : Fin n} {a : Fin 2} {m : Move n} (h : ongoing M (q, a) = some m) :
    transLookup M q.val a.val = (m.state.val, m.write.val, if m.left then 0 else 2) := by
  have hc := ongoing_command M (q, a) m h
  dsimp only [transLookup, Constant14.transitionCode]
  rw [dif_pos q.isLt, dif_pos a.isLt]
  change (match M q a with
    | some (q', stmt) => (Constant14.stateCode q', stmt.symbol.val, Constant14.directionCode (some stmt.dir))
    | none => (n, a.val, Constant14.directionCode none)) = _
  rw [hc]
  rcases m with ⟨qm, wm, dm⟩
  cases dm <;> rfl

/- Bridge 1: No holes -/

lemma no_holes_invariant {n : ℕ} [NeZero n] {M : MachineOf n} {tb : Program n}
    (hm : Matches M tb) (h0 : (holes tb).card = 0) :
    HasNonHaltingInvariant M0 M := by
  let φ : SetTheorySemiproposition 1 :=
    ∃¹ ((Rew.subst ![#0, #1] ▹ Rewriting.emb SetTheory.kpair.π₁.dfn) ⋏
        Semiformula.rel Language.Set.Rel.mem ![#0, &0])
  obtain ⟨A, hA⟩ := sepV M0 (cfgSetV M0 (n + 1)) φ (fun _ => vnNatV M0 n)
  have hA_iff : ∀ z : M0.V, M0.mem z A ↔
      M0.mem z (cfgSetV M0 (n + 1)) ∧ M0.mem (pi1V M0 z) (vnNatV M0 n) := by
    intro z
    rw [hA z]
    refine and_congr Iff.rfl ?_
    dsimp only [φ]
    rw [evalM_exs]
    constructor
    · rintro ⟨s, hs1, hs2⟩
      change evalM M0.mem (s :> z :> ![]) _
        ((Rewriting.emb SetTheory.kpair.π₁.dfn) ⇜ ![#0, #1]) at hs1
      rw [evalM_subst, evalM_emb] at hs1
      have hseq : s = pi1V M0 z := (ev_pi1 M0 s z).mp (by
        refine (evalRaw_congr Eq M0.mem SetTheory.kpair.π₁.dfn ?_ rfl).mp hs1
        funext i; fin_cases i <;> rfl)
      rwa [hseq] at hs2
    · intro hmem
      refine ⟨pi1V M0 z, ?_, hmem⟩
      change evalM M0.mem (pi1V M0 z :> z :> ![]) _
        ((Rewriting.emb SetTheory.kpair.π₁.dfn) ⇜ ![#0, #1])
      rw [evalM_subst, evalM_emb]
      refine (evalRaw_congr Eq M0.mem SetTheory.kpair.π₁.dfn ?_ rfl).mpr ((ev_pi1 M0 _ z).mpr rfl)
      funext i; fin_cases i <;> rfl
  refine ⟨A, ?_, ?_, ?_⟩
  · rw [hA_iff]
    refine ⟨simCfgV_mem M0 M 0, ?_⟩
    dsimp only [simCfgV, Function.iterate_zero, id_eq, extInit, Constant14.stateCode]
    rw [pi1V_kpairV]
    exact vnNatV_lt_mem M0 (Nat.pos_of_ne_zero (NeZero.ne n))
  · intro y hy
    obtain ⟨hycfg, hypi⟩ := (hA_iff y).mp hy
    obtain ⟨s, _, p_tail, hp_tail, rfl⟩ := (mem_prodV M0).mp hycfg
    obtain ⟨pos, hpos, g, hg, rfl⟩ := (mem_prodV M0).mp hp_tail
    rw [pi1V_kpairV] at hypi
    obtain ⟨qCode, hq, rfl⟩ := (mem_vnNatV_iff M0).mp hypi
    obtain ⟨symCode, hsym_lt, hsym⟩ := (mem_vnNatV_iff M0).mp (zfcAppV_mem_codomain M0 hg hpos)
    have hget_ne : tb.get (⟨qCode, hq⟩, ⟨symCode, hsym_lt⟩) ≠ none := by
      intro hnone
      have hmem : (⟨qCode, hq⟩, ⟨symCode, hsym_lt⟩) ∈ holes tb := by simp [holes, hnone]
      have hpos_card := Finset.card_pos.mpr ⟨_, hmem⟩
      omega
    obtain ⟨m, hm_get⟩ := Option.ne_none_iff_exists'.mp hget_ne
    have hong := hm _ _ hm_get
    have hlu := transLookup_of_ongoing hong
    rw [zfcAppV_nextStepV_cfg M0 M qCode (Nat.lt_succ_of_lt hq) pos g hpos hg symCode hsym_lt hsym]
    rw [hlu, hA_iff]
    refine ⟨?_, ?_⟩
    · refine (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (Nat.lt_succ_of_lt m.state.isLt),
        (kpairV_mem_prodV M0).mpr ⟨?_, updateTapeV_mem_funs M0 hg hpos (vnNatV_lt_mem M0 m.write.isLt)⟩⟩
      cases m.left <;> simp [intPredV_mem M0 hpos, intSuccV_mem M0 hpos]
    · rw [pi1V_kpairV]
      exact vnNatV_lt_mem M0 m.state.isLt
  · intro y hy heq
    have hmem := ((hA_iff y).mp hy).2
    rw [heq] at hmem
    exact irreflV M0 _ hmem

/- Bridge 2: `BeaverBound.Certificate` (non-mirrored) -/

lemma cert_invariant {n : ℕ} [NeZero n] {M : MachineOf n} {tb : Program n} {cert : Certificate n}
    (hm : Matches M tb) (hb : checkBlank cert = true) (hchk : checkMachine tb cert = true) :
    HasNonHaltingInvariant M0 M := by
  let D := cert.dfa
  let W := n * D.size + 1
  let P_W := powersetV M0 (vnNatV M0 W)
  let F_L := funsV M0 (intSetV M0) (vnNatV M0 D.size)
  let F_S := funsV M0 (intSetV M0) P_W
  let F_g := funsV M0 (intSetV M0) (vnNatV M0 2)
  let φLeft : SetTheorySemiproposition 6 :=
    Semiformula.ballMem (&0)
      ((Rew.subst ![#0, #4] ▹ Rewriting.emb intLtFormula) 🡒
        (∀¹ ((Rew.subst ![#0, #1] ▹ Rewriting.emb Constant14.integerSucc.dfn) 🡒
          bigAnd ((List.finRange 2).flatMap fun a => (List.finRange D.size).map fun l =>
            ((appEqNum 4 1 a.val ⋏ appEqNum 3 1 l.val) 🡒 appEqNum 3 0 (D.next a l).val)))))
  let φRight : SetTheorySemiproposition 6 :=
    Semiformula.ballMem (&0)
      ((Semiformula.rel Language.Set.Rel.eq ![#4, #0] ⋎
          (Rew.subst ![#4, #0] ▹ Rewriting.emb intLtFormula)) 🡒
        (∼(numMemApp 1 0 (n * D.size)) ⋏
          (∀¹ ((Rew.subst ![#0, #1] ▹ Rewriting.emb Constant14.integerSucc.dfn) 🡒
            bigAnd ((List.finRange 2).flatMap fun a => (nodes cert).flatMap fun p =>
              ((nodes cert).filter fun r => cert.edge p a r).map fun r =>
                ((appEqNum 4 1 a.val ⋏ numMemApp 2 1 (nodeId cert p)) 🡒
                  numMemApp 2 0 (nodeId cert r)))))))
  let φHead : SetTheorySemiproposition 6 :=
    bigAnd ((List.finRange n).flatMap fun qf => (List.finRange D.size).map fun l =>
      ((bvarEqNum 4 qf.val ⋏ appEqNum 1 3 l.val) 🡒 numMemApp 0 3 (nodeId cert (some (qf, l)))))
  let φPair : SetTheorySemiproposition 6 :=
    ∃¹ ((Rew.subst ![#0, #4, #3] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋏
        (Rew.subst ![#6, #5, #0] ▹ Rewriting.emb SetTheory.kpair.dfn))
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.bexsMem (&4)
      (Semiformula.bexsMem (&0)
        (Semiformula.bexsMem (&1)
          (Semiformula.bexsMem (&2)
            (Semiformula.bexsMem (&3)
              (φPair ⋏ φLeft ⋏ φRight ⋏ φHead)))))
  let ε : ℕ → M0.V := fun k =>
    if k = 0 then intSetV M0 else if k = 1 then F_g else if k = 2 then F_L else if k = 3 then F_S else vnNatV M0 n
  obtain ⟨A, hA⟩ := sepV M0 (cfgSetV M0 (n + 1)) φ ε
  -- Helper characterization of `z ∈ A`
  have hA_iff : ∀ z : M0.V, M0.mem z A ↔
      ∃ (q : Fin n) (pos g L S : M0.V),
        M0.mem pos (intSetV M0) ∧ M0.mem g F_g ∧ M0.mem L F_L ∧ M0.mem S F_S ∧
        z = kpairV M0 (vnNatV M0 q.val) (kpairV M0 pos g) ∧
        (∀ u : M0.V, M0.mem u (intSetV M0) → intLtV M0 u pos →
          ∀ (a : Fin 2) (l : Fin D.size),
            zfcAppV M0 g u = vnNatV M0 a.val → zfcAppV M0 L u = vnNatV M0 l.val →
              zfcAppV M0 L (intSuccV M0 u) = vnNatV M0 (D.next a l).val) ∧
        (∀ u : M0.V, M0.mem u (intSetV M0) → intLeV M0 pos u →
          ¬ M0.mem (vnNatV M0 (n * D.size)) (zfcAppV M0 S u) ∧
          ∀ (a : Fin 2) (p r : Node cert), cert.edge p a r = true →
            zfcAppV M0 g u = vnNatV M0 a.val →
            M0.mem (vnNatV M0 (nodeId cert p)) (zfcAppV M0 S u) →
              M0.mem (vnNatV M0 (nodeId cert r)) (zfcAppV M0 S (intSuccV M0 u))) ∧
        (∀ (l : Fin D.size), zfcAppV M0 L pos = vnNatV M0 l.val →
          M0.mem (vnNatV M0 (nodeId cert (some (q, l)))) (zfcAppV M0 S pos)) := by
    intro z
    rw [hA z]
    have hφ_iff : evalM M0.mem ![z] ε φ ↔
        ∃ (q : Fin n) (pos g L S : M0.V),
          M0.mem pos (intSetV M0) ∧ M0.mem g F_g ∧ M0.mem L F_L ∧ M0.mem S F_S ∧
          z = kpairV M0 (vnNatV M0 q.val) (kpairV M0 pos g) ∧
          (∀ u : M0.V, M0.mem u (intSetV M0) → intLtV M0 u pos →
            ∀ (a : Fin 2) (l : Fin D.size),
              zfcAppV M0 g u = vnNatV M0 a.val → zfcAppV M0 L u = vnNatV M0 l.val →
                zfcAppV M0 L (intSuccV M0 u) = vnNatV M0 (D.next a l).val) ∧
          (∀ u : M0.V, M0.mem u (intSetV M0) → intLeV M0 pos u →
            ¬ M0.mem (vnNatV M0 (n * D.size)) (zfcAppV M0 S u) ∧
            ∀ (a : Fin 2) (p r : Node cert), cert.edge p a r = true →
              zfcAppV M0 g u = vnNatV M0 a.val →
              M0.mem (vnNatV M0 (nodeId cert p)) (zfcAppV M0 S u) →
                M0.mem (vnNatV M0 (nodeId cert r)) (zfcAppV M0 S (intSuccV M0 u))) ∧
          (∀ (l : Fin D.size), zfcAppV M0 L pos = vnNatV M0 l.val →
            M0.mem (vnNatV M0 (nodeId cert (some (q, l)))) (zfcAppV M0 S pos)) := by
      dsimp only [φ]
      rw [evalM_bexsMem]
      let φAfterQ : SetTheorySemiproposition 2 :=
        Semiformula.bexsMem (&0)
          (Semiformula.bexsMem (&1)
            (Semiformula.bexsMem (&2)
              (Semiformula.bexsMem (&3)
                (φPair ⋏ φLeft ⋏ φRight ⋏ φHead))))
      have hq_step : (∃ qv : M0.V, M0.mem qv (vnNatV M0 n) ∧
            evalM M0.mem (qv :> z :> ![]) ε φAfterQ) ↔
          ∃ q : Fin n, evalM M0.mem (vnNatV M0 q.val :> z :> ![]) ε φAfterQ := by
        constructor
        · rintro ⟨qv, hqv, h⟩
          obtain ⟨k, hk, rfl⟩ := (mem_vnNatV_iff M0).mp hqv
          exact ⟨⟨k, hk⟩, h⟩
        · rintro ⟨q, h⟩
          exact ⟨vnNatV M0 q.val, vnNatV_lt_mem M0 q.isLt, h⟩
      refine hq_step.trans (exists_congr fun q => ?_)
      dsimp only [φAfterQ]
      rw [evalM_bexsMem]; refine exists_congr fun pos => ?_
      change (M0.mem pos (intSetV M0) ∧ _) ↔ _
      refine ⟨fun ⟨hpos, h⟩ => ?_, fun ⟨g, L, S, hpos, hg, hL, hS, rest⟩ => ⟨hpos, ?_⟩⟩
      · rw [evalM_bexsMem] at h; obtain ⟨g, hg, h⟩ := h
        rw [evalM_bexsMem] at h; obtain ⟨L, hL, h⟩ := h
        rw [evalM_bexsMem] at h; obtain ⟨S, hS, h⟩ := h
        rw [evalM_and, evalM_and, evalM_and] at h
        rcases h with ⟨h1, h2, h3, h4⟩
        refine ⟨g, L, S, hpos, hg, hL, hS, ?_, ?_, ?_, ?_⟩
        · exact (evalM_kpair3 M0 (S :> L :> g :> pos :> vnNatV M0 q.val :> z :> ![]) ε 5 4 3 2).mp h1
        · intro u hu hlt a l hgu hLu
          dsimp only [φLeft] at h2
          rw [evalM_ballMem] at h2
          have hu2 := h2 u hu
          rw [evalM_imp] at hu2
          have hlt' : evalM M0.mem (u :> S :> L :> g :> pos :> vnNatV M0 q.val :> z :> ![]) ε
              ((Rewriting.emb intLtFormula) ⇜ ![#0, #4]) := by
            rw [evalM_subst, evalM_emb]
            refine (evalRaw_congr Eq M0.mem intLtFormula ?_ rfl).mpr ((ev_intLt M0 u pos).mpr hlt)
            funext i; fin_cases i <;> rfl
          have hu3 := hu2 hlt'
          rw [evalM_all] at hu3
          have hu4 := hu3 (intSuccV M0 u)
          rw [evalM_imp] at hu4
          have hsucc' : evalM M0.mem (intSuccV M0 u :> u :> S :> L :> g :> pos :> vnNatV M0 q.val :> z :> ![]) ε
              ((Rewriting.emb Constant14.integerSucc.dfn) ⇜ ![#0, #1]) := by
            rw [evalM_subst, evalM_emb]
            refine (evalRaw_congr Eq M0.mem Constant14.integerSucc.dfn ?_ rfl).mpr
              ((ev_integerSucc_iff M0 hu _).mpr rfl)
            funext i; fin_cases i <;> rfl
          have hu5 := hu4 hsucc'
          rw [evalM_bigAnd] at hu5
          have hmem_list : (((appEqNum (m := 8) 4 1 a.val ⋏ appEqNum 3 1 l.val) 🡒
              appEqNum 3 0 (D.next a l).val)) ∈
              ((List.finRange 2).flatMap fun a => (List.finRange D.size).map fun l =>
                ((appEqNum (m := 8) 4 1 a.val ⋏ appEqNum 3 1 l.val) 🡒
                  appEqNum 3 0 (D.next a l).val)) := by
            rw [List.mem_flatMap]; exact ⟨a, List.mem_finRange a, List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩⟩
          have hitem := hu5 _ hmem_list
          rw [evalM_imp, evalM_and, evalM_appEqNum, evalM_appEqNum, evalM_appEqNum] at hitem
          exact hitem ⟨hgu, hLu⟩
        · intro u hu hle
          dsimp only [φRight] at h3
          rw [evalM_ballMem] at h3
          have hu2 := h3 u hu
          rw [evalM_imp] at hu2
          have hle' : evalM M0.mem (u :> S :> L :> g :> pos :> vnNatV M0 q.val :> z :> ![]) ε
              (Semiformula.rel Language.Set.Rel.eq ![#4, #0] ⋎
                (Rew.subst ![#4, #0] ▹ Rewriting.emb intLtFormula)) := by
            rw [evalM_or]
            rcases hle with rfl | hlt
            · exact Or.inl rfl
            · right
              change evalM M0.mem _ ε ((Rewriting.emb intLtFormula) ⇜ ![#4, #0])
              rw [evalM_subst, evalM_emb]
              refine (evalRaw_congr Eq M0.mem intLtFormula ?_ rfl).mpr ((ev_intLt M0 pos u).mpr hlt)
              funext i; fin_cases i <;> rfl
          have ⟨hno, hu3⟩ := (evalM_and _ _ _ _).mp (hu2 hle')
          rw [evalM_not, evalM_numMemApp] at hno
          refine ⟨hno, fun a p r hedge hgu hpS => ?_⟩
          rw [evalM_all] at hu3
          have hu4 := hu3 (intSuccV M0 u)
          rw [evalM_imp] at hu4
          have hsucc' : evalM M0.mem (intSuccV M0 u :> u :> S :> L :> g :> pos :> vnNatV M0 q.val :> z :> ![]) ε
              ((Rewriting.emb Constant14.integerSucc.dfn) ⇜ ![#0, #1]) := by
            rw [evalM_subst, evalM_emb]
            refine (evalRaw_congr Eq M0.mem Constant14.integerSucc.dfn ?_ rfl).mpr
              ((ev_integerSucc_iff M0 hu _).mpr rfl)
            funext i; fin_cases i <;> rfl
          have hu5 := hu4 hsucc'
          rw [evalM_bigAnd] at hu5
          have hmem_p : p ∈ nodes cert := by
            rcases p with _ | ⟨pq, pl⟩ <;> simp [nodes]
          have hmem_r : r ∈ nodes cert := by
            rcases r with _ | ⟨rq, rl⟩ <;> simp [nodes]
          have hmem_list : (((appEqNum (m := 8) 4 1 a.val ⋏ numMemApp 2 1 (nodeId cert p)) 🡒
              numMemApp 2 0 (nodeId cert r))) ∈
              ((List.finRange 2).flatMap fun a => (nodes cert).flatMap fun p =>
                ((nodes cert).filter fun r => cert.edge p a r).map fun r =>
                  ((appEqNum (m := 8) 4 1 a.val ⋏ numMemApp 2 1 (nodeId cert p)) 🡒
                    numMemApp 2 0 (nodeId cert r))) := by
            rw [List.mem_flatMap]; refine ⟨a, List.mem_finRange a, ?_⟩
            rw [List.mem_flatMap]; refine ⟨p, hmem_p, ?_⟩
            rw [List.mem_map]; exact ⟨r, List.mem_filter.mpr ⟨hmem_r, hedge⟩, rfl⟩
          have hitem := hu5 _ hmem_list
          rw [evalM_imp, evalM_and, evalM_appEqNum, evalM_numMemApp, evalM_numMemApp] at hitem
          exact hitem ⟨hgu, hpS⟩
        · intro l hLp
          dsimp only [φHead] at h4
          rw [evalM_bigAnd] at h4
          have hmem_list : (((bvarEqNum (m := 6) 4 q.val ⋏ appEqNum 1 3 l.val) 🡒
              numMemApp 0 3 (nodeId cert (some (q, l))))) ∈
              ((List.finRange n).flatMap fun qf => (List.finRange D.size).map fun l =>
                ((bvarEqNum (m := 6) 4 qf.val ⋏ appEqNum 1 3 l.val) 🡒
                  numMemApp 0 3 (nodeId cert (some (qf, l))))) := by
            rw [List.mem_flatMap]; exact ⟨q, List.mem_finRange q, List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩⟩
          have hitem := h4 _ hmem_list
          rw [evalM_imp, evalM_and, evalM_bvarEqNum, evalM_appEqNum, evalM_numMemApp] at hitem
          exact hitem ⟨rfl, hLp⟩
      · rcases rest with ⟨hz_eq, hleft, hright, hhead⟩
        rw [evalM_bexsMem]; refine ⟨g, hg, ?_⟩
        rw [evalM_bexsMem]; refine ⟨L, hL, ?_⟩
        rw [evalM_bexsMem]; refine ⟨S, hS, ?_⟩
        rw [evalM_and, evalM_and, evalM_and]
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact (evalM_kpair3 M0 (S :> L :> g :> pos :> vnNatV M0 q.val :> z :> ![]) ε 5 4 3 2).mpr hz_eq
        · dsimp only [φLeft]
          rw [evalM_ballMem]; intro u hu
          rw [evalM_imp]; intro hlt_raw
          have hlt : intLtV M0 u pos := (ev_intLt M0 u pos).mp (by
            change evalM M0.mem _ ε ((Rewriting.emb intLtFormula) ⇜ ![#0, #4]) at hlt_raw
            rw [evalM_subst, evalM_emb] at hlt_raw
            refine (evalRaw_congr Eq M0.mem intLtFormula ?_ rfl).mp hlt_raw
            funext i; fin_cases i <;> rfl)
          rw [evalM_all]; intro u'
          rw [evalM_imp]; intro hsucc_raw
          have hu' : u' = intSuccV M0 u := (ev_integerSucc_iff M0 hu u').mp (by
            change evalM M0.mem _ ε ((Rewriting.emb Constant14.integerSucc.dfn) ⇜ ![#0, #1]) at hsucc_raw
            rw [evalM_subst, evalM_emb] at hsucc_raw
            refine (evalRaw_congr Eq M0.mem Constant14.integerSucc.dfn ?_ rfl).mp hsucc_raw
            funext i; fin_cases i <;> rfl)
          subst hu'
          rw [evalM_bigAnd]; intro item hitem
          rw [List.mem_flatMap] at hitem; obtain ⟨a, _, hitem⟩ := hitem
          rw [List.mem_map] at hitem; obtain ⟨l, _, rfl⟩ := hitem
          rw [evalM_imp, evalM_and, evalM_appEqNum, evalM_appEqNum, evalM_appEqNum]
          rintro ⟨hgu, hLu⟩
          exact hleft u hu hlt a l hgu hLu
        · dsimp only [φRight]
          rw [evalM_ballMem]; intro u hu
          rw [evalM_imp]; intro hle_raw
          have hle : intLeV M0 pos u := by
            rw [evalM_or] at hle_raw
            rcases hle_raw with heq | hlt_raw
            · exact Or.inl heq
            · right
              change evalM M0.mem _ ε ((Rewriting.emb intLtFormula) ⇜ ![#4, #0]) at hlt_raw
              rw [evalM_subst, evalM_emb] at hlt_raw
              exact (ev_intLt M0 pos u).mp (by
                refine (evalRaw_congr Eq M0.mem intLtFormula ?_ rfl).mp hlt_raw
                funext i; fin_cases i <;> rfl)
          obtain ⟨hno, hstep⟩ := hright u hu hle
          rw [evalM_and, evalM_not, evalM_numMemApp]
          refine ⟨hno, ?_⟩
          rw [evalM_all]; intro u'
          rw [evalM_imp]; intro hsucc_raw
          have hu' : u' = intSuccV M0 u := (ev_integerSucc_iff M0 hu u').mp (by
            change evalM M0.mem _ ε ((Rewriting.emb Constant14.integerSucc.dfn) ⇜ ![#0, #1]) at hsucc_raw
            rw [evalM_subst, evalM_emb] at hsucc_raw
            refine (evalRaw_congr Eq M0.mem Constant14.integerSucc.dfn ?_ rfl).mp hsucc_raw
            funext i; fin_cases i <;> rfl)
          subst hu'
          rw [evalM_bigAnd]; intro item hitem
          rw [List.mem_flatMap] at hitem; obtain ⟨a, _, hitem⟩ := hitem
          rw [List.mem_flatMap] at hitem; obtain ⟨p, _, hitem⟩ := hitem
          rw [List.mem_map] at hitem; obtain ⟨r, hr_filt, rfl⟩ := hitem
          have hedge : cert.edge p a r = true := (List.mem_filter.mp hr_filt).2
          rw [evalM_imp, evalM_and, evalM_appEqNum, evalM_numMemApp, evalM_numMemApp]
          rintro ⟨hgu, hpS⟩
          exact hstep a p r hedge hgu hpS
        · dsimp only [φHead]
          rw [evalM_bigAnd]; intro item hitem
          rw [List.mem_flatMap] at hitem; obtain ⟨qf, _, hitem⟩ := hitem
          rw [List.mem_map] at hitem; obtain ⟨l, _, rfl⟩ := hitem
          rw [evalM_imp, evalM_and, evalM_bvarEqNum, evalM_appEqNum, evalM_numMemApp]
          rintro ⟨hqeq, hLp⟩
          have hqf : q = qf := Fin.ext (vnNatV_inj M0 hqeq)
          subst hqf
          exact hhead l hLp
    rw [hφ_iff]
    refine ⟨And.right, fun h => ⟨?_, h⟩⟩
    rcases h with ⟨q, pos, g, _, _, hpos, hg, _, _, rfl, _, _, _⟩
    exact (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (Nat.lt_succ_of_lt q.isLt),
      (kpairV_mem_prodV M0).mpr ⟨hpos, hg⟩⟩
  -- Helper: `nodeId cert p < W`
  have hnodeId_lt : ∀ p : Node cert, nodeId cert p < W := by
    intro p
    rcases p with _ | ⟨pq, pl⟩
    · dsimp only [nodeId, W, D]; omega
    · dsimp only [nodeId, W, D]
      have h1 : pq.val + 1 ≤ n := pq.isLt
      have h2 : (pq.val + 1) * cert.dfa.size ≤ n * cert.dfa.size := Nat.mul_le_mul_right _ h1
      have h3 : pq.val * cert.dfa.size + pl.val < pq.val * cert.dfa.size + cert.dfa.size :=
        Nat.add_lt_add_left pl.isLt _
      have h4 : pq.val * cert.dfa.size + cert.dfa.size = (pq.val + 1) * cert.dfa.size := by ring
      omega
  have hnodeId_inj : Function.Injective (nodeId cert) := by
    intro p1 p2 heq
    rcases p1 with _ | ⟨q1, l1⟩ <;> rcases p2 with _ | ⟨q2, l2⟩
    · rfl
    · dsimp only [nodeId] at heq
      have h1 : q2.val * cert.dfa.size + l2.val < n * cert.dfa.size := by
        have hlt := Nat.add_lt_add_left l2.isLt (q2.val * cert.dfa.size)
        have hle : (q2.val + 1) * cert.dfa.size ≤ n * cert.dfa.size := Nat.mul_le_mul_right _ q2.isLt
        have hmul : q2.val * cert.dfa.size + cert.dfa.size = (q2.val + 1) * cert.dfa.size := by ring
        omega
      omega
    · dsimp only [nodeId] at heq
      have h1 : q1.val * cert.dfa.size + l1.val < n * cert.dfa.size := by
        have hlt := Nat.add_lt_add_left l1.isLt (q1.val * cert.dfa.size)
        have hle : (q1.val + 1) * cert.dfa.size ≤ n * cert.dfa.size := Nat.mul_le_mul_right _ q1.isLt
        have hmul : q1.val * cert.dfa.size + cert.dfa.size = (q1.val + 1) * cert.dfa.size := by ring
        omega
      omega
    · dsimp only [nodeId] at heq
      have hdiv : q1.val = q2.val := by
        have h1 := congrArg (· / cert.dfa.size) heq
        rw [Nat.mul_comm q1.val _, Nat.mul_comm q2.val _,
          Nat.mul_add_div (Nat.succ_pos _), Nat.mul_add_div (Nat.succ_pos _),
          Nat.div_eq_of_lt l1.isLt, Nat.div_eq_of_lt l2.isLt, add_zero, add_zero] at h1
        exact h1
      have hmod : l1.val = l2.val := by
        have h1 := congrArg (· % cert.dfa.size) heq
        rw [Nat.mul_comm q1.val _, Nat.mul_comm q2.val _,
          Nat.mul_add_mod, Nat.mul_add_mod,
          Nat.mod_eq_of_lt l1.isLt, Nat.mod_eq_of_lt l2.isLt] at h1
        exact h1
      rw [Fin.ext hdiv, Fin.ext hmod]
  -- Unpack `checkBlank cert = true`
  simp only [checkBlank, Bool.and_eq_true_iff, Bool.not_eq_true_eq_eq_false] at hb
  obtain ⟨⟨hblank_start, hblank_sink⟩, hblank_closure⟩ := hb
  refine ⟨A, ?_, ?_, ?_⟩
  · -- Initial configuration `simCfgV M0 M 0 ∈ A`
    rw [hA_iff]
    let L0 := constFunV M0 (intSetV M0) (vnNatV M0 D.size) (vnNatV M0 0)
      (vnNatV_lt_mem M0 (Nat.succ_pos _))
    let blankSet := listToV M0 (((nodes cert).filter cert.onBlank).map fun p => vnNatV M0 (nodeId cert p))
    have hblankSet_mem : M0.mem blankSet P_W := by
      rw [mem_powersetV]
      intro w hw
      rw [mem_listToV, List.mem_map] at hw
      obtain ⟨p, _, rfl⟩ := hw
      exact vnNatV_lt_mem M0 (hnodeId_lt p)
    let S0 := constFunV M0 (intSetV M0) P_W blankSet hblankSet_mem
    have hmem_blankSet : ∀ p : Node cert, M0.mem (vnNatV M0 (nodeId cert p)) blankSet ↔ cert.onBlank p = true := by
      intro p
      rw [mem_listToV, List.mem_map]
      constructor
      · rintro ⟨p', hp', heq⟩
        have hp_eq : p' = p := hnodeId_inj (vnNatV_inj M0 heq)
        subst hp_eq
        exact (List.mem_filter.mp hp').2
      · intro hon
        have hp_nodes : p ∈ nodes cert := by rcases p with _ | ⟨pq, pl⟩ <;> simp [nodes]
        exact ⟨p, List.mem_filter.mpr ⟨hp_nodes, hon⟩, rfl⟩
    refine ⟨0, encodeIntV M0 0, emptyTapeV M0, L0, S0,
      encodeIntV_mem M0 0, emptyTapeV_mem_funs M0,
      constFunV_mem_funs M0 _, constFunV_mem_funs M0 _, rfl, ?_, ?_, ?_⟩
    · intro u hu _ a l hgu hLu
      rw [emptyTapeV_app M0 hu] at hgu
      rw [constFunV_app M0 _ hu] at hLu
      have ha : a = 0 := Fin.ext (vnNatV_inj M0 hgu).symm
      have hl : l = 0 := Fin.ext (vnNatV_inj M0 hLu).symm
      subst ha hl
      rw [constFunV_app M0 _ (intSuccV_mem M0 hu), D.blank]
      rfl
    · intro u hu _
      refine ⟨?_, ?_⟩
      · rw [constFunV_app M0 _ hu]
        change ¬ M0.mem (vnNatV M0 (nodeId cert none)) blankSet
        rw [hmem_blankSet none, hblank_sink]
        decide
      · intro a p r hedge hgu hpS
        rw [emptyTapeV_app M0 hu] at hgu
        have ha : a = 0 := Fin.ext (vnNatV_inj M0 hgu).symm
        subst ha
        rw [constFunV_app M0 _ hu, hmem_blankSet] at hpS
        rw [constFunV_app M0 _ (intSuccV_mem M0 hu), hmem_blankSet]
        have ht := allNodes hblank_closure p
        simp only [hpS, if_true] at ht
        have hn := allNodes ht r
        simp [hedge] at hn
        exact hn
    · intro l hL0
      rw [constFunV_app M0 _ (encodeIntV_mem M0 0)] at hL0
      have hl : l = 0 := Fin.ext (vnNatV_inj M0 hL0).symm
      subst hl
      rw [constFunV_app M0 _ (encodeIntV_mem M0 0), hmem_blankSet]
      exact hblank_start
  · -- Closure under `nextStepV M0 M`
    intro y hy
    obtain ⟨q, pos, g, L, S, hpos, hg, hL, hS, rfl, hleft, hright, hhead⟩ := (hA_iff y).mp hy
    obtain ⟨aCode, ha_lt, ha_eq⟩ := (mem_vnNatV_iff M0).mp (zfcAppV_mem_codomain M0 hg hpos)
    obtain ⟨lCode, hl_lt, hl_eq⟩ := (mem_vnNatV_iff M0).mp (zfcAppV_mem_codomain M0 hL hpos)
    let a : Fin 2 := ⟨aCode, ha_lt⟩
    let l : Fin D.size := ⟨lCode, hl_lt⟩
    have hq_in_S : M0.mem (vnNatV M0 (nodeId cert (some (q, l)))) (zfcAppV M0 S pos) := hhead l hl_eq
    have hchk_at := allFin (allFin (allFin hchk q) a) l
    unfold checkAt at hchk_at
    cases hget : tb.get (q, a) with
    | none =>
      rw [hget] at hchk_at
      have hnone_in := (hright pos hpos (Or.inl rfl)).2 a (some (q, l)) none hchk_at ha_eq hq_in_S
      have hnone_out := (hright (intSuccV M0 pos) (intSuccV_mem M0 hpos)
        (Or.inr (intLtV_self_intSuccV M0 hpos))).1
      exact (hnone_out hnone_in).elim
    | some m =>
      rw [hget] at hchk_at
      have hong := hm (q, a) m hget
      have hlu := transLookup_of_ongoing hong
      rw [zfcAppV_nextStepV_cfg M0 M q.val (Nat.lt_succ_of_lt q.isLt) pos g hpos hg a.val a.isLt ha_eq]
      rw [hlu, hA_iff]
      let g' := updateTapeV M0 g pos (vnNatV M0 m.write.val)
      have hg' : M0.mem g' F_g := updateTapeV_mem_funs M0 hg hpos (vnNatV_lt_mem M0 m.write.isLt)
      cases hdir : m.left with
      | false =>
        -- Move right to `pos' = intSuccV M0 pos`
        simp only [Bool.false_eq_true, ↓reduceIte, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
        let pos' := intSuccV M0 pos
        have hpos' : M0.mem pos' (intSetV M0) := intSuccV_mem M0 hpos
        let lNext : Fin D.size := D.next m.write l
        let L' := updateFunV M0 (intSetV M0) (vnNatV M0 D.size) L pos' (vnNatV M0 lNext.val)
        have hL' : M0.mem L' F_L := updateFunV_mem_funs M0 hL hpos' (vnNatV_lt_mem M0 lNext.isLt)
        refine ⟨m.state, pos', g', L', S, hpos', hg', hL', hS, rfl, ?_, ?_, ?_⟩
        · intro u hu hlt a_u l_u hgu hLu
          have hle_pos : intLeV M0 u pos := by
            have h1 := (intLtV_iff_intLeV_intSuccV M0 hu hpos').mp hlt
            rcases h1 with heq | hlt2
            · exact Or.inl (intSuccV_inj M0 hu hpos heq)
            · right
              rcases intLtV_trichotomy M0 hu hpos with h | rfl | hgt
              · exact h
              · exact (intLtV_irrefl M0 _ hlt2).elim
              · have hge := (intLtV_iff_intLeV_intSuccV M0 hpos hu).mp hgt
                rcases hge with heq2 | hlt3
                · rw [← heq2] at hlt
                  exact (intLtV_irrefl M0 _ hlt).elim
                · exact (intLtV_asymm M0 hlt hlt3).elim
          have hu_ne_pos' : u ≠ pos' := fun h => intLtV_irrefl M0 _ (h ▸ hlt)
          rw [updateFunV_app M0 hL hpos' (vnNatV_lt_mem M0 lNext.isLt) hu, if_neg hu_ne_pos'] at hLu
          rw [updateFunV_app M0 hL hpos' (vnNatV_lt_mem M0 lNext.isLt) (intSuccV_mem M0 hu)]
          rcases hle_pos with rfl | hlt_pos
          · rw [if_pos rfl]
            rw [updateTapeV_app M0 hg hpos (vnNatV_lt_mem M0 m.write.isLt) hpos, if_pos rfl] at hgu
            have ha_w : a_u = m.write := Fin.ext (vnNatV_inj M0 hgu).symm
            have hl_w : l_u = l := Fin.ext (vnNatV_inj M0 (hLu.symm.trans hl_eq))
            subst ha_w hl_w; rfl
          · have hu_ne_pos : u ≠ pos := fun h => intLtV_irrefl M0 _ (h ▸ hlt_pos)
            have hsu_ne_pos' : intSuccV M0 u ≠ pos' := fun h => hu_ne_pos (intSuccV_inj M0 hu hpos h)
            rw [if_neg hsu_ne_pos']
            rw [updateTapeV_app M0 hg hpos (vnNatV_lt_mem M0 m.write.isLt) hu, if_neg hu_ne_pos] at hgu
            exact hleft u hu hlt_pos a_u l_u hgu hLu
        · intro u hu hle_pos'
          have hlt_pos : intLtV M0 pos u := (intLtV_iff_intLeV_intSuccV M0 hpos hu).mpr hle_pos'
          have hu_ne_pos : u ≠ pos := fun h => intLtV_irrefl M0 _ (h ▸ hlt_pos)
          obtain ⟨hno, hstep⟩ := hright u hu (Or.inr hlt_pos)
          refine ⟨hno, fun a_u p r hedge hgu hpS => ?_⟩
          rw [updateTapeV_app M0 hg hpos (vnNatV_lt_mem M0 m.write.isLt) hu, if_neg hu_ne_pos] at hgu
          exact hstep a_u p r hedge hgu hpS
        · intro l_u hLu
          rw [updateFunV_app M0 hL hpos' (vnNatV_lt_mem M0 lNext.isLt) hpos', if_pos rfl] at hLu
          have hl_eq' : l_u = lNext := Fin.ext (vnNatV_inj M0 hLu).symm
          subst hl_eq'
          simp only [hdir, Bool.false_eq_true, ↓reduceIte] at hchk_at
          exact (hright pos hpos (Or.inl rfl)).2 a (some (q, l)) (some (m.state, lNext)) hchk_at ha_eq hq_in_S
      | true =>
        -- Move left to `pos' = intPredV M0 pos`
        simp only [↓reduceIte]
        let pos' := intPredV M0 pos
        have hpos' : M0.mem pos' (intSetV M0) := intPredV_mem M0 hpos
        have hpos'_lt : intLtV M0 pos' pos := intLtV_intPredV_self M0 hpos
        have hpos_ne_pos' : pos ≠ pos' := fun h => intLtV_irrefl M0 _ (h ▸ hpos'_lt)
        have hsucc_pos' : intSuccV M0 pos' = pos := intSuccV_intPredV M0 hpos
        obtain ⟨a'Code, ha'_lt, ha'_eq⟩ := (mem_vnNatV_iff M0).mp (zfcAppV_mem_codomain M0 hg hpos')
        let a' : Fin 2 := ⟨a'Code, ha'_lt⟩
        let Sp := listToV M0 (((nodes cert).filter fun s =>
            decide (∀ t : Node cert, cert.edge s m.write t = true →
              M0.mem (vnNatV M0 (nodeId cert t)) (zfcAppV M0 S (intSuccV M0 pos)))).map
            fun s => vnNatV M0 (nodeId cert s))
        have hSp_mem : M0.mem Sp P_W := by
          rw [mem_powersetV]; intro w hw
          rw [mem_listToV, List.mem_map] at hw
          obtain ⟨s, _, rfl⟩ := hw; exact vnNatV_lt_mem M0 (hnodeId_lt s)
        have hmem_Sp : ∀ s : Node cert, M0.mem (vnNatV M0 (nodeId cert s)) Sp ↔
            ∀ t : Node cert, cert.edge s m.write t = true →
              M0.mem (vnNatV M0 (nodeId cert t)) (zfcAppV M0 S (intSuccV M0 pos)) := by
          intro s
          rw [mem_listToV, List.mem_map]
          constructor
          · rintro ⟨s', hs', heq⟩
            have hs_eq : s' = s := hnodeId_inj (vnNatV_inj M0 heq)
            subst hs_eq
            exact of_decide_eq_true (List.mem_filter.mp hs').2
          · intro hall
            have hs_nodes : s ∈ nodes cert := by rcases s with _ | ⟨sq, sl⟩ <;> simp [nodes]
            exact ⟨s, List.mem_filter.mpr ⟨hs_nodes, decide_eq_true hall⟩, rfl⟩
        let Spm := listToV M0 (((nodes cert).filter fun p =>
            decide (∀ s : Node cert, cert.edge p a' s = true →
              M0.mem (vnNatV M0 (nodeId cert s)) Sp)).map
            fun p => vnNatV M0 (nodeId cert p))
        have hSpm_mem : M0.mem Spm P_W := by
          rw [mem_powersetV]; intro w hw
          rw [mem_listToV, List.mem_map] at hw
          obtain ⟨p, _, rfl⟩ := hw; exact vnNatV_lt_mem M0 (hnodeId_lt p)
        have hmem_Spm : ∀ p : Node cert, M0.mem (vnNatV M0 (nodeId cert p)) Spm ↔
            ∀ s : Node cert, cert.edge p a' s = true →
              M0.mem (vnNatV M0 (nodeId cert s)) Sp := by
          intro p
          rw [mem_listToV, List.mem_map]
          constructor
          · rintro ⟨p', hp', heq⟩
            have hp_eq : p' = p := hnodeId_inj (vnNatV_inj M0 heq)
            subst hp_eq
            exact of_decide_eq_true (List.mem_filter.mp hp').2
          · intro hall
            have hp_nodes : p ∈ nodes cert := by rcases p with _ | ⟨pq, pl⟩ <;> simp [nodes]
            exact ⟨p, List.mem_filter.mpr ⟨hp_nodes, decide_eq_true hall⟩, rfl⟩
        let S1 := updateFunV M0 (intSetV M0) P_W S pos Sp
        have hS1 : M0.mem S1 F_S := updateFunV_mem_funs M0 hS hpos hSp_mem
        let S' := updateFunV M0 (intSetV M0) P_W S1 pos' Spm
        have hS' : M0.mem S' F_S := updateFunV_mem_funs M0 hS1 hpos' hSpm_mem
        have hS'_app : ∀ u : M0.V, M0.mem u (intSetV M0) →
            zfcAppV M0 S' u = if u = pos' then Spm else if u = pos then Sp else zfcAppV M0 S u := by
          intro u hu
          rw [updateFunV_app M0 hS1 hpos' hSpm_mem hu]
          by_cases h1 : u = pos'
          · rw [if_pos h1, if_pos h1]
          · rw [if_neg h1, if_neg h1, updateFunV_app M0 hS hpos hSp_mem hu]
        have hnone_not_Sp : ¬ M0.mem (vnNatV M0 (n * D.size)) Sp := by
          change ¬ M0.mem (vnNatV M0 (nodeId cert none)) Sp
          rw [hmem_Sp]
          intro hall
          have h1 := hall none rfl
          exact (hright (intSuccV M0 pos) (intSuccV_mem M0 hpos)
            (Or.inr (intLtV_self_intSuccV M0 hpos))).1 h1
        have hnone_not_Spm : ¬ M0.mem (vnNatV M0 (n * D.size)) Spm := by
          change ¬ M0.mem (vnNatV M0 (nodeId cert none)) Spm
          rw [hmem_Spm]
          intro hall
          exact hnone_not_Sp (hall none rfl)
        refine ⟨m.state, pos', g', L, S', hpos', hg', hL, hS', rfl, ?_, ?_, ?_⟩
        · intro u hu hlt a_u l_u hgu hLu
          have hlt_pos : intLtV M0 u pos := intLtV_trans M0 hu hpos' hpos hlt hpos'_lt
          have hu_ne_pos : u ≠ pos := fun h => intLtV_irrefl M0 _ (h ▸ hlt_pos)
          rw [updateTapeV_app M0 hg hpos (vnNatV_lt_mem M0 m.write.isLt) hu, if_neg hu_ne_pos] at hgu
          exact hleft u hu hlt_pos a_u l_u hgu hLu
        · intro u hu hle_pos'
          have hsu_mem : M0.mem (intSuccV M0 u) (intSetV M0) := intSuccV_mem M0 hu
          rw [hS'_app u hu, hS'_app (intSuccV M0 u) hsu_mem]
          rcases hle_pos' with rfl | hlt_pos'
          · rw [if_pos rfl, hsucc_pos', if_neg hpos_ne_pos', if_pos rfl]
            refine ⟨hnone_not_Spm, fun a_u p s hedge hgu hpSpm => ?_⟩
            rw [updateTapeV_app M0 hg hpos (vnNatV_lt_mem M0 m.write.isLt) hpos',
              if_neg hpos_ne_pos'.symm] at hgu
            have ha_eq' : a_u = a' := Fin.ext (vnNatV_inj M0 (hgu.symm.trans ha'_eq))
            subst ha_eq'
            exact ((hmem_Spm p).mp hpSpm) s hedge
          · have hle_pos : intLeV M0 pos u := by
              have h1 := (intLtV_iff_intLeV_intSuccV M0 hpos' hu).mp hlt_pos'
              rwa [hsucc_pos'] at h1
            have hu_ne_pos' : u ≠ pos' := fun h => intLtV_irrefl M0 _ (h ▸ hlt_pos')
            rw [if_neg hu_ne_pos']
            rcases hle_pos with rfl | hlt_pos
            · have hsp_ne_pos' : intSuccV M0 pos ≠ pos' := fun h =>
                intLtV_asymm M0 (intLtV_self_intSuccV M0 hpos) (h ▸ hpos'_lt)
              have hsp_ne_pos : intSuccV M0 pos ≠ pos := fun h =>
                intLtV_irrefl M0 _ (h ▸ intLtV_self_intSuccV M0 hpos)
              rw [if_pos rfl, if_neg hsp_ne_pos', if_neg hsp_ne_pos]
              refine ⟨hnone_not_Sp, fun a_u s t hedge hgu hsSp => ?_⟩
              rw [updateTapeV_app M0 hg hpos (vnNatV_lt_mem M0 m.write.isLt) hpos, if_pos rfl] at hgu
              have ha_w : a_u = m.write := Fin.ext (vnNatV_inj M0 hgu).symm
              subst ha_w
              exact ((hmem_Sp s).mp hsSp) t hedge
            · have hu_ne_pos : u ≠ pos := fun h => intLtV_irrefl M0 _ (h ▸ hlt_pos)
              have hsu_gt_pos : intLtV M0 pos (intSuccV M0 u) :=
                intLtV_trans M0 hpos hu hsu_mem hlt_pos (intLtV_self_intSuccV M0 hu)
              have hsu_gt_pos' : intLtV M0 pos' (intSuccV M0 u) :=
                intLtV_trans M0 hpos' hpos hsu_mem hpos'_lt hsu_gt_pos
              have hsu_ne_pos' : intSuccV M0 u ≠ pos' := fun h => intLtV_irrefl M0 _ (h ▸ hsu_gt_pos')
              have hsu_ne_pos : intSuccV M0 u ≠ pos := fun h => intLtV_irrefl M0 _ (h ▸ hsu_gt_pos)
              rw [if_neg hu_ne_pos, if_neg hsu_ne_pos', if_neg hsu_ne_pos]
              obtain ⟨hno, hstep⟩ := hright u hu (Or.inr hlt_pos)
              refine ⟨hno, fun a_u p r hedge hgu hpS => ?_⟩
              rw [updateTapeV_app M0 hg hpos (vnNatV_lt_mem M0 m.write.isLt) hu, if_neg hu_ne_pos] at hgu
              exact hstep a_u p r hedge hgu hpS
        · intro l' hLl'
          rw [hS'_app pos' hpos', if_pos rfl, hmem_Spm]
          have hstepL := hleft pos' hpos' hpos'_lt a' l' ha'_eq hLl'
          rw [hsucc_pos', hl_eq] at hstepL
          have hnext_eq : cert.dfa.next a' l' = l := Fin.ext (vnNatV_inj M0 hstepL).symm
          intro s hs_edge
          rw [hmem_Sp]
          intro t ht_edge
          simp only [hdir, ↓reduceIte] at hchk_at
          have h1 := allFin (allFin hchk_at l') a'
          simp only [hnext_eq, ↓reduceIte] at h1
          have h2 := allNodes h1 s
          simp only [hs_edge, ↓reduceIte] at h2
          have h3 := allNodes h2 t
          simp only [ht_edge, Bool.not_true, Bool.false_or] at h3
          exact (hright pos hpos (Or.inl rfl)).2 a (some (q, l)) t h3 ha_eq hq_in_S
  · -- Non-halting
    intro y hy heq
    obtain ⟨q, pos, g, _, _, _, _, _, _, rfl, _, _, _⟩ := (hA_iff y).mp hy
    rw [pi1V_kpairV] at heq
    exact Nat.ne_of_lt q.isLt (vnNatV_inj M0 heq)

/- Bridge 3: `reindex` pullback -/

lemma reindex_invariant {n : ℕ} [NeZero n] {M : MachineOf n}
    (e : Fin n ≃ Fin n) (h0 : e 0 = 0) (mirror : Bool)
    (hInv : HasNonHaltingInvariant M0 (reindex M e mirror)) :
    HasNonHaltingInvariant M0 M := by
  obtain ⟨A', hA'0, hA'step, hA'nohalt⟩ := hInv
  let F_g := funsV M0 (intSetV M0) (vnNatV M0 2)
  let φState : SetTheorySemiproposition 7 :=
    bigAnd ((List.finRange n).map fun qf => bvarEqNum 5 qf.val 🡒 bvarEqNum 2 (e qf).val)
  let φPos : SetTheorySemiproposition 7 :=
    if mirror then Rew.subst ![#1, #4] ▹ Rewriting.emb intNegFormula
    else Semiformula.rel Language.Set.Rel.eq ![#1, #4]
  let φTape : SetTheorySemiproposition 7 :=
    if mirror then
      Semiformula.ballMem (&2)
        (∀¹ ((Rew.subst ![#0, #1] ▹ Rewriting.emb intNegFormula) 🡒
          bigAnd ((List.finRange 2).map fun a => appEqNum 2 1 a.val 🡘 appEqNum 5 0 a.val)))
    else Semiformula.rel Language.Set.Rel.eq ![#0, #3]
  let φInA' : SetTheorySemiproposition 7 :=
    ∃¹ ((Rew.subst ![#0, #2, #1] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋏
        (∃¹ ((Rew.subst ![#0, #4, #1] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋏
             Semiformula.rel Language.Set.Rel.mem ![#0, &0])))
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.bexsMem (&1)
      (Semiformula.bexsMem (&2)
        (Semiformula.bexsMem (&3)
          ((∃¹ ((Rew.subst ![#0, #2, #1] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋏
                (Rew.subst ![#4, #3, #0] ▹ Rewriting.emb SetTheory.kpair.dfn))) ⋏
           Semiformula.bexsMem (&1)
             (Semiformula.bexsMem (&2)
               (Semiformula.bexsMem (&3)
                 (φState ⋏ φPos ⋏ φTape ⋏ φInA'))))))
  let ε : ℕ → M0.V := fun k =>
    if k = 0 then A' else if k = 1 then vnNatV M0 n else if k = 2 then intSetV M0 else F_g
  obtain ⟨A, hA⟩ := sepV M0 (cfgSetV M0 (n + 1)) φ ε
  let mapCfg : Fin n → M0.V → M0.V → M0.V := fun q pos g =>
    kpairV M0 (vnNatV M0 (e q).val)
      (kpairV M0 (if mirror then intNegV M0 pos else pos) (if mirror then flipTapeV M0 g else g))
  have hA_iff : ∀ z : M0.V, M0.mem z A ↔
      ∃ (q : Fin n) (pos g : M0.V),
        M0.mem pos (intSetV M0) ∧ M0.mem g F_g ∧
        z = kpairV M0 (vnNatV M0 q.val) (kpairV M0 pos g) ∧
        M0.mem (mapCfg q pos g) A' := by
    intro z
    rw [hA z]
    have hφ_iff : evalM M0.mem ![z] ε φ ↔
        ∃ (q : Fin n) (pos g : M0.V),
          M0.mem pos (intSetV M0) ∧ M0.mem g F_g ∧
          z = kpairV M0 (vnNatV M0 q.val) (kpairV M0 pos g) ∧
          M0.mem (mapCfg q pos g) A' := by
      dsimp only [φ]
      rw [evalM_bexsMem]
      constructor
      · rintro ⟨qv, hqv, h⟩
        obtain ⟨qk, hqk, rfl⟩ := (mem_vnNatV_iff M0).mp hqv
        let q : Fin n := ⟨qk, hqk⟩
        rw [evalM_bexsMem] at h; obtain ⟨pos, hpos, h⟩ := h
        rw [evalM_bexsMem] at h; obtain ⟨g, hg, hpair, h⟩ := h
        have hz_eq := (evalM_kpair3 M0 (g :> pos :> vnNatV M0 q.val :> z :> ![]) ε 3 2 1 0).mp hpair
        change evalM M0.mem (g :> pos :> vnNatV M0 q.val :> z :> ![]) ε _ at h
        rw [evalM_bexsMem] at h; obtain ⟨q', hq', h⟩ := h
        rw [evalM_bexsMem] at h; obtain ⟨pos', hpos', h⟩ := h
        rw [evalM_bexsMem] at h; obtain ⟨g', hg', h⟩ := h
        rw [evalM_and, evalM_and, evalM_and] at h
        rcases h with ⟨hst, hpo, hta, hin⟩
        have hq'_eq : q' = vnNatV M0 (e q).val := by
          dsimp only [φState] at hst
          rw [evalM_bigAnd] at hst
          have hmem : (bvarEqNum (m := 7) 5 q.val 🡒 bvarEqNum 2 (e q).val) ∈
              ((List.finRange n).map fun qf => bvarEqNum (m := 7) 5 qf.val 🡒 bvarEqNum 2 (e qf).val) :=
            List.mem_map.mpr ⟨q, List.mem_finRange q, rfl⟩
          have hitem := hst _ hmem
          rw [evalM_imp, evalM_bvarEqNum, evalM_bvarEqNum] at hitem
          exact hitem rfl
        have hpos'_eq : pos' = if mirror then intNegV M0 pos else pos := by
          cases mirror
          · exact hpo
          · dsimp only [φPos] at hpo
            change evalM M0.mem _ ε ((Rewriting.emb intNegFormula) ⇜ ![#1, #4]) at hpo
            rw [evalM_subst, evalM_emb] at hpo
            exact (ev_intNeg_iff M0 hpos pos').mp (by
              refine (evalRaw_congr Eq M0.mem intNegFormula ?_ rfl).mp hpo
              funext i; fin_cases i <;> rfl)
        have hg'_eq : g' = if mirror then flipTapeV M0 g else g := by
          cases mirror
          · exact hta
          · dsimp only [φTape] at hta
            simp only [↓reduceIte] at hta ⊢
            rw [evalM_ballMem] at hta
            refine funsV_ext M0 hg' (flipTapeV_mem_funs M0 hg) fun u hu => ?_
            rw [flipTapeV_app M0 hg hu]
            have hu1 := hta u hu
            rw [evalM_all] at hu1
            have hu2 := hu1 (intNegV M0 u)
            rw [evalM_imp] at hu2
            have hneg' : evalM M0.mem (intNegV M0 u :> u :> g' :> pos' :> q' :> g :> pos :> vnNatV M0 q.val :> z :> ![]) ε
                ((Rewriting.emb intNegFormula) ⇜ ![#0, #1]) := by
              rw [evalM_subst, evalM_emb]
              refine (evalRaw_congr Eq M0.mem intNegFormula ?_ rfl).mpr ((ev_intNeg_iff M0 hu _).mpr rfl)
              funext i; fin_cases i <;> rfl
            have hu3 := hu2 hneg'
            rw [evalM_bigAnd] at hu3
            obtain ⟨ac, hac_lt, hac_eq⟩ := (mem_vnNatV_iff M0).mp (zfcAppV_mem_codomain M0 hg (intNegV_mem M0 hu))
            let a : Fin 2 := ⟨ac, hac_lt⟩
            have hmem : (appEqNum (m := 9) 2 1 a.val 🡘 appEqNum 5 0 a.val) ∈
                ((List.finRange 2).map fun a => appEqNum (m := 9) 2 1 a.val 🡘 appEqNum 5 0 a.val) :=
              List.mem_map.mpr ⟨a, List.mem_finRange a, rfl⟩
            have hitem := hu3 _ hmem
            rw [evalM_iff, evalM_appEqNum, evalM_appEqNum] at hitem
            rw [hac_eq]
            exact hitem.mpr hac_eq
        have hinA' : M0.mem (kpairV M0 q' (kpairV M0 pos' g')) A' := by
          dsimp only [φInA'] at hin
          rw [evalM_exs] at hin
          rcases hin with ⟨pg', hpg', h2⟩
          change evalM M0.mem (pg' :> g' :> pos' :> q' :> g :> pos :> vnNatV M0 q.val :> z :> ![]) ε
            ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #2, #1]) at hpg'
          rw [evalM_subst, evalM_emb] at hpg'
          have hpg'_eq : pg' = kpairV M0 pos' g' := (ev_kpair M0 pg' pos' g').mp (by
            refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mp hpg'
            funext i; fin_cases i <;> rfl)
          subst hpg'_eq
          change evalM M0.mem _ ε _ at h2
          rw [evalM_exs] at h2
          rcases h2 with ⟨z', hz', hz'mem⟩
          change evalM M0.mem (z' :> kpairV M0 pos' g' :> g' :> pos' :> q' :> g :> pos :> vnNatV M0 q.val :> z :> ![]) ε
            ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #4, #1]) at hz'
          rw [evalM_subst, evalM_emb] at hz'
          have hz'_eq : z' = kpairV M0 q' (kpairV M0 pos' g') := (ev_kpair M0 z' q' _).mp (by
            refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mp hz'
            funext i; fin_cases i <;> rfl)
          rwa [hz'_eq] at hz'mem
        subst hq'_eq hpos'_eq hg'_eq
        exact ⟨q, pos, g, hpos, hg, hz_eq, hinA'⟩
      · rintro ⟨q, pos, g, hpos, hg, hz_eq, hinA'⟩
        refine ⟨vnNatV M0 q.val, vnNatV_lt_mem M0 q.isLt, ?_⟩
        rw [evalM_bexsMem]; refine ⟨pos, hpos, ?_⟩
        rw [evalM_bexsMem]; refine ⟨g, hg, ?_, ?_⟩
        · exact (evalM_kpair3 M0 (g :> pos :> vnNatV M0 q.val :> z :> ![]) ε 3 2 1 0).mpr hz_eq
        · let pos' := if mirror then intNegV M0 pos else pos
          let g' := if mirror then flipTapeV M0 g else g
          have hpos' : M0.mem pos' (intSetV M0) := by
            dsimp only [pos']; cases mirror; exact hpos; exact intNegV_mem M0 hpos
          have hg' : M0.mem g' F_g := by
            dsimp only [g']; cases mirror; exact hg; exact flipTapeV_mem_funs M0 hg
          change evalM M0.mem (g :> pos :> vnNatV M0 q.val :> z :> ![]) ε _
          rw [evalM_bexsMem]; refine ⟨vnNatV M0 (e q).val, vnNatV_lt_mem M0 (e q).isLt, ?_⟩
          rw [evalM_bexsMem]; refine ⟨pos', hpos', ?_⟩
          rw [evalM_bexsMem]; refine ⟨g', hg', ?_⟩
          rw [evalM_and, evalM_and, evalM_and]
          refine ⟨?_, ?_, ?_, ?_⟩
          · dsimp only [φState]
            rw [evalM_bigAnd]; intro item hitem
            rw [List.mem_map] at hitem; obtain ⟨qf, _, rfl⟩ := hitem
            rw [evalM_imp, evalM_bvarEqNum, evalM_bvarEqNum]
            intro hqeq
            have : q = qf := Fin.ext (vnNatV_inj M0 hqeq)
            subst this; rfl
          · cases mirror
            · rfl
            · dsimp only [φPos, pos']
              change evalM M0.mem _ ε ((Rewriting.emb intNegFormula) ⇜ ![#1, #4])
              rw [evalM_subst, evalM_emb]
              refine (evalRaw_congr Eq M0.mem intNegFormula ?_ rfl).mpr ((ev_intNeg_iff M0 hpos _).mpr rfl)
              funext i; fin_cases i <;> rfl
          · cases mirror
            · rfl
            · dsimp only [φTape, g']
              simp only [↓reduceIte]
              rw [evalM_ballMem]; intro u hu
              rw [evalM_all]; intro u'
              rw [evalM_imp]; intro hneg_raw
              have hu' : u' = intNegV M0 u := (ev_intNeg_iff M0 hu u').mp (by
                change evalM M0.mem _ ε ((Rewriting.emb intNegFormula) ⇜ ![#0, #1]) at hneg_raw
                rw [evalM_subst, evalM_emb] at hneg_raw
                refine (evalRaw_congr Eq M0.mem intNegFormula ?_ rfl).mp hneg_raw
                funext i; fin_cases i <;> rfl)
              subst hu'
              rw [evalM_bigAnd]; intro item hitem
              rw [List.mem_map] at hitem; obtain ⟨a, _, rfl⟩ := hitem
              rw [evalM_iff, evalM_appEqNum, evalM_appEqNum]
              change zfcAppV M0 (flipTapeV M0 g) u = vnNatV M0 a.val ↔
                zfcAppV M0 g (intNegV M0 u) = vnNatV M0 a.val
              rw [flipTapeV_app M0 hg hu]
          · dsimp only [φInA']
            rw [evalM_exs]
            refine ⟨kpairV M0 pos' g', ?_, ?_⟩
            · change evalM M0.mem _ ε ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #2, #1])
              rw [evalM_subst, evalM_emb]
              refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mpr
                ((ev_kpair M0 (kpairV M0 pos' g') pos' g').mpr rfl)
              funext i; fin_cases i <;> rfl
            · change evalM M0.mem _ ε _
              rw [evalM_exs]
              refine ⟨mapCfg q pos g, ?_, hinA'⟩
              change evalM M0.mem _ ε ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #4, #1])
              rw [evalM_subst, evalM_emb]
              refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mpr
                ((ev_kpair M0 (mapCfg q pos g) (vnNatV M0 (e q).val) (kpairV M0 pos' g')).mpr rfl)
              funext i; fin_cases i <;> rfl
    rw [hφ_iff]
    refine ⟨And.right, fun h => ⟨?_, h⟩⟩
    rcases h with ⟨q, pos, g, hpos, hg, rfl, _⟩
    exact (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (Nat.lt_succ_of_lt q.isLt),
      (kpairV_mem_prodV M0).mpr ⟨hpos, hg⟩⟩
  refine ⟨A, ?_, ?_, ?_⟩
  · -- `simCfgV M0 M 0 ∈ A`
    rw [hA_iff]
    refine ⟨0, encodeIntV M0 0, emptyTapeV M0, encodeIntV_mem M0 0, emptyTapeV_mem_funs M0, rfl, ?_⟩
    have hmap0 : mapCfg 0 (encodeIntV M0 0) (emptyTapeV M0) = simCfgV M0 (reindex M e mirror) 0 := by
      dsimp only [mapCfg, simCfgV, Function.iterate_zero, id_eq, extInit, Constant14.stateCode]
      rw [h0]
      cases mirror
      · rfl
      · rw [intNegV_zero]
        have hfl : flipTapeV M0 (emptyTapeV M0) = emptyTapeV M0 := by
          refine funsV_ext M0 (flipTapeV_mem_funs M0 (emptyTapeV_mem_funs M0)) (emptyTapeV_mem_funs M0) fun u hu => ?_
          rw [flipTapeV_app M0 (emptyTapeV_mem_funs M0) hu, emptyTapeV_app M0 (intNegV_mem M0 hu), emptyTapeV_app M0 hu]
        rw [hfl]
        rfl
    rw [hmap0]
    exact hA'0
  · -- Closure under `nextStepV M0 M`
    intro y hy
    obtain ⟨q, pos, g, hpos, hg, rfl, hinA'⟩ := (hA_iff y).mp hy
    obtain ⟨ac, hac_lt, hac_eq⟩ := (mem_vnNatV_iff M0).mp (zfcAppV_mem_codomain M0 hg hpos)
    let a : Fin 2 := ⟨ac, hac_lt⟩
    let pos' := if mirror then intNegV M0 pos else pos
    let g' := if mirror then flipTapeV M0 g else g
    have hpos' : M0.mem pos' (intSetV M0) := by
      dsimp only [pos']; cases mirror; exact hpos; exact intNegV_mem M0 hpos
    have hg' : M0.mem g' F_g := by
      dsimp only [g']; cases mirror; exact hg; exact flipTapeV_mem_funs M0 hg
    have ha'_eq : zfcAppV M0 g' pos' = vnNatV M0 a.val := by
      dsimp only [pos', g']
      cases mirror
      · exact hac_eq
      · simp only [↓reduceIte]
        rw [flipTapeV_app M0 hg (intNegV_mem M0 hpos), intNegV_invol M0 hpos]
        exact hac_eq
    have hstepA' := hA'step _ hinA'
    dsimp only [mapCfg] at hstepA'
    rw [zfcAppV_nextStepV_cfg M0 (reindex M e mirror) (e q).val (Nat.lt_succ_of_lt (e q).isLt)
        pos' g' hpos' hg' a.val a.isLt ha'_eq] at hstepA'
    rw [zfcAppV_nextStepV_cfg M0 M q.val (Nat.lt_succ_of_lt q.isLt) pos g hpos hg a.val a.isLt hac_eq]
    have hlu_M : transLookup M q.val a.val = Constant14.transitionCode M q a := by
      dsimp only [transLookup]; rw [dif_pos q.isLt, dif_pos a.isLt]
    have hlu_M' : transLookup (reindex M e mirror) (e q).val a.val =
        Constant14.transitionCode (reindex M e mirror) (e q) a := by
      dsimp only [transLookup]; rw [dif_pos (e q).isLt, dif_pos a.isLt]
    rw [hlu_M]
    rw [hlu_M'] at hstepA'
    cases hMqa : M q a with
    | none =>
      have htc' : Constant14.transitionCode (reindex M e mirror) (e q) a =
          (n, a.val, Constant14.directionCode none) := by
        rw [Constant14.transitionCode, reindex, Equiv.symm_apply_apply, hMqa]; rfl
      rw [htc'] at hstepA'
      exact (hA'nohalt _ hstepA' (pi1V_kpairV M0 _ _)).elim
    | some out =>
      rcases out with ⟨qNext, ⟨sym, d⟩⟩
      have htc : Constant14.transitionCode M q a =
          (Constant14.stateCode qNext, sym.val, Constant14.directionCode (some d)) := by
        rw [Constant14.transitionCode, hMqa]
      have htc' : Constant14.transitionCode (reindex M e mirror) (e q) a =
          (Constant14.stateCode (qNext.map e), sym.val, Constant14.directionCode (some (orient mirror d))) := by
        rw [Constant14.transitionCode, reindex, Equiv.symm_apply_apply, hMqa]; rfl
      rw [htc]
      rw [htc'] at hstepA'
      cases qNext with
      | none =>
        exact (hA'nohalt _ hstepA' (pi1V_kpairV M0 _ _)).elim
      | some qN =>
        rw [hA_iff]
        have hfl_upd : flipTapeV M0 (updateTapeV M0 g pos (vnNatV M0 sym.val)) =
            updateTapeV M0 (flipTapeV M0 g) (intNegV M0 pos) (vnNatV M0 sym.val) := by
          have hg1 := updateTapeV_mem_funs M0 hg hpos (vnNatV_lt_mem M0 sym.isLt)
          have hg2 := updateTapeV_mem_funs M0 (flipTapeV_mem_funs M0 hg) (intNegV_mem M0 hpos) (vnNatV_lt_mem M0 sym.isLt)
          refine funsV_ext M0 (flipTapeV_mem_funs M0 hg1) hg2 fun u hu => ?_
          rw [flipTapeV_app M0 hg1 hu,
              updateTapeV_app M0 hg hpos (vnNatV_lt_mem M0 sym.isLt) (intNegV_mem M0 hu),
              updateTapeV_app M0 (flipTapeV_mem_funs M0 hg) (intNegV_mem M0 hpos) (vnNatV_lt_mem M0 sym.isLt) hu,
              flipTapeV_app M0 hg hu]
          by_cases h1 : u = intNegV M0 pos
          · have h2 : intNegV M0 u = pos := by rw [h1, intNegV_invol M0 hpos]
            rw [if_pos h2, if_pos h1]
          · have h2 : intNegV M0 u ≠ pos := fun h => h1 (by rw [← h, intNegV_invol M0 hu])
            rw [if_neg h2, if_neg h1]
        cases mirror <;> cases d
        · refine ⟨qN, intPredV M0 pos, updateTapeV M0 g pos (vnNatV M0 sym.val),
            intPredV_mem M0 hpos, updateTapeV_mem_funs M0 hg hpos (vnNatV_lt_mem M0 sym.isLt), rfl, ?_⟩
          simpa [mapCfg, orient, Constant14.directionCode, Constant14.stateCode, pos', g'] using hstepA'
        · refine ⟨qN, intSuccV M0 pos, updateTapeV M0 g pos (vnNatV M0 sym.val),
            intSuccV_mem M0 hpos, updateTapeV_mem_funs M0 hg hpos (vnNatV_lt_mem M0 sym.isLt), rfl, ?_⟩
          simpa [mapCfg, orient, Constant14.directionCode, Constant14.stateCode, pos', g'] using hstepA'
        · refine ⟨qN, intPredV M0 pos, updateTapeV M0 g pos (vnNatV M0 sym.val),
            intPredV_mem M0 hpos, updateTapeV_mem_funs M0 hg hpos (vnNatV_lt_mem M0 sym.isLt), rfl, ?_⟩
          dsimp only [mapCfg]
          rw [intNegV_intPredV M0 hpos, hfl_upd]
          simpa [orient, Constant14.directionCode, Constant14.stateCode, pos', g'] using hstepA'
        · refine ⟨qN, intSuccV M0 pos, updateTapeV M0 g pos (vnNatV M0 sym.val),
            intSuccV_mem M0 hpos, updateTapeV_mem_funs M0 hg hpos (vnNatV_lt_mem M0 sym.isLt), rfl, ?_⟩
          dsimp only [mapCfg]
          rw [intNegV_intSuccV M0 hpos, hfl_upd]
          simpa [orient, Constant14.directionCode, Constant14.stateCode, pos', g'] using hstepA'
  · intro y hy heq
    obtain ⟨q, _, _, _, _, rfl, _⟩ := (hA_iff y).mp hy
    rw [pi1V_kpairV] at heq
    exact Nat.ne_of_lt q.isLt (vnNatV_inj M0 heq)

lemma matches_flip_reindex {n : ℕ} [NeZero n] {M : MachineOf n} {tb : Program n}
    (hm : Matches M tb) : Matches (reindex M (Equiv.refl (Fin n)) true) tb.flip := by
  intro k m hk
  rw [get_flip] at hk
  cases hget : tb.get k with
  | none => rw [hget] at hk; simp at hk
  | some m0 =>
    rw [hget, Option.map_some, Option.some.injEq] at hk
    subst hk
    have hong := hm k m0 hget
    have hc := ongoing_command M k m0 hong
    change ongoing (reindex M (Equiv.refl (Fin n)) true) k = some m0.flip
    have hre : reindex M (Equiv.refl (Fin n)) true k.1 k.2 = m0.flip.command := by
      unfold reindex
      rw [Equiv.refl_symm, Equiv.refl_apply, hc]
      rcases m0 with ⟨qm, wm, dm⟩
      cases dm <;> rfl
    unfold ongoing
    rw [hre]
    rcases m0 with ⟨qm, wm, dm⟩
    cases dm <;> rfl

lemma checkCertificate_invariant {n : ℕ} [NeZero n] {M : MachineOf n} {tb : Program n} {val : ℕ}
    (hm : Matches M tb) (hc : checkCertificate tb val = true) :
    HasNonHaltingInvariant M0 M := by
  unfold checkCertificate at hc
  obtain ⟨hb, hchk⟩ := Bool.and_eq_true_iff.mp hc
  cases hmir : (unpack n val).mirror with
  | false =>
    rw [hmir] at hchk
    exact cert_invariant M0 hm hb hchk
  | true =>
    rw [hmir] at hchk
    exact reindex_invariant M0 (Equiv.refl (Fin n)) rfl true
      (cert_invariant M0 (matches_flip_reindex hm) hb hchk)

/- Bridge 4: Padding `n < 4` (`n = 1, 2, 3`) up to `n = 3` -/

def padTo3 {n : ℕ} [NeZero n] (hn : n ≤ 3) (M : Machine (Fin 2) (Fin n)) : Machine (Fin 2) (Fin 3) :=
  fun q a =>
    if hq : q.val < n then
      (M ⟨q.val, hq⟩ a).map fun (q', stmt) =>
        (q'.map fun r => ⟨r.val, lt_of_lt_of_le r.isLt hn⟩, stmt)
    else none

lemma padTo3_haltsAfter {n : ℕ} [NeZero n] (hn : n ≤ 3) (M : Machine (Fin 2) (Fin n)) (k : ℕ) :
    (padTo3 hn M).HaltsAfter (Machine.init []) k ↔ M.HaltsAfter (Machine.init []) k := by
  let liftCfg : Cfg (Fin 2) (Fin n) → Cfg (Fin 2) (Fin 3) := fun c =>
    ⟨c.q.map fun r => ⟨r.val, lt_of_lt_of_le r.isLt hn⟩, c.tape⟩
  have hstep : ∀ c : Cfg (Fin 2) (Fin n),
      (padTo3 hn M).step (liftCfg c) = (M.step c).map liftCfg := by
    intro ⟨qOpt, T⟩
    cases qOpt with
    | none => rfl
    | some q =>
      simp only [liftCfg, Machine.step, padTo3, dif_pos q.isLt, Option.map_some]
      cases hM : M q T.head with
      | none => rfl
      | some out =>
        rcases out with ⟨q', ⟨sym, d⟩⟩
        rfl
  have hmulti : ∀ j : ℕ, (padTo3 hn M).multiStep (Machine.init []) j =
      (M.multiStep (Machine.init []) j).map liftCfg := by
    intro j
    induction j with
    | zero =>
      simp [Machine.multiStep_zero, Machine.init, liftCfg, Fin.default_eq_zero]
    | succ j ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
      cases hm : M.multiStep (Machine.init []) j with
      | none => rfl
      | some c => exact hstep c
  unfold Machine.HaltsAfter
  rw [hmulti (k + 1)]
  exact Option.map_eq_none_iff

lemma padTo3_invariant {n : ℕ} [NeZero n] (hn : n ≤ 3) (M : Machine (Fin 2) (Fin n))
    (hInv : HasNonHaltingInvariant M0 (padTo3 hn M)) :
    HasNonHaltingInvariant M0 M := by
  obtain ⟨A3, hA3_0, hA3_step, hA3_nohalt⟩ := hInv
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.rel Language.Set.Rel.mem ![#0, &0] ⋏
      (∃¹ ((Rew.subst ![#0, #1] ▹ Rewriting.emb SetTheory.kpair.π₁.dfn) ⋏
           Semiformula.rel Language.Set.Rel.mem ![#0, &1]))
  let ε : ℕ → M0.V := fun k => if k = 0 then A3 else vnNatV M0 n
  obtain ⟨A, hA⟩ := sepV M0 (cfgSetV M0 (n + 1)) φ ε
  have hA_iff : ∀ z : M0.V, M0.mem z A ↔
      M0.mem z (cfgSetV M0 (n + 1)) ∧ M0.mem z A3 ∧ M0.mem (pi1V M0 z) (vnNatV M0 n) := by
    intro z
    rw [hA z]
    refine and_congr Iff.rfl ?_
    dsimp only [φ]
    rw [evalM_and, evalM_exs]
    refine and_congr Iff.rfl ?_
    constructor
    · rintro ⟨s, hs1, hs2⟩
      change evalM M0.mem (s :> z :> ![]) ε
        ((Rewriting.emb SetTheory.kpair.π₁.dfn) ⇜ ![#0, #1]) at hs1
      rw [evalM_subst, evalM_emb] at hs1
      have hseq : s = pi1V M0 z := (ev_pi1 M0 s z).mp (by
        refine (evalRaw_congr Eq M0.mem SetTheory.kpair.π₁.dfn ?_ rfl).mp hs1
        funext i; fin_cases i <;> rfl)
      rwa [hseq] at hs2
    · intro hmem
      refine ⟨pi1V M0 z, ?_, hmem⟩
      change evalM M0.mem (pi1V M0 z :> z :> ![]) ε
        ((Rewriting.emb SetTheory.kpair.π₁.dfn) ⇜ ![#0, #1])
      rw [evalM_subst, evalM_emb]
      refine (evalRaw_congr Eq M0.mem SetTheory.kpair.π₁.dfn ?_ rfl).mpr ((ev_pi1 M0 _ z).mpr rfl)
      funext i; fin_cases i <;> rfl
  refine ⟨A, ?_, ?_, ?_⟩
  · rw [hA_iff]
    refine ⟨simCfgV_mem M0 M 0, hA3_0, ?_⟩
    dsimp only [simCfgV, Function.iterate_zero, id_eq, extInit, Constant14.stateCode]
    rw [pi1V_kpairV]
    exact vnNatV_lt_mem M0 (Nat.pos_of_ne_zero (NeZero.ne n))
  · intro y hy
    obtain ⟨hycfg, hyA3, hypi⟩ := (hA_iff y).mp hy
    obtain ⟨s, _, p_tail, hp_tail, rfl⟩ := (mem_prodV M0).mp hycfg
    obtain ⟨pos, hpos, g, hg, rfl⟩ := (mem_prodV M0).mp hp_tail
    rw [pi1V_kpairV] at hypi
    obtain ⟨qCode, hq, rfl⟩ := (mem_vnNatV_iff M0).mp hypi
    obtain ⟨symCode, hsym_lt, hsym⟩ := (mem_vnNatV_iff M0).mp (zfcAppV_mem_codomain M0 hg hpos)
    have hstep3 := hA3_step _ hyA3
    rw [zfcAppV_nextStepV_cfg M0 (padTo3 hn M) qCode (by omega) pos g hpos hg symCode hsym_lt hsym] at hstep3
    rw [zfcAppV_nextStepV_cfg M0 M qCode (Nat.lt_succ_of_lt hq) pos g hpos hg symCode hsym_lt hsym]
    have hlu_M : transLookup M qCode symCode = Constant14.transitionCode M ⟨qCode, hq⟩ ⟨symCode, hsym_lt⟩ := by
      dsimp only [transLookup]; rw [dif_pos hq, dif_pos hsym_lt]
    have hlu_3 : transLookup (padTo3 hn M) qCode symCode =
        Constant14.transitionCode (padTo3 hn M) ⟨qCode, lt_of_lt_of_le hq hn⟩ ⟨symCode, hsym_lt⟩ := by
      dsimp only [transLookup]; rw [dif_pos (lt_of_lt_of_le hq hn), dif_pos hsym_lt]
    rw [hlu_M]
    rw [hlu_3] at hstep3
    cases hMqa : M ⟨qCode, hq⟩ ⟨symCode, hsym_lt⟩ with
    | none =>
      have htc3 : Constant14.transitionCode (padTo3 hn M) ⟨qCode, lt_of_lt_of_le hq hn⟩ ⟨symCode, hsym_lt⟩ =
          (3, symCode, Constant14.directionCode none) := by
        rw [Constant14.transitionCode, padTo3, dif_pos hq, hMqa]; rfl
      rw [htc3] at hstep3
      exact (hA3_nohalt _ hstep3 (pi1V_kpairV M0 _ _)).elim
    | some out =>
      rcases out with ⟨qNext, ⟨sym, d⟩⟩
      have htcM : Constant14.transitionCode M ⟨qCode, hq⟩ ⟨symCode, hsym_lt⟩ =
          (Constant14.stateCode qNext, sym.val, Constant14.directionCode (some d)) := by
        rw [Constant14.transitionCode, hMqa]
      have htc3 : Constant14.transitionCode (padTo3 hn M) ⟨qCode, lt_of_lt_of_le hq hn⟩ ⟨symCode, hsym_lt⟩ =
          (Constant14.stateCode (qNext.map fun r => ⟨r.val, lt_of_lt_of_le r.isLt hn⟩),
           sym.val, Constant14.directionCode (some d)) := by
        rw [Constant14.transitionCode, padTo3, dif_pos hq, hMqa]; rfl
      rw [htcM]
      rw [htc3] at hstep3
      cases qNext with
      | none =>
        exact (hA3_nohalt _ hstep3 (pi1V_kpairV M0 _ _)).elim
      | some qN =>
        rw [hA_iff]
        refine ⟨?_, hstep3, ?_⟩
        · refine (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (Nat.lt_succ_of_lt qN.isLt),
            (kpairV_mem_prodV M0).mpr ⟨?_, updateTapeV_mem_funs M0 hg hpos (vnNatV_lt_mem M0 sym.isLt)⟩⟩
          cases d <;> simp [Constant14.directionCode, intPredV_mem M0 hpos, intSuccV_mem M0 hpos]
        · rw [pi1V_kpairV]
          exact vnNatV_lt_mem M0 qN.isLt
  · intro y hy heq
    have hmem := ((hA_iff y).mp hy).2.2
    rw [heq] at hmem
    exact irreflV M0 _ hmem

end Bridges

end C14H2



namespace BeaverBound

open Turing Turing.BusyBeaver

def Upper [NeZero n] (M : MachineOf n) (limit : ℕ) : Prop :=
  M.HaltsAfter (Machine.init []) limit ∨ ∀ M0 : C14Stage2.ZFCModel, C14H2.HasNonHaltingInvariant M0 M

abbrev TreeBound [NeZero n] (limit : ℕ) (tb : Program n) : Prop :=
  ∀ M : MachineOf n, Matches M tb → Upper M limit

theorem branch_bound [NeZero n] {limit : ℕ} {tb : Program n} {k : Key n}
    (h : firstMissing tb limit (start n) = some k)
    (children : ∀ m, TreeBound limit ((k, m) :: tb)) : TreeBound limit tb := by
  intro M hm
  cases hs : ongoing M k with
  | none =>
    left
    simpa only [view_start] using firstMissing_stops hm limit (start n) h hs
  | some m => exact children m M (matches_add hm hs)

theorem subtree_bound [NeZero n] {limit fuel : ℕ} {tb : Program n} {a b : List ℕ}
    (hCount : (holes tb).card ≤ fuel) (h : checkTree limit fuel tb a = some b) :
    TreeBound limit tb := by
  induction fuel generalizing tb a b with
  | zero =>
    intro M hm
    exact Or.inr fun M0 => C14H2.no_holes_invariant M0 hm (by omega)
  | succ fuel ih =>
    rw [checkTree.eq_def] at h
    cases hFirst : firstMissing tb limit (start n) with
    | none =>
      simp only [hFirst] at h
      intro M hm
      cases a with
      | nil => contradiction
      | cons v rest =>
        by_cases hc : checkCertificate tb v = true
        · exact Or.inr fun M0 => C14H2.checkCertificate_invariant M0 hm hc
        · simp [hc] at h
    | some k =>
      simp only [hFirst] at h
      apply branch_bound hFirst
      intro m
      obtain ⟨x, y, hy⟩ := succeeds_each h (mem_moves m)
      refine ih ?_ hy
      rw [holes_add, Finset.card_erase_of_mem (missing_is_hole hFirst)]
      omega

theorem upper_of_reindex {n : ℕ} [NeZero n] {M : MachineOf n} (e : Fin n ≃ Fin n) (h0 : e 0 = 0)
    (mirror : Bool) {limit : ℕ} (h : Upper (reindex M e mirror) limit) : Upper M limit := by
  rcases h with h | h
  · exact Or.inl ((reindex_haltsAfter M e h0 mirror limit).mp h)
  · exact Or.inr fun M0 => C14H2.reindex_invariant M0 e h0 mirror (h M0)

theorem canonical_start {n : ℕ} (hn : 1 < n) [NeZero n] {limit : ℕ} (hl : 1 ≤ limit)
    (same : ∀ a, TreeBound (n := n) limit [((0, 0), ⟨0, a, false⟩)])
    (other : ∀ a, TreeBound (n := n) limit [((0, 0), ⟨1, a, false⟩)]) :
    TreeBound (n := n) limit [] := by
  intro M _
  cases h : ongoing M (0, 0) with
  | none =>
    left
    rw [← view_start n]
    exact Machine.multiStep_eq_none_mono (step_stop M (start n) h) (by omega)
  | some m =>
    by_cases hs : m.state = 0
    · apply upper_of_reindex (Equiv.refl (Fin n)) rfl m.left
      apply same m.write
      apply matches_add (matches_empty _)
      simpa [hs] using first_reindex (Equiv.refl (Fin n)) rfl m h
    · let e := Equiv.swap m.state (1 : Fin n)
      have h1 : (0 : Fin n) ≠ 1 := by
        intro he
        have hval := congrArg Fin.val he
        change 0 = 1 % n at hval
        rw [Nat.mod_eq_of_lt hn] at hval
        omega
      have h0 : e 0 = 0 := Equiv.swap_apply_of_ne_of_ne (Ne.symm hs) h1
      have he : e m.state = 1 := Equiv.swap_apply_left _ _
      apply upper_of_reindex e h0 m.left
      apply other m.write
      apply matches_add (matches_empty _)
      simpa [he] using first_reindex e h0 m h

end BeaverBound


namespace BeaverBound

-- Each integer packs one DFA, an NFA edge set, and its states reachable on blank input.
-- They follow the enumeration order of `moves` within each checked subtree.

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound0 : TreeBound (n := 3) 21 [((0, 0), ⟨0, 0, false⟩)] := by
  refine subtree_bound (fuel := 5) (b := []) (a := List.flatten [
    [2290647312]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound2 : TreeBound (n := 3) 21 [((0, 0), ⟨0, 1, false⟩)] := by
  refine subtree_bound (fuel := 5) (b := []) (a := List.flatten [
    [2290647312]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_0 : TreeBound (n := 3) 21 [((1, 0), ⟨0, 0, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2290188848]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_1 : TreeBound (n := 3) 21 [((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [159704012627178225784091378386]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_2 : TreeBound (n := 3) 21 [((1, 0), ⟨0, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2290188848]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_0 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 0, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012046070326013221470930]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_1 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 0, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282848273]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_2 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 1, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012055294265398076179410]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_3 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 1, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282848273]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_4 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 0, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2281799697]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_5 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 0, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2283897105]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_6 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 1, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2283999792, 2283938352, 2283999792, 2283938352, 2283938352, 2283938352, 2283938352, 2283938352, 404963888, 159695549625865372387489416914, 404963888, 673333808],
    [673333808, 673333808, 673333808, 673333808, 3050680171447260652985726214423479955031365085804317754492676, 3053839722287363361602897585282638441664996641959855193033316, 3050697627545928250880797138877184920351970549054258958272260, 3053839722287363361602897585282638441664996641959855193033316, 3053839722287363276929755659611678701146566325498107600013924, 3050860551133492522597953663223605947787070200094719071455940, 3053653526920307254404740393435843253237768957088922679610052, 3053653526920307254404740393435843253237768957088922679610052],
    [404963888, 404963888, 673333808, 673333808, 673333808, 673333808, 673333808, 3050680171447260652985726214346470181067500149663360419858180, 3053839722287363276929755659611678701146566325498107600013924, 3053653526920307254404740393435843253237768957088922679610052, 3053653526920307254404740393435843253237768957088922679610052]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_7 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 1, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2283897105]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_8 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 0, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485340580985765381026155218, 159703955516031622350299531986, 158504684574691220165232757714, 159703955516031622350299531986, 158543372562102129733645961938, 159703936776445486471682525938, 2185564784, 2185564784, 2185503344, 2185503344, 2185503344, 3050860551133492523756725887911399053310083377520570729715396],
    [6247881234161990097237510898, 303136785, 14895868032962298724213722925458677432849742225741416521508, 303136785, 34701329, 571572241, 571572241, 303136785, 1110540561, 154751949788890356886012115, 1110540561, 158775500486567587144125188818],
    [159703936776445486471682525938, 159085004385854863691430828754, 159703936776445486471682525938]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_9 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 0, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485341023700814974056202962, 2168553745, 158504685017406269758262805202, 2168553745, 2151776273, 2185331249, 158620748975097665830317523666, 158620748975025040853917827794, 158620748975170290806717219794, 158620748975025040853917827794, 158620748975025040991365169874, 159703941344464539276651070419],
    [159703946066831022284817434067, 159703955511563988301150161107, 2185331249, 158775500929289444913154427602, 2218886225, 159085004828585799028458984146, 2218886225]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_10 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 1, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485340728568795538701488850, 2269450864, 158466034366221248922889818770, 2269450864, 3053653524079148749976080743356061908917308212314373924727812, 2219057776, 158466034509183515494071734994, 2219057776, 159085004533437892199738053330, 3055143109744870393947697063814042181976210286003047097053028, 158466034513795202612077859538, 158504684722274250322908091346],
    [2235896432, 2235896432, 2219057776, 158466034509183515494071734994, 2219057776, 3055143109744870393947697063814042181976210286003047097053028, 158543372709685159891321295570, 158466072292727066668818305746, 2185564784, 158543377284477688109638685330, 2185564784, 2185503344],
    [2185503344, 2185503344, 2495451045645141610984444626, 4990826233648808773636133842, 33652753, 570523665, 570523665, 1111589425, 33652753, 1111589425, 158775500634150617301800524498, 2553445247829643006442541778],
    [3053653524077069854995521669952512700416178443489035628194820, 5029476442127855384887628498, 3053653524077069854995521669952512700416178443489035628194820, 67207185, 606175505, 606175505, 1145144401, 1145144401, 67207185, 1145144401, 159085004533437893849106158290, 67207185],
    [606175505, 20427267097470966395471729362, 606175505, 1145144401, 1145144401, 67207185, 1145144401]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_11 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 1, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2151743505, 2151747601, 2151743505, 2151747601, 2151743505, 2168529169, 2168529169, 158485341023707621500687289042, 2151759889, 158485341023716699618475578066, 2151759889, 2168553745],
    [2151743505, 2168525073, 2151743505, 2168525073, 2151743505, 159085042307902051980327522515, 159085042307902052117774864595, 158504685017413076284893891538, 158504685017422154402682180562, 2168553745, 2151776273, 2185331249],
    [2495449860585818121020915923, 4990823867997864566529753555, 10058876731448176006091834066, 9981571882821957457547428819, 19963001508641025519872180946, 19963067912470143239582778835, 154751954255326492311487186, 2185331249, 2785535688493554851114975954, 272728081, 5261566882792334577559995346, 272728081],
    [4292625, 557941009, 557941009, 4292625, 1078034449, 4292625, 1078034449, 2218886225, 3095039587780831398420611794, 5571070782079611124865631186, 4292625, 641828465],
    [641828465, 4292625, 1145144401, 4292625, 1145144401, 2218886225]
  ]) (by decide) ?_
  decide +kernel

theorem bound4_3 : TreeBound (n := 3) 21 [((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  apply branch_bound (k := (1, 1)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound4_3_0
  · exact bound4_3_1
  · exact bound4_3_2
  · exact bound4_3_3
  · exact bound4_3_4
  · exact bound4_3_5
  · exact bound4_3_6
  · exact bound4_3_7
  · exact bound4_3_8
  · exact bound4_3_9
  · exact bound4_3_10
  · exact bound4_3_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_4 : TreeBound (n := 3) 21 [((1, 0), ⟨1, 0, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2290254384]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_5 : TreeBound (n := 3) 21 [((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [159704012622854787750107874003]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_6 : TreeBound (n := 3) 21 [((1, 0), ⟨1, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2290254384]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_7 : TreeBound (n := 3) 21 [((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [159704012623143035718445696211]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_8 : TreeBound (n := 3) 21 [((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2172945008, 159703955955321737203272452818, 2172945008, 159703937665339522273186482898, 159703955955294715605508229842, 159703938855155077977405983698, 159703937065819776927672634066, 159703941234786189385844984530, 159703936475523966568966982354, 159703945994048412202722987730, 3713973005624580752996895442, 287342609],
    [6190005380514976798806707154, 287342609, 18907153, 555778065, 555778065, 555778065, 18907153, 1092714769, 1092714769, 159703955512572857836478991058, 159703937066972698433353222898, 2235830896],
    [2235830896, 2219057776, 2219057776, 3055143109744870393945113044898275107605770863286671532751716, 159703937066972698433353222898, 2189722224, 159703937065855805724691598034, 2189722224, 3713973005660046600062438098, 159696702400404049428224215762, 6190005380549879695918828498, 159694417374510057068435671762],
    [303071249, 159694569680053064601302010834, 303071249, 302022673, 304119825, 302022673, 304119825, 302022673, 306348593, 306348593, 11142070130329545887631608530, 159694265659298888691293948626],
    [21046199629888878271057170130, 159694265659298888691293948626, 40854458629007543037908290258, 39771251649323373637511808211, 1528316348414892512998655757759130083550712739943293937383428, 1528316347704602717255836939511838435421052844983710234310660, 1176797808, 1145340528, 1176797808, 1145340528, 1145340528, 1145340528],
    [1145340528, 1145340528, 79387750758094771692633195731, 2223276656, 159703937067008727230372186866, 2223276656, 159703937067008727230372186866]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_9 : TreeBound (n := 3) 21 [((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [158485341023734591971261481682, 158485341020275880250105151699, 158504685017440046755468083922, 159742623304825734934271427314, 2165604625, 2165575953, 2165575953, 2164523281, 2165575953, 2165575953, 8958981238197476326177311459650582757774936292054758434283186835648059974856032567611673620261429556119, 158504684445556075649097073362],
    [3050697627529280836437818341828927773679386267588896812271493, 3053676798866273260618420510516936884203303227905978818533220, 2165604625, 2165604625, 2166654289, 158495013017092578828009636307, 5981623143433830939434399677984267768645028962894905719013, 23856668179054075492061040271873456372226058572569417201893, 3050694718196161159420863503080851207770698652064827901065445, 556041553, 17072401, 556041553],
    [38687988563903640921735635, 1095008529, 1095008529, 2166654289, 160322925685554108087712942834, 2168750353, 158485377326908916866400453330, 158466034513795060775010763474, 158504720140022755365604099026, 159085004533437891787396027090, 3050697627545928253359196942881244284563626915295265019495653, 159085004533437891924843369170],
    [3050697627545928253359196942881357091957288309608350933157093, 3050697627545928253359196942881507501815503501767119111567589, 2168750353, 158543373004850938731695243986, 158543373001392244602725010131, 310542896, 3713973005660046616168513747, 310542896, 26835839488300807337387739821800008747893408452382855642181, 6190004799441975526465503699, 6190004808665910512736829907, 3714124711648405889229029779],
    [321161073, 26812567553433089599985534414923663508030319675784564422885, 321161073, 4952064750932660264221311443, 289702161, 289702161, 578847280, 11142070130329545903737735891, 578847280, 21046199629888878287163362515, 1115849264, 41976368],
    [1115849264, 1529805933370324362550148102619764485567804507535465817552357, 572555824, 33587760, 572555824, 33587760, 1111654960, 33587760, 1111654960, 33587760, 158620748976214063739551485139, 158775500929316466510918650578],
    [158775500925857702013204433107, 159085004828603813426968466130, 159085004825144978560510333139]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_0 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 0, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2172945008]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_1 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 0, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2256802416, 2223260272, 2256802416, 2249462384, 3053653524079148751297805313372474709249493474381092719832068, 2249462384, 2214855280, 2216960624, 158466034216323438925423121106, 2216960624, 3053653524789438544725343222521133569106038278788715618642948, 158466034806619249284128772818],
    [3053653524079148749974788732512002587267006733596985914174468, 2223252080, 158504683837424884884342637299, 2223252080, 8937519721047441111971469767762683617669072291103255702532, 2495375778912002547126502611, 26812564756667685664598110361647171917663440230908156587012, 4971406973210214925571589331, 50645958803416650955381406986689559728533564889996737784836, 19344584037329416377860307, 39635843693961648976106375379, 79252342803885968535834874067],
    [2223260272, 158504683839154320740859265267, 2223260272, 9846900276336116950148240501331878857130117043231548705533727530623256423716594224680430843978036118, 1149518448, 28488331583649437303561323983938858658879263065636955106980, 4971406974939703560282063059, 195135768378416116076839798094529310940389706175228257644388, 1149518448, 1149518448, 1149518448, 75760240]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_2 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 1, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2172945008]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_3 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 1, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485416578139674352271037074, 6703141183623034106236804573401788395184386084808455758308, 4911852627085829982982802, 6004914966423947491604479631023558303322416986378669547172, 9747555905544346681807506, 9981572178996813231684653714, 9982176641906620546272006802, 79852044387687036165094970066, 158485417758731295069684437650, 2165576304, 2165576304, 2147746416],
    [2183406192, 2147746416, 2183406192, 158465997027687386326967063250, 158465997027687386326967063250, 2165580400, 2219057776, 2165580400, 2147754608, 2183406192, 2147754608, 2183406192],
    [2219057776, 158465997027687386464414405330, 2219057776, 158465997027687386464414405330, 3050685990146816524957035741105552240037675442821619309476677, 2165580400, 2219057776, 2165580400, 2147754608, 2183406192, 2147754608, 2183406192],
    [2219057776, 2219057776, 8937519682205500062692281747914145115459207741252656049156, 2514719772617457331333104851, 4990750966915669709778191571, 2495451337352295025658106514, 159080206901951373208849552082, 2514946446785201638511547282, 9981576901363296513613173394, 158456401179030224554701165266, 19963068209797920929536349906, 40238000908333808271088489106],
    [3053653524084697215598282447022820993802056430741563221355956, 3055143109744870396591147469271473556869211477811479234621284, 3053676798866273260616966998471390246091270498546184472120772, 3053653524079148073912669908004195146242993267863691595754932, 3050685990146816522353472506177019747911097295210500449690533, 3053653524079148073912672431460468394169290773666312462675812, 3055143109744870393945113045822392688941124263332657622822756, 3053653524079148073912672431460468394169290773666312462675812, 2495451337352295025691660946, 14621038115866370298155666, 2495603633671367571749802642, 9747555905544896437621394],
    [9981576901363296513646727826, 9982186086639586697879294610, 79852044387687036165094970066, 3053653524084697215598282447022820993802056430741530606448052, 3053653524079148073912669908004195146242993267863691595754932, 3053653524123541225919820016393724369953905202612443582180788, 3050685990146816522352826501371067691545800928382299783908261, 3053653524079148073912672431460468394169290773666312462675812, 3053653524079148073912672431460468394169290773666312462675812]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_4 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 0, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2189722224]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_5 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 0, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2182382192, 158620743685565862469043224819, 2182382192, 3053653524079150783453214052931180090758955840472215494470660, 2216985200, 2147779184, 2216985200, 8937519721049515603948648703874471186427708029829922040836, 26812564756669760156575289297773060397182061004316365171716, 606372464, 295536, 606372464],
    [295536, 1078231664, 295536, 1078231664, 295536, 2151973488, 158620743964437261619044616947, 2151973488, 3050720902477331076633197446979553959497762221606235925484357]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_6 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 1, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2189722224]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_7 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 1, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485415997031770183354618514, 159085079801900869558976189074, 158504759990737224967563318162, 158485415997031770183354618514, 158543447978148134639059931794, 158466072004479237006831981266, 158620814509389909678650103506, 159085079801900869009220375186, 8937519682202795814222030629832515730812891305469258116100, 26812564734470473330785098339685802925671854852607958739140, 34701329, 571572241],
    [571572241, 154751958867579857664999635, 1108705905, 1108705905, 158485415997032333133308039826, 158466109782258741271968420498, 158485417177623953850721440402, 158466074364510119749566403218, 158543447978148697589013353106, 158543447978148697589147570834, 158543452700515180458666955410, 158466072003326878314873819794],
    [159085042033345863093229523666, 3053653524079150783453214052931180090758955840472215494470660, 158543448005819941661194654354, 158466071995255304081742303954, 158543452728188676330653553298, 572818032, 295536, 572818032, 295536, 1145340528, 295536, 1145340528],
    [295536, 289702512, 159080206459202495491424195282, 289702512, 574915184, 4489840, 574915184, 4489840, 1145340528, 4489840, 1145340528, 4489840],
    [5981640212585498775733989137177765717007814094657655022004, 11928334078434182738169146862625978366252259656396696331972, 574915184, 295536, 574915184, 295536, 1145340528, 295536, 1145340528, 295536, 289702512, 289702512],
    [574915184, 4489840, 574915184, 4489840, 1145340528, 4489840, 1145340528, 4489840, 570720880, 295536, 570720880, 295536],
    [1145340528, 295536, 1145340528, 295536]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_8 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 0, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2223276656]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_9 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 0, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [377782896, 5570900777065241520885465331, 377782896, 3053653524120775462334439288950172144301665225462974566509572, 3053653524077069856317248763425198748674591171376970424265732, 3053653524120780881431026662020312097588409885301707904003076, 3053653524076376213938593666922402782834346021927087435033604, 3053653524786710037110519972444903836539136328760239806360580, 3053653524076373504398052045451691086244680955156669423038356, 4578989245775683749876456372929704170396626396564694831607652, 3053653524076373504398049521995417838318453489302055756377956, 3053653524077069854994229659108453378765876964771647617641476],
    [3053653524076373504398049521995417838318453489302055756377956, 612663920, 20426634596104519066130121459, 612663920, 605258545, 605258545, 606372464, 295536, 606372464, 295536, 4489840, 295536],
    [4489840, 295536, 1082425968, 8684144, 1082425968, 8684144]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_10 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 1, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2223276656]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_11 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 1, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [293868144, 3095040764949288688940028562, 293868144, 2553483318468658965935886994, 2476031786936037480968819410, 2630849849710434005526058706, 2495375780641492265177518802, 360989296, 2476031786936035419384517330, 360989296, 277086832, 50645958138172289331884133953976609518745399023436710161412],
    [1149518448, 50645958138172289331884133953976609532193088277878676532228, 1149510256, 3095039583492839557606424787, 1149510256, 3095039583781070071205594323, 1149518448, 1149518448, 1149518448, 1149518448, 293868144, 2476221861034049280625676946],
    [293868144, 2553634434196110794582725266, 2553639156562593664236327570, 360989296, 2553673393719594469357064850, 360989296, 277086832, 3053653524076376213938593666922402782834346021927087435033604, 3053653524120812718553062887806151880744552504466398593821700, 3053653524076373504398052045451691086244680955156669423038356, 4580478831796550630410757798047428647346881850614839273192292, 3053653524076373504398049521995417838318453489302055756377956],
    [3053653524076373504398049521995417838318453489302055756377956, 9923544339139029641445053074, 68190225, 9942888332845047375605076882, 68190225, 572818032, 537166448, 572818032, 572818032, 642024048, 644121200, 642024048],
    [537166448, 3053653524076373504398052045454097641681051734411073320529812, 9924148802048836956032406162, 9924149982641020623397130898, 572818032, 537166448, 572818032, 572818032, 642024048, 644121200, 642024048, 537166448],
    [605258545, 605258545, 572818032, 295536, 572818032, 295536, 4489840, 295536, 4489840, 295536, 1149534832, 8684144],
    [1149534832, 8684144]
  ]) (by decide) ?_
  decide +kernel

theorem bound4_10 : TreeBound (n := 3) 21 [((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  apply branch_bound (k := (2, 0)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound4_10_0
  · exact bound4_10_1
  · exact bound4_10_2
  · exact bound4_10_3
  · exact bound4_10_4
  · exact bound4_10_5
  · exact bound4_10_6
  · exact bound4_10_7
  · exact bound4_10_8
  · exact bound4_10_9
  · exact bound4_10_10
  · exact bound4_10_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_0 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 0, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485341023734576612326310610, 158485341023734572179917963986, 158485341023734581044734657490, 2147749905, 2148798481, 2148798481, 2148798481, 2147749905, 2216957009, 2216957009, 158485340580985765380925491922, 2151944209],
    [158485340728568795538634379986, 2151944209, 158485341023734589909551350482, 159085080384161694286474645715, 293741104, 293741104, 3241364592738876689668717491911948658807399956551759338900068, 1099309680, 1099309680, 159085080384161694423921987795, 158485341023734643098451512018, 158485341023734591971135652562],
    [158485341023734714016985060050, 158485341023734574378941219538]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_1 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 0, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485341021428872123456176339]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_2 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 1, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158504685017440031396532912850, 158504685017440026964124566226, 158504685017440035828941259730, 2165575953, 2165575953, 2165575953, 2165575953, 2165575953, 158504760019561951474470654419, 158504760056457691421703442899, 2168721681, 2168721681],
    [158504685017440044693757952722, 158504684436332140524975751890, 2199135089, 2147754001, 2199135089, 2147754001, 158543448006972861111607562963, 158620824018690420195666826451, 158504684574691156462286210002, 158504684722274116251217363922, 159085042310063911742860693715, 293741104],
    [293741104, 1099309680, 1099309680, 159085042310063911880308035795, 2199135089, 2147754001, 2199135089, 2147754001, 158543448006972861249054905043, 158620824018690420333114168531, 159085042310063911880308035795, 158504685017440097882658114514],
    [293741104, 38688577742748725220016850, 293741104, 9942813359547284257427751634, 9981572180149735164680934099, 19963068209797920945642542291, 1099379312, 39293045264242058234757842, 1099379312, 38688577742748725220016850, 158504685017440168801191662546, 293601840],
    [25166384, 293601840, 9981572180149735714470302419, 19963068209797921495431910611, 1099186800, 1099186800, 25166384]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_3 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 1, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2165575953, 2165575953, 2165571857, 2165575953, 2165575953, 2169774353, 2169774353, 159742623306555168868127542002, 2165588241, 2165588241, 2165604625, 2165575953],
    [2165575953, 2164523281, 2165575953, 2165575953, 8960074863559867832139023426366177812645257346669697714717288355231900294110884692019169045496073813910, 3050697627545928250714127742383317692580689674579078557161285, 2165604625, 2165604625, 2166654289, 38990221171799171566436819, 556041553, 17072401],
    [556041553, 38687989716895514272760275, 1095008529, 1095008529, 2166654289, 6808840521175695003635221234, 286556433, 286556433, 286556433, 559186193, 38687989716895514272760275, 559186193],
    [286556433, 1091862801, 1091862801, 2168750353, 6703161066186141738249088944619590669939822565119492541316, 190690421844868311049895619043389048692922716731969920784197, 1525360451171382217996144957516649557037403372106078913517381, 2168750353]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_4 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 0, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158543372423743038960825336530, 2148827153, 158543372432966978345680045010, 2148827153, 2147778577, 2216985681, 572686896, 572686896, 572686896, 572686896, 1109820016, 572686896],
    [1109820016, 572686896, 2216985681, 158543372562102129733645961938, 2151972881, 158543372709685159891321295570, 2151972881]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_5 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 0, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158543373002545236476076036819]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_6 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 1, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158620748398564858097651745490, 158620748426236674087420232402, 158620748389340916513639563986, 158620748426236674121782067922, 158620748389340916513639563986, 158620748389340916651086906066, 158543443256934573274021565139, 158620814509389909679723910355, 159085042024121928113937977555, 158620748407788797482506453970, 158620748398564292982902686418, 158620748389340916513639563986],
    [158620748407787669452165809106, 158620748389340916513639563986, 158620748389340916651086906066, 158543443266158508259756020435, 158620748389340916788534248146, 158620814518613844664384623827, 159085042033345863092156240083, 158620748426236676252215870162, 158543443284606380303672480467, 572686896, 572686896, 572686896],
    [572686896, 1109820016, 572686896, 1109820016, 572686896, 158620814573957456518086530259, 2476032377195819041715912915, 4952064752085652137572303059, 574915184, 574915184, 574915184, 38044272],
    [1111786096, 1648788080, 1111786096, 1111786096, 2630783185483073407380685522, 289702161, 5106814379781285785825772242, 289702161, 570458672, 33587760, 570458672, 33587760],
    [1114014320, 33587760, 1114014320, 33587760, 574915184, 574915184, 574915184, 38044272, 1111786096, 1648788080, 1111786096, 1111786096],
    [289702161, 289702161, 570458672, 33587760, 570458672, 33587760, 1111786096, 33587760, 1111786096, 33587760]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_7 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 1, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158620748977367055612902511827]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_8 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 0, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2785535688529020698180518610, 158765829522759479108776821458, 5261566882827237474672116690, 158765980057379031166553752274, 269778961, 158766131182330422380055299026, 269778961, 268730385, 337937489, 337937489, 268730385, 272924689],
    [158770664930872158785101699794, 272924689, 10213629271423671027655312082, 10523133168405227727156154579, 605258288, 605258288, 606241328, 606241328, 606241328, 604144176, 608600688, 610697840],
    [608600688, 606241328, 20427257945598077240936501459, 1149534832, 1149534832, 1149534832, 75530800]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_9 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 0, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158775500927010693886555457747]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_10 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 1, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3095039587816297245486154450, 10523133170710945410165310162, 75498032, 10523133170710945444527145682, 75506224, 2553478597255097617003647699, 75506224, 2630849849710434021632251091, 1149518448, 1149518448, 1149518448, 75498032],
    [5571070782114514021977752530, 3104559878717817879479255762, 628679800074995303234732754, 5580439957360640455723779026, 5029509791553309995448734419, 5106881044008646400077337811, 628679800074996402813469394, 5571073140992043305509851347, 10523133170710947574960947922, 10523132585063414981655069394, 9923543159700330427835236563, 10523132594359407562501194450],
    [9942885982038099481170313683, 69239344, 67142192, 69239344, 67142192, 1145340528, 1145340528, 1145340528, 67142192, 605258288, 605258288, 606241328],
    [606241328, 606241328, 604144176, 608600688, 610697840, 608600688, 606241328, 19827667936893179941615583443, 19847010759230948994950660563, 606241328, 67142192, 606241328],
    [67142192, 71336496, 71336496, 71336496, 67142192, 1149534832, 1149534832, 1149534832, 75530800]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_11 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 1, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159085004826297970433861357779]
  ]) (by decide) ?_
  decide +kernel

theorem bound4_11 : TreeBound (n := 3) 21 [((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  apply branch_bound (k := (2, 0)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound4_11_0
  · exact bound4_11_1
  · exact bound4_11_2
  · exact bound4_11_3
  · exact bound4_11_4
  · exact bound4_11_5
  · exact bound4_11_6
  · exact bound4_11_7
  · exact bound4_11_8
  · exact bound4_11_9
  · exact bound4_11_10
  · exact bound4_11_11

theorem bound4 : TreeBound (n := 3) 21 [((0, 0), ⟨1, 0, false⟩)] := by
  apply branch_bound (k := (1, 0)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound4_0
  · exact bound4_1
  · exact bound4_2
  · exact bound4_3
  · exact bound4_4
  · exact bound4_5
  · exact bound4_6
  · exact bound4_7
  · exact bound4_8
  · exact bound4_9
  · exact bound4_10
  · exact bound4_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_0 : TreeBound (n := 3) 21 [((1, 0), ⟨0, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2290188848]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_0 : TreeBound (n := 3) 21 [((0, 1), ⟨0, 0, false⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2290225712]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_1 : TreeBound (n := 3) 21 [((0, 1), ⟨0, 0, true⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2290090544]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_2 : TreeBound (n := 3) 21 [((0, 1), ⟨0, 1, false⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2290225712]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_3 : TreeBound (n := 3) 21 [((0, 1), ⟨0, 1, true⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282885680, 2281701936, 2282885680, 2281701936, 2283807280, 2281701936, 2283807280, 2281701936, 3050680171447260653151103602391104359050785815225183591271812, 3053653526920307593262523983266054800177665146928097255283076, 3053676798855174985203251820166199406119649137545884728933445, 3050720902344151741915306614679859080966393333050435801037029],
    [3050860551133492522763169550138948990291477808980796552056196, 3050860551133492525075874010309498803531237039049965431273701, 3051046749519280431214590571108404223805932255246521692379524, 3052163939834006696499129736453561393949115814161347068024196, 406917393, 406917393, 406917393, 406917393, 11142140374377984502169470162, 675353393, 406917393, 675353393],
    [3050680171447260654143367930628964205911867817586758941216132, 3050674352747707494190838330374004476076953080235359090838916, 3051046749519280432206854899346264070667014257608097042323844, 3052163939834006697491394065307500020059065638360099082485124, 406917393, 406917393, 406917393, 406917393, 675353393, 406917393, 675353393]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_4 : TreeBound (n := 3) 21 [((0, 1), ⟨1, 0, false⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2290098736]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_5 : TreeBound (n := 3) 21 [((0, 1), ⟨1, 0, true⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012622638599712144425683]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_6 : TreeBound (n := 3) 21 [((0, 1), ⟨1, 1, false⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2290098736]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_7 : TreeBound (n := 3) 21 [((0, 1), ⟨1, 1, true⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012622638599849591833811]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_8 : TreeBound (n := 3) 21 [((0, 1), ⟨2, 0, false⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2172731952, 2155889200, 2172731952, 159703937664258590743625598162, 159703936474370973047321658578, 159703938854146208439929538002, 159703941233921443832537417426, 159703936474370973047321658578, 159703945993471914617753175250, 159703936474370973047321658578, 159703955512572856188184693970, 2189574704],
    [159703937064702812203046274258, 2189574704, 159703937064702812203046274258, 2223260272, 158775500924776772131837184211, 2223260272, 159085004824064048679176638675]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_9 : TreeBound (n := 3) 21 [((0, 1), ⟨2, 0, true⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159703937064846932362546907379, 158485341019194948719470708947, 293610032, 25174576, 293610032, 562045488, 21277704200969723526223497971, 562045488, 98312744943595374206582834682876832815157605422334307799301, 1099051568, 562045488, 1099051568],
    [38688577742748726302213330, 2165392465, 2165392465, 2165392465, 2166441585, 2166441585, 3050697627545928254681911970428238736502707025953204924057765, 159703955954240805688744085715, 158543373000311313072090516179, 159703955954240805688744085715, 158620748975133132208916925651, 159703937064846932362546907379],
    [158775500924776770482569742547, 159703937064846932362546907379, 159085004824064047029875382483]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_10 : TreeBound (n := 3) 21 [((0, 1), ⟨2, 1, false⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2172731952, 2155889200, 2172731952, 2495451336271576250657670290, 9747554752764129319191698, 2495603632590657592808834194, 9747554752764129319191698, 9981572178131999921073686226, 19963068208068433670372984018, 79852044387687036166168777938, 2189574704, 2182234672],
    [2147500592, 2182234672, 2149597744, 2147500592, 2149597744, 2147500592, 2151694896, 158543372557562435354564496083, 2151694896, 158543372705145395143529468627, 2189574704, 159085079803054071988803998866],
    [2147500592, 159085042033345863094303331538, 2183283248, 2147500592, 2183283248, 2147500592, 158620748532384254491390905555, 158620748679967214280355878099, 2223260272, 310526512, 8405552, 310526512],
    [545276464, 10213629266884029425106617043, 545276464, 20117754044076878938895418579, 1082147376, 8405552, 1082147376, 8405552, 2223260272, 361054832, 8405552, 361054832],
    [10523133166171305972412252883, 20427257943364155486201054419, 1149518448, 8405552, 1149518448, 8405552]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_11 : TreeBound (n := 3) 21 [((0, 1), ⟨2, 1, true⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158466072583353220399377158355, 158485341019194949269260341459, 293601840, 25166384, 293601840, 9981576900282296829498364627, 19963077652296965480105120979, 1098990128, 1098990128, 25166384, 2165392465, 2165392465],
    [2165392465, 158485341618696116716555473043, 2166441585, 2166441585, 158466034214089518269310963923, 2215724113, 2215724113, 158466034214107532135244501139, 2267104881, 3050720902344151739437224766392480634509776588870658433027460, 2267104881, 3055143109744870396589878169538084353328948577882149753435621],
    [159085004381315168212871549139, 158466034509255437864353140947, 158543373000311313621880148691, 158466034214089518269310963923, 2215724113, 2215724113, 2250327665, 2250327665, 3050860551133492522763169550138948990291477808980796552056196, 158620748975133132758706558163, 344068656, 75498032],
    [344068656, 3053653524077069856315961799500303366233626267695849314693765, 9923507140234069519716847827, 191039543818220493865641880016996731203948573947588456025476, 19827631917426919033497194707, 1149518448, 1149518448, 1149518448, 75498032, 158775500924776771032359377107, 344068656, 75498032],
    [344068656, 5571073138758121550892241107, 1149518448, 1149518448, 1149518448, 75498032, 159085004824064047579665010899]
  ]) (by decide) ?_
  decide +kernel

theorem bound6_1 : TreeBound (n := 3) 21 [((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (0, 1)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_1_0
  · exact bound6_1_1
  · exact bound6_1_2
  · exact bound6_1_3
  · exact bound6_1_4
  · exact bound6_1_5
  · exact bound6_1_6
  · exact bound6_1_7
  · exact bound6_1_8
  · exact bound6_1_9
  · exact bound6_1_10
  · exact bound6_1_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_2 : TreeBound (n := 3) 21 [((1, 0), ⟨0, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2290188848]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_0 : TreeBound (n := 3) 21 [((0, 1), ⟨0, 0, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012622638881067929568402]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_1 : TreeBound (n := 3) 21 [((0, 1), ⟨0, 0, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012622566819042557035730]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_2 : TreeBound (n := 3) 21 [((0, 1), ⟨0, 1, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012622638885465978176658]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_3 : TreeBound (n := 3) 21 [((0, 1), ⟨0, 1, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282820144, 2281701936, 2282820144, 2281701936, 2283938352, 2281701936, 2283938352, 2281701936, 3714046939102406354848056466, 159694340773260811536166946002, 6190078133472676362764551634, 50645960934288067702270132775058176271842256058990942443333],
    [11142744985411254203554333842, 1238015744732136348005303442, 406917393, 406917393, 406917393, 406917393, 11142140374377984502169470162, 675353393, 406917393, 675353393, 3714046939111554291658261650, 2982083519608544361364165071237751952113568976558764133764],
    [6190078281055706520473437650, 1242851595593625023486756050, 193646184843609242816871928697544259382146097094117896818724, 1238015744741284284815508626, 406917393, 406917393, 406917393, 406917393, 675353393, 406917393, 675353393]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_4 : TreeBound (n := 3) 21 [((0, 1), ⟨1, 0, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282824240, 2281710128, 2282824240, 2281710128, 2283938352, 2281710128, 2283938352, 2281710128, 2168726128, 2219057776, 2168726128, 2219057776],
    [2185503344, 2151948912, 2185503344, 2219057776, 3053653526920307255560928599207870456310515923087768599715140, 2219057776, 3053653526920307255560928599207870456310515923087768599715140, 158485341019668103329900266706, 158485340576518130829466026195, 158504685013373558114106868946, 158620748975025322467415688402, 158775500925830889444930096338],
    [158775500482099953107961383123, 159085004826280094696097322194, 159085004381387230205023097043, 2168726128, 2219057776, 2168726128, 2219057776, 2185503344, 2151948912, 2185503344, 2219057776, 2219057776],
    [158485340724101090618397180115, 158543373000203503330589279442, 158775500629682912896892537043, 159085004528970189993954250963]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_5 : TreeBound (n := 3) 21 [((0, 1), ⟨1, 0, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282824240, 2281701936, 2282824240, 2281701936, 2283938352, 2281701936, 2283938352, 2281701936, 3050680171463908070237534855127966848221798391072609941652276, 158465996582668622380308497618, 158485341758262743438360448914, 2185503344],
    [2151940720, 2185503344, 3050860551133492525075889151061591729225656968251996996285029, 943792945, 406922033, 406922033, 159694340773404865286857884627, 675357233, 675357233, 675357233, 3050680171463908070567642680100586080790606774499848280148036, 158465996730251652537983829202],
    [158504684720112520372427036114, 158466034509183515495145538770, 2185503344, 2151940720, 2185503344, 943792945, 406922033, 406922033, 675357233, 675357233, 675357233]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_6 : TreeBound (n := 3) 21 [((0, 1), ⟨1, 1, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282824240, 2281710128, 2282824240, 2281710128, 2283938352, 2281710128, 2283938352, 2281710128, 2168726128, 2219057776, 2168726128, 2219057776],
    [2185503344, 2151948912, 2185503344, 2219057776, 2219057776, 138477585, 406917393, 138477585, 406917393, 11142140374377984777064154322, 675357233, 138477585],
    [675357233, 2168726128, 2219057776, 2168726128, 2219057776, 2185503344, 2151948912, 2185503344, 2219057776, 2219057776, 138477585, 406917393],
    [138477585, 406917393, 675357233, 138477585, 675357233]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_7 : TreeBound (n := 3) 21 [((0, 1), ⟨1, 1, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282816048, 2281701936, 2282816048, 2281701936, 2283938352, 2281701936, 2283938352, 2281701936, 3714046939102410752863110290, 1238015744732136349045490898, 6190078133472676362735191506, 50645960934288067702270132775058176397476592401260280954181],
    [1238015744732136347971749010, 943792945, 406922033, 2240838367556492501896381855999333348508688525187246944494725967475524644551345373947010017753974674327, 406922033, 159694340773404865424305292755, 675357233, 675357233, 675357233, 3714046939111558689606206610, 1238015892315166506720822482, 6190078281055706520410523090],
    [1242851595593625023419647186, 1238015744741284284714845330, 943792945, 406922033, 406922033, 675357233, 675357233, 675357233]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_8 : TreeBound (n := 3) 21 [((0, 1), ⟨2, 0, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714047381851501741316637842, 159694341216009902558948754642, 6190078576221767316826883538, 403784240, 403784240, 134234672, 673333808, 134234672, 673333808, 134234672, 1238015597185135538178491602, 1238015597185135538178491602],
    [672350768, 672350768, 673333808, 673333808, 673333808, 673333808, 671236656, 11142140374666215428110550738, 940786224, 940786224, 134234672, 673333808],
    [134234672, 673333808, 134234672, 11142140522069039546030392275, 11142140669651999334961546195, 11142745428160380135830324370, 134234672, 673333808, 134234672, 673333808, 134234672, 1238015744732136897761117330],
    [21046265299261889060884481491, 1238015744741284834504213650, 21046265446844848849815635411, 39635843693961965894243585170, 39926003599543717289672182994, 39655187687667350310779751890, 39693880397444813116508605586, 39926003599543787657342618770, 39616499700256511110036982930, 39926022489009719135923477650, 39926003599543787657342618770, 19827594138999770930007377042],
    [590332121182638310610, 19846938132705190530915632338, 154752539975759456291128530, 39926003599543787657342618770, 590332121181564568722, 119159020708858498992868301970, 590332121181564568722, 39638261546754187025944024210, 79852006608755313396706055378, 39638262727345807743355327634, 40238000909487011250672112786, 79387750759824398575747601618],
    [39928421452336008789043059858, 39618917553048732241737421970, 39928440341801940267623914642, 39928459231267871746204769426, 39635843693961965894243585170, 590332121182638310610, 39655187687667350310779751890, 309504489619397728870204562, 590332121181564568722, 309523379085329207451059346, 590332121181564568722]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_9 : TreeBound (n := 3) 21 [((0, 1), ⟨2, 0, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2147566673, 2148615249, 2148615249, 158465996435229716754444060883, 2166441585, 2166441585, 3050680171447260653151103602694328283060544615446357663078788, 3050680171447260654143367931856306298794928350562915253501316, 158485341019267010711555147987, 3050697627545928250720587794141561799217665625125530817596804, 3050697627545928250756764097808947515791386119966734515275524, 3050720905140920519588508636574096929886316642676684558294165],
    [3050767454692974321003925460658965437770720457645961315628981, 2165392465, 2165392465, 2165392465, 158504684422640626322857265619, 2166441585, 2166441585, 158465996435229716754444060883, 2215724113, 2215724113, 158465996435229716754444060883, 2267104881],
    [2267104881, 3050720902477331075981383050796752914712605895658469551481877, 2182169713, 2182169713, 158543372410051535891270470611, 2183218801, 2183218801, 3050720902344151741915321755431942606304663471879524309040741, 3050720902344151741915321755431933205697490148255880468266597, 159703955954312867680828524755, 158543377206138004017739336851, 2182169713],
    [2182169713, 158620748384873355028096880083, 2183218801, 2183218801, 6330745116786011110111460158360959248875857103055500414340, 39923585746751566526715921618, 191039543818220493865641880094006505167811389737709303827844, 39926003599543787657342618770, 39926003599543787657342618770, 39928421452336008789043059858, 309504489619397179114390674, 158775500924848832474654181587],
    [7447935431512276394650625195478739767625505100075300097412, 79852006608755313946495423698, 39926022489009719685746400402, 119159020708858500092447038610, 39928440342954861772297870482, 309523379085328657762354322, 159085004824136109021959821523]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_10 : TreeBound (n := 3) 21 [((0, 1), ⟨2, 1, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714047381851501741350192274, 2505047184964767369731900562, 9747554752764129319191698, 2505350597011300540529902738, 9747554752764129319191698, 19963002094937919785944614098, 39935675006100704690773822610, 590332121732427678930, 39940529598845235423541861522, 590332121732427678930, 3714198497578957968043541650, 1247687594038144404218315922],
    [672350768, 672350768, 673333808, 673333808, 673333808, 673333808, 671236656, 11142140374666215977899919058, 940786224, 11142140383710014725653807315, 940786224, 134234672],
    [673333808, 134234672, 673333808, 134234672, 21046265742443387701514339538, 21046265160902864239434154195, 134234672, 673333808, 134234672, 673333808, 134234672, 1238015744732136897794671762],
    [1238015744741284834537768082, 39635843693961965894277139602, 39616518589722372770736770258, 39655187687667350860569120210, 381335387939751254045730649098717286831813751948078489547428, 39693880397444813116542160018, 39926003599543787657376173202, 39616499700256511110070537362, 39926022489009719135957032082, 39926003599543787657376173202, 20553509857225779351520402, 590332121732427678930],
    [39897503562645930015589586, 154752539975760006080496850, 39926003599543787657376173202, 590332121181598123154, 119159020708858498992901856402, 590332121181598123154, 39638261545601265521370729618, 79233036589112623809045861586, 79271686797591670420297356754, 79852044387687176903657133266, 39696298249084112743635750034, 39928421451183087284469763218],
    [39618917551895810737164127378, 39928440340649018763050622098, 39928459230114950241631476882, 24180287316175219991905426, 590332121732427678930, 43524281021489817539708114, 309504489619397728903758994, 590332121181598123154, 309523379085329207484613778, 590332121181598123154]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_11 : TreeBound (n := 3) 21 [((0, 1), ⟨2, 1, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158466072583425282391461597395, 158485341019267011261344780499, 2495376958927408511838192786, 38688577743030201262146770, 2495528074654860340485031058, 39655187687667350310779751890, 79271686797591670420297356754, 19345764629196133393106066, 2165392465, 2165392465, 2165392465, 158504684422640626872646898131],
    [2166441585, 2166441585, 158465996435229717304233693395, 2215724113, 2215724113, 158465996435229717304233693395, 2267104881, 2267104881, 158466072288259362813599289555, 3050720902477331075971052139101201520806305513100681058824613, 2182169713, 2182169713],
    [158543372410051536441060103123, 2183218801, 2183218801, 3050720902344151741915321755431942607165315584965354898580069, 3050720902344151741915321755431933206558142260540167081157221, 158466034214161580261395402963, 2215724113, 2215724113, 158466034214161580261395402963, 2250327665, 2250327665, 158620748458665961382996350419],
    [2182169713, 2182169713, 158620748384873355577886512595, 2183218801, 2183218801, 2785535683989671583972197522, 309504489619397180154578130, 2785686799645061386176955538, 39926003599543787657342618770, 39926003599543787657342618770, 39928421451183087284469763218, 309504489619397179080836242],
    [158775500924848833024443816147, 2785554573455603062553052306, 619008388906673727460213970, 5571070777503098484354581714, 5571073138830183542976680147, 39926022489009719135923477650, 119159020708858500092447038610, 39928440342954861772297870482, 309523379085328657661691026, 159085004824136109571749449939]
  ]) (by decide) ?_
  decide +kernel

theorem bound6_3 : TreeBound (n := 3) 21 [((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (0, 1)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_3_0
  · exact bound6_3_1
  · exact bound6_3_2
  · exact bound6_3_3
  · exact bound6_3_4
  · exact bound6_3_5
  · exact bound6_3_6
  · exact bound6_3_7
  · exact bound6_3_8
  · exact bound6_3_9
  · exact bound6_3_10
  · exact bound6_3_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_4 : TreeBound (n := 3) 21 [((1, 0), ⟨1, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2290254384]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_0 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 0, false⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282914352]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_1 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 0, true⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012041746883581191405779]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_2 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 1, false⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282914352]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_3 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 1, true⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282885680, 2281701936, 2282885680, 2281701936, 2281710128, 2281701936, 2281710128, 2281701936, 403849776, 159694340625677781928247428306, 403849776, 134234672],
    [673202736, 134234672, 673202736, 134234672, 2232567121, 2165458257, 2165458257, 2266121585, 2182235505, 2232567121, 2182235505, 2215789905],
    [2215789905, 403849776, 403849776, 134234672, 673202736, 134234672, 673202736, 134234672, 2232567121, 2165458257, 2165458257, 2266121585],
    [2182235505, 2232567121, 2182235505, 2215789905, 2215789905]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_4 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 0, false⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2283831856]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_5 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 0, true⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2281734704]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_6 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 1, false⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2283831856]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_7 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 1, true⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2281734704]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_8 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 0, false⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2168685104, 159703936621953934485620917458, 2168685104, 159703955512572857837552798930, 2185396784, 2151711280, 2185396784, 159703936621953934485620917458, 2219082352, 158775500924965936510426941651, 2219082352, 159085004824262220256987582675]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_9 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 0, true⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159703936770104365443409250547, 158485340576662256978298669267, 287343152, 6228538414707034985794373875, 287343152, 14895870863023203636724822465415516833833146301576077639589, 555778608, 18907696, 555778608, 555778608, 1093829168, 555778608],
    [1093829168, 158495315395265698369758300627, 289572177, 158495013163810794711927753171, 289572177, 826443633, 558007921, 1094878289, 558007921, 1363314001, 1094878289, 1094878289],
    [158543372557778621330918476499, 158543372557778621330918476499, 159703955511708113947572046035, 158620748532600440467744886483, 159703936770104365443409250547, 158775500482244078741397702867, 159703936770104365443409250547, 159085004381531355288703342803]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_10 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 1, false⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2168685104, 2185368112, 2151678512, 2185368112, 2151686704, 2151678512, 2151686704, 158485341019379609223437616851, 2151694896, 158485341019384113097959803091, 2151694896, 158485341019393120847004176595],
    [2168685104, 2236027504, 158466034509183374757657183442, 2236027504, 2219057776, 158466034509183374757657183442, 2219057776, 158504685013085064007644219091, 2185396784, 2151711280, 2185396784, 2495469782997742764150621330],
    [2495661038840466110549197970, 642155120, 4227632, 642155120, 4227632, 1145340528, 4227632, 1145340528, 4227632, 2219082352, 306348592, 2785535684170112419084910803],
    [306348592, 541098544, 4227632, 541098544, 4227632, 1077969456, 4227632, 1077969456, 4227632, 2219082352, 3095039583457388966390546643, 642155120],
    [4227632, 642155120, 4227632, 1145340528, 4227632, 1145340528, 4227632]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_11 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 1, true⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3050680171447260655466387035017309366917712952587962725240196, 159085080086978038827162538195, 158543448263225304972463182547, 158543448263225304972463182547, 3050680171447260655466387034940370024204363855661037184159108, 158543448263225305109910524627, 3050680171447260655466387034945408827825090956377162699836804, 3050680171447260655466387034940370026355994136371099505331588, 3050680171447260655466387034945709648115289416068249034755460, 158466072288403486797768167635, 158485340724245216767230087379, 3050697627545928253361457959471014332238318415837903929019780],
    [158485415101517319799346565331, 3053653524789440577871762131356844169746096376764577295610501, 159085042308046175973086335187, 159085042308046176110533677267, 289572177, 289572177, 826443633, 558007921, 1094878289, 558007921, 1363314001, 1094878289],
    [1094878289, 158466001452906244852668698835, 158543372705361581119849894611, 356681041, 356681041, 570458672, 33587760, 570458672, 33587760, 1111654960, 33587760, 1111654960],
    [33587760, 158620748680183400256676304595, 6330745116786011110111460228155842872809948816612982066564, 356681041, 356681041, 606110256, 67142192, 606110256, 67142192, 1145340528, 1145340528, 1145340528],
    [67142192, 158775500629827038530329123027, 7447935431512276394650625265273623391559596812850023959940, 606110256, 67142192, 606110256, 67142192, 1145340528, 1145340528, 1145340528, 67142192, 159085004529114315077634756819]
  ]) (by decide) ?_
  decide +kernel

theorem bound6_5 : TreeBound (n := 3) 21 [((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (1, 1)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_5_0
  · exact bound6_5_1
  · exact bound6_5_2
  · exact bound6_5_3
  · exact bound6_5_4
  · exact bound6_5_5
  · exact bound6_5_6
  · exact bound6_5_7
  · exact bound6_5_8
  · exact bound6_5_9
  · exact bound6_5_10
  · exact bound6_5_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_6 : TreeBound (n := 3) 21 [((1, 0), ⟨1, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2290254384]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_0 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 0, false⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282820144, 2282750512, 2282820144, 2282820144, 2282955312, 2282959408, 2282955312, 2282750512, 158485340439168255890691329170, 158775500344750007286119926994, 158504684432873640307227495890, 159703937665339731731124718802],
    [3050860551133492480117807994571865640212432359593726417393348, 3053839722376149501254033306076292117418657836772279641496900, 158543377142651103112956349586, 3055143110100014613131624137065505016141868154727990501104964, 158775500344750077653790362770, 3053653526920307254261165687619582816065788156735969295392068, 158775519234216009132371221650, 3053653526920307254261165687619582816065788156735969295392068, 2147631121, 158485340438591478482260213971, 158504684432296939311616623826, 3050697627545928254702722924305732624764213948041325465681061],
    [2183283249, 2183283249, 2147631121, 2183283249, 158775500344750008935387368658, 158775500482568353857386318035, 159085004245190206987333407954, 159085004529438590193623371987, 158485340440321247764075910290, 158466109783411381851354436754, 158485341620912868481487213714, 158620823954123157167845545106],
    [158620748396259291066863326418, 159085079803054071988803998866, 158775500345903069527174945938, 158775519235369001005755800722, 2147631121, 158485340438591479036344549587, 3050697627545928250733669406400786088668768382396205956761413, 2183283249, 2183283249, 2147631121, 2183283249, 158775500482568354407175686355],
    [159085004529438590743412740307]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_1 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 0, true⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012042035131549529161939]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_2 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 1, false⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282820144, 2282750512, 2282820144, 2282820144, 2282955312, 2282959408, 2282955312, 2282750512, 158485340439168818840644750482, 158775500353973942272928124114, 158504684442097575294035693010, 159703938855155287435344219602],
    [3050674352792100689780055372476457497012233473547822249554596, 158543377142651666062909770898, 158775500344750640603743784082, 158775519234216572082324642962, 3714046801248598590230758546, 3714046801256757244758868179, 134365201, 3089403582894860268654979616333930439850698684467683359789092, 673333809, 673333809, 134365201, 673333809],
    [158485340439168889209422482578, 158466034234771450737180415186, 158504684443250497348431910354, 158620823963346951967994942674, 158543377142651736431687502994, 159085042033346003831791686866, 158775500344750710972521516178, 158775519234216642451102375058, 3714046801265764998097944787, 134365201, 673333809, 673333809],
    [134365201, 673333809]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_3 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 1, true⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282820144, 2281701936, 2282820144, 2281701936, 2281710128, 2281701936, 2281710128, 2281701936, 159694340625677781928247428306, 134234672, 673333808, 134234672],
    [673333808, 134234672, 2232567121, 2165458257, 2165458257, 2266121585, 2182235505, 2232567121, 2182235505, 2215789905, 2215789905, 134234672],
    [673333808, 134234672, 673333808, 134234672, 2232567121, 2165458257, 2165458257, 2266121585, 2182235505, 2232567121, 2182235505, 2215789905],
    [2215789905]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_4 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 0, false⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2283962928]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_5 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 0, true⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2281734704]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_6 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 1, false⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2283962928]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_7 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 1, true⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2281734704]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_8 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 0, false⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714046939102624023891281042, 159694340773260743366546687186, 6190078133472889599401526738, 158478087022609313093231185106, 285376529, 158497431016314767877437787602, 285376529, 304251441, 304251441, 268599313, 304251441, 268599313],
    [25322980467132183595974528010338260430220991896746311924901, 159077750827478411403635858642, 3339653974736134392066391622741197425733489178507940861938085, 159694340773260743366546687186, 11142744985411291312172434578, 138445360, 1095008880, 16941073, 1095008880, 16941073, 1111786096, 1078231664],
    [1111786096, 1145340528, 1145340528, 1078231664, 1145340528, 1145340528, 19827593696250682106349487250, 39635843112277285979149058259, 19846937689956136891629831378, 1525360451171035398149375644282763618585577632026218903223461, 37782064, 4227632],
    [37782064, 4227632, 1145340528, 4227632, 1145340528, 4227632, 1095008880, 1095008880, 1111786096, 1078231664, 1111786096, 1145340528],
    [1145340528, 1078231664, 1145340528, 1145340528, 79252342221048684034270445779, 1111786096, 4227632, 1111786096, 4227632, 71336496, 4227632, 71336496],
    [4227632]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_9 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 0, true⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [287474224, 3713990271208982056957905107, 287474224, 6190004937224504391913179603, 555909680, 555909680, 555909680, 555909680, 381340112793018967416409982496059334923998523380472388324740, 555909680, 1525342995072714618784514980504666586123638071527203287141764, 158485340576950504946636425427],
    [287474224, 287474224, 555909680, 555909680, 555909680, 555909680, 555909680, 158495315395553946338096056787, 289572177, 158495013164099042680265509331, 289572177, 826443633],
    [558007921, 1094878289, 558007921, 1363314001, 1094878289, 1094878289, 158620748532888688436082642131, 158543372558066869299256233683, 159703955511996361915909802195, 158620748532888688436082642131, 2785535168034813225392538770, 356681041],
    [5261566362400579599321925074, 356681041, 610697840, 1145340528, 610697840, 71336496, 1145340528, 1145340528, 1145340528, 71336496, 158775500482532326709735459027, 2785554057518759102482875538],
    [5571070261696863345882301906, 610697840, 1145340528, 610697840, 71336496, 1145340528, 1145340528, 1145340528, 71336496, 159085004381819603257041098963]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_10 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 1, false⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714046939111631223146022034, 21048683151342567804173943954, 138412592, 21046265447277361539680699602, 138420784, 3714046828953331603408488147, 138420784, 138412592, 3714198054839087449839371410, 3721300494029246464654443666, 1242851595593484285931291858, 3721451609756707089396401298],
    [1242851595593484285998400722, 6190078023251543981853574867, 1242851595593484285931291858, 1245269299658972609586005138, 558269040, 558269040, 575046256, 642155120, 575046256, 642155120, 608600688, 642155120],
    [608600688, 642155120, 2506255668044617033818702994, 2514417097918803623926695058, 1648788080, 4227632, 1648788080, 4227632, 1145340528, 4227632, 1145340528, 4227632],
    [21046265447277363670114501842, 138445360, 1095008880, 40854458333841623461119790290, 1095008880, 1111786096, 1078231664, 1111786096, 1145340528, 1145340528, 1078231664, 1145340528],
    [1145340528, 20553067117144154914817170, 39635843250663332383331453139, 39897208396445976755307730, 37782064, 4227632, 37782064, 4227632, 1145340528, 4227632, 1145340528, 4227632],
    [1095008880, 1095008880, 1111786096, 1078231664, 1111786096, 1145340528, 1145340528, 1078231664, 1145340528, 1145340528, 79252342507008683032424485075, 1525360451171382217995014448028097136498787916814435503540037],
    [1111786096, 4227632, 1111786096, 4227632, 71336496, 4227632, 71336496, 4227632]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_11 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 1, true⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3050680171447260655466387034945112634974486254716418584808836, 159085080087266286795500294355, 158620824238335372215074690259, 158620824238335372077627348179, 158620824238335372215074690259, 158466072288691734766105923795, 158485340724533464735567843539, 3050697627545928253361457959398817600295091717966359788588420, 158485415101805567767684321491, 159085042308334423941424091347, 159085042308334424078871433427, 289572177],
    [289572177, 826443633, 558007921, 1094878289, 558007921, 1363314001, 1094878289, 1094878289, 158466006175560975690651668691, 158543372705649829088187651795, 356681041, 356681041],
    [570458672, 33587760, 570458672, 33587760, 1111786096, 33587760, 1111786096, 33587760, 158620748680471648225014060243, 356681041, 356681041, 606241328],
    [67142192, 606241328, 67142192, 1145340528, 1145340528, 1145340528, 67142192, 158775500630115286498666879187, 606241328, 67142192, 606241328, 67142192],
    [1145340528, 1145340528, 1145340528, 67142192, 159085004529402563045972512979]
  ]) (by decide) ?_
  decide +kernel

theorem bound6_7 : TreeBound (n := 3) 21 [((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (1, 1)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_7_0
  · exact bound6_7_1
  · exact bound6_7_2
  · exact bound6_7_3
  · exact bound6_7_4
  · exact bound6_7_5
  · exact bound6_7_6
  · exact bound6_7_7
  · exact bound6_7_8
  · exact bound6_7_9
  · exact bound6_7_10
  · exact bound6_7_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_0 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 0, false⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2172945008]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_1 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 0, true⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159703955955321737204346260690]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_2 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 1, false⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2172945008]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_3 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 1, true⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159703937665339522274260290770, 2271482480, 159703936475532971570171612370, 2271482480, 158465996436247591295238933714, 2219057776, 158465996436247591295238933714, 2219057776, 159703936475532972119927426258, 159703938855155077978479791570, 2165576304, 3050685990146816522321192305670836906169419086196381981660485],
    [2165576304, 2147746416, 2147754608, 2147746416, 2147754608, 159703941234786189386918792914, 159703936475523966570040790226, 159703945994048412203796794578, 287474225, 287474225, 555909681, 555909681],
    [555909681, 555909681, 555909681, 381347022497701097954203413620138719625946245755484725126821, 762680225586037934900085284412493028978467872274802761606821, 159703955512572857837552798930, 3713980753301564758402665682, 6190011947599777136847752402, 11142083854716143927866559698, 558270065, 21004305, 558270065],
    [21004305, 381347022497701098202512693778088580272892563535328485572517, 762680225586037935148717566973418917951503981792365679987621, 2235830896, 3196670516267870255641817316123211488780077153222683550690177866299871605311105132983022479246368166216601152696020082725300094572204421373799563906059861384, 2235830896, 2219057776, 2219057776, 558270065, 21004305, 558270065, 21004305],
    [381347022497701098534235530770401359185551538123660383694757, 762680225586037935479471396756803611885893581167540868467621]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_4 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 0, false⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2189722224]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_5 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 0, true⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159703937065855805725765405906]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_6 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 1, false⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2189722224]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_7 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 1, true⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3713973005660046601136245970, 159696702400404049429298023634, 6190005380549879696992636370, 159694417374510057069509479634, 159694569680053064602375818706, 302022673, 304251441, 302022673, 304251441, 302022673, 11142070130329545888705416914, 159694265659298888692367756498],
    [21046199629888878272130976978, 159694265659298888692367756498, 40854458629007543038982098130, 39771251068215469468595273939, 1713668720, 295536, 1713668720, 295536, 4489840, 295536, 4489840, 295536],
    [1528316348414892512998655757759130083550817800015594265276804, 1176797808, 1145340528, 1176797808, 1145340528, 1145340528, 1145340528, 1145340528, 1145340528, 79387750176986867523716661459, 572818032, 295536],
    [572818032, 295536, 4489840, 295536, 4489840, 295536]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_8 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 0, false⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2223276656]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_9 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 0, true⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [377782896, 5570900779443208095371641075, 377782896, 25322979401697488662465686780352235770949017422079880444997, 3245810257499029785290995738963484330334359086422313617631508, 5261566325067744196555803603, 5261566362251714521014109651, 4578990700449532252358724005833974182230632789828419791923476, 3053653524076373504398049521379339352838559833919961573927188, 3053653524076373504398049521379339352838559833919961573927188, 612663920, 10213629267964959306499033811],
    [612663920, 20117754044004887315672597715, 1082425968, 8684144, 1082425968, 8684144]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_10 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 1, false⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2223276656]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_11 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 1, true⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [293868144, 2785536865661941533412297938, 293868144, 2476031785783045608691600594, 2495375779488500392900299986, 360989296, 2476031785783043684546251986, 360989296, 277086832, 1149518448, 1149510256, 1149510256],
    [1149518448, 1149518448, 1149518448, 1149518448, 293868144, 4952062980081255788146986194, 293868144, 360989296, 360989296, 277086832, 3244506869420019775541995498850776017261091994690211150080276, 5571070224355091112605619155],
    [5571070261539061437063923155, 25322980467132518960184781459053075927175640947248778664229, 25322980467132519621694333608100358565595974630745662773541, 10213633990304420563347705554, 572818032, 537166448, 572818032, 572818032, 642024048, 644121200, 642024048, 537166448],
    [10523133168405227727155696339, 572818032, 537166448, 572818032, 572818032, 642024048, 644121200, 642024048, 537166448, 20427257943292234231722411219, 1149534832, 8684144],
    [1149534832, 8684144]
  ]) (by decide) ?_
  decide +kernel

theorem bound6_8 : TreeBound (n := 3) 21 [((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (2, 0)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_8_0
  · exact bound6_8_1
  · exact bound6_8_2
  · exact bound6_8_3
  · exact bound6_8_4
  · exact bound6_8_5
  · exact bound6_8_6
  · exact bound6_8_7
  · exact bound6_8_8
  · exact bound6_8_9
  · exact bound6_8_10
  · exact bound6_8_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_0 : TreeBound (n := 3) 21 [((2, 1), ⟨0, 0, false⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714047382355937335275816082]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_1 : TreeBound (n := 3) 21 [((2, 1), ⟨0, 0, true⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714047382932151813080629459]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_2 : TreeBound (n := 3) 21 [((2, 1), ⟨0, 1, false⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [6190078576654114530422555858]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_3 : TreeBound (n := 3) 21 [((2, 1), ⟨0, 1, true⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3053653526917540813351374026051298829286143145577562686426500, 403968273, 403968273, 403964177, 403968273, 403968273, 403968273, 403968273, 402915601, 403968273, 6190078004770143286604203218, 14895865180707536320100220772649332108947871097035704349461],
    [403968273, 6190077986903026693985829331, 6190078004770143698946229458, 26812567553435787265341296884023604864340513647875111631941, 1238317847628623149139100882, 403968273, 403968273, 403964177, 403968273, 1238015597149387802720470162, 403968273, 1238015597149388215062496402],
    [1238015597149388215096050834, 6190002429034799104297828819, 268730641, 308578161, 308578161, 4952062389749418829398704595, 340033809, 3052163939831275479343764865522696393889518228355009314831748, 340033809, 6190026077762953400830430163, 287605617, 287605617],
    [337937265, 304382833, 321160049, 304382833, 388268913, 337937265, 4577501116205084522286448166769511201869141302019872704446740, 337937265, 403968273, 403968273, 403964177, 403968273],
    [3714197908328888169706586515, 403968273, 3714197908328888169710780819, 3714197908328888169706586515, 6190030837025176218782174675, 287605617, 6051455972803725903336310861904762067253054184442383683989, 287605617, 337937265, 304382833, 321160049, 304382833],
    [388268913, 337937265, 337937265, 3050680171444832904825810764633421933317062213400334560988548, 4990750377160328397811909075, 4952062389749418829398704595, 23879942977277564048486154265445906055099569483002915961061, 4952064750932660264221311443, 24019591766618347209053549895085628619943275482532546197733, 4952062389749418829398704595, 24205790152406255660474570633511319916072288559316436891877, 3052163939831578948173836898695879486901237224806849729254788],
    [407142673, 3050680171445873369386057737624573270649872897715550175432068, 3050720902342764455837556289704273150049441855573021567059716, 3050674352746320209433528137369615822114648170963838738173316, 3051046749517893147449544706341873066552916017497461060852100, 3052163939832619412734083872303109015944967398249463101013380, 407142673]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_4 : TreeBound (n := 3) 21 [((2, 1), ⟨1, 0, false⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [562201136, 158475820729446415045354340563, 562201136, 3074528088847707462967693677046457630913928352280340273413189, 1361348465, 1361348465, 38990220018807298215412179, 289702161, 289702161, 578847280, 158534306057745134883914713811, 578847280],
    [158612286495476761335328541907, 612663920, 545292848, 612663920, 159080169121866520043811508435]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_5 : TreeBound (n := 3) 21 [((2, 1), ⟨1, 0, true⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [21664574632507648356070263539, 9923469362383137543400000211, 554861104, 21084271958333783458980104947, 554861104, 555909680, 555909680, 555909680, 553812528, 826442288, 555909680, 826442288],
    [95356802862998964324652723126112312503505643256689973690389, 95356802862998964324652723125811493073959295849889486503957, 556040817, 556040817, 556040817, 560236145, 558137969, 558137969, 11142065407963063034092522195, 9981501343499501896019806931, 11142070130329545903737735891, 10058877318321321032846216915],
    [10213610378499027827918179027, 10213629267964959306499033811, 21045585723399026740039846643, 10523133167252235853804673747]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_6 : TreeBound (n := 3) 21 [((2, 1), ⟨1, 1, false⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [11142745427583885848522917010]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_7 : TreeBound (n := 3) 21 [((2, 1), ⟨1, 1, true⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3074530998178057981448111594249870519529508400893255547162852, 555909680, 555909680, 555909680, 16941616, 11198724912381733234208504991015173626633666466719937770324774263474055308012544380897048238805020554134, 555909680, 4576030439895460561447472679691151727880171620381320320716836, 21046208779455924433559096531, 19827594139575987057180413139, 555909680, 555909680],
    [555909680, 16941616, 281608534987662527204225561660183690354085399917623927016366189331861402123343156587084360282603519895, 555909680, 4957364370303900827244264334129722651006775923228157145845796, 190690421844868315018951669339265217116155129040851057048389, 556040817, 556040817, 556040817, 560236145, 558137969, 558137969],
    [21046190185155912547872935123, 19885626120692351409800220371, 21046199629888878287163362515, 19963002095514170546626628819, 20117735155691877341698591955, 20117754045157808820279446739, 606372464, 71598704, 606372464, 67404400, 71598704, 71598704],
    [71598704, 67404400, 20427257944445085367585086675]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_8 : TreeBound (n := 3) 21 [((2, 1), ⟨2, 0, false⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [1099137584, 40854439738388901162026927314, 1099137584, 40854440337944710488931828946, 40854441527832323787189257682, 1898219377, 17072145, 1898219377, 17072145, 21266449, 21266449, 1115849264],
    [49597395989361092636554037971, 1115849264, 59578292278465953972573441235, 1149534832, 1082163760, 1149534832, 1149534832]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_9 : TreeBound (n := 3) 21 [((2, 1), ⟨2, 0, true⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [562201136, 39635843693961686084741236947, 562201136, 762691499316427424353437265552478624070510809230310624200341, 1092912753, 1095009361, 1092912753, 1525360451171035399473523996359924491303025654071942194661541, 1095009361, 1095009361, 41976368, 39693875675078050437361044179],
    [41976368, 39771251649899869574187453651, 1149534832, 8421936, 1149534832, 8421936]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_10 : TreeBound (n := 3) 21 [((2, 1), ⟨2, 1, false⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [1099137584, 1115820592, 1082130992, 1115820592, 1082139184, 158476274076628768469584775891, 1082139184, 158476878539538575921619537107, 1082147376, 1082130992, 1082147376, 1082147376],
    [1099137584, 39638337102384025854594385042, 79233074365738642657415136466, 39638338282975668562240341138, 40238000909487011250672112786, 79852044387687317641145488594, 1115849264, 1108509232, 158533852129454875229057728723, 1108509232, 1075872304, 1073775152],
    [1075872304, 1073775152, 1077969456, 1073775152, 1077969456, 1077969456, 1115849264, 158611228104276694365884137683, 1109557808, 1073775152, 1109557808, 1073775152],
    [1145340528, 1073775152, 1145340528, 1145340528, 1149534832, 1082163760, 1149534832, 1149534832]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_11 : TreeBound (n := 3) 21 [((2, 1), ⟨2, 1, true⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [293737008, 19344584037329126450922706, 293737008, 3050680171444529438600432592542318709441793890788376249699716, 19344584037331325474178258, 3050680171444572791249098535996696081021832497097754886868356, 1099121200, 3050680171444572791249098535996696083173460589058398305979780, 1099121200, 25297456, 79252342802733084139862888659, 293737008],
    [38688577742783910657524946, 293737008, 1099121200, 38688577742783910674302162, 1099121200, 25297456, 1092912753, 1095009361, 1092912753, 1095009361, 39638262283488692694277427347, 1095009361],
    [3050720902341382588843478278738707754385595343051625369243012, 77376565117631696837149906, 572555824, 33587760, 572555824, 33587760, 1111654960, 33587760, 1111654960, 33587760, 79310374783849448492482697939, 3050860551130723372004045674368349900544475921478992991686020],
    [572555824, 33587760, 572555824, 33587760, 1111654960, 33587760, 1111654960, 33587760, 79387750758671267629309107411, 75793008, 8421936, 75793008],
    [8421936]
  ]) (by decide) ?_
  decide +kernel

theorem bound6_9 : TreeBound (n := 3) 21 [((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (2, 1)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_9_0
  · exact bound6_9_1
  · exact bound6_9_2
  · exact bound6_9_3
  · exact bound6_9_4
  · exact bound6_9_5
  · exact bound6_9_6
  · exact bound6_9_7
  · exact bound6_9_8
  · exact bound6_9_9
  · exact bound6_9_10
  · exact bound6_9_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_0 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 0, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2172945008]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_1 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 0, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2256802416, 2223260272, 2256802416, 2249462384, 158466034216341453325006410962, 2249462384, 2214855280, 2216960624, 158466034216323438926496928978, 2216960624, 2223252080, 2215928432],
    [2219065968, 2215928432, 158466034216323438926496928978, 2216968816, 2219065968, 2216968816, 2219065968, 158504683542249958113668237555, 2219065968, 2223252080, 3050674355588866337149433838934229584919333325384930377347940, 3052163941254586965203233381279575090865069781697582274985348],
    [3050680171463908070236323598576306104203130230312476601173317, 2223260272, 344220272, 1149518448, 344220272, 612647536, 19846332495544620234957720307, 612647536, 1149518448, 1149518448, 1149518448, 75776624],
    [2223260272, 8976479243995738434221747945572191143695106096254864433826004051742056694371039969015121177117552279447, 1149518448, 5958368544084219916759560057038244512163563365893895107428, 1149518448, 1149518448, 1149518448, 75760240]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_2 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 1, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2172945008]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_3 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 1, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485415398700975140540388562, 3050674355588866678483840699300769757647858741731417508298116, 158504758211814809241697523154, 2165576304, 158465996437409590367844701394, 2165576304, 2147746416, 2183406192, 2147746416, 2183406192, 2165580400, 2219057776],
    [2165580400, 2147754608, 2183406192, 2147754608, 2183406192, 2219057776, 2219057776, 2199138928, 158465996437409590367844701394, 2199138928, 2147746416, 2147746416],
    [158466034511489358504359236818, 2165580400, 2219057776, 2165580400, 2147754608, 2183406192, 2147754608, 2183406192, 2219057776, 2219057776, 3050674355588864003345959512628401736880097727908012344750948, 3050767454870544272082579388422615936249309217780766036736116],
    [2495450157913595813927458002, 159080206901951373209923359954, 4990824165325642259167843794, 9981572180149735149648615122, 158456401179030224555774973138, 19963068209797920930610156754, 79852044387687035616379409618, 2514719773193953542903185619, 95426766652087800869908845714594561133594905198798231582836, 2495450157913596363716826322, 4911853780008435175265490, 4990824165325642808957212114],
    [9747557058466951874090194, 9981572180149735699437983442, 19963068209797921480399525074, 79852044387687036166168777938, 2514719774346945966043578579, 5958368233332772971844029757818719029585152158513072190308, 43524281021349095083606227]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_4 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 0, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2189722224]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_5 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 0, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2182382192, 2221150832, 2151957104, 2221150832, 158465996437409590367844701394, 2151948912, 2151940720, 2151948912, 2151957104, 158620743685565861382316100339, 2151957104, 3050720902477331075976214995089292665720284084977112028123973],
    [2182382192, 2182353520, 2182353520, 2147746416, 2147754608, 2147746416, 2147754608, 3050720902477331075981388070592204551718720859346202310728997, 3050720902477331075981388070592204552005604075459076290097573, 2216985200, 2147779184, 2216985200],
    [606372464, 295536, 606372464, 295536, 1078231664, 295536, 1078231664, 295536, 2151973488, 342131312, 5106658802220642324386431219, 342131312],
    [11963246420047014787289113748876545194554073242903741313957, 541360752, 295536, 541360752, 295536, 1074037360, 295536, 1074037360, 295536, 2151973488, 23926492573724476335729394688670643639273831091527272847653, 537166448],
    [295536, 537166448, 295536, 1078231664, 295536, 1078231664, 295536]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_6 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 1, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2189722224]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_7 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 1, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485414817593070971623970002, 159085042024121928107495134418, 158504757630706905072781104594, 158485414817593070971623970002, 158543443256934573275095373522, 158466072004479237145344742610, 158620814509389909679723910354, 159085042024121928107495134418, 3050767454781760587808661725011655760599445181950743713428324, 3050674355588866675837802490666075740112244938893569946303876, 3050767454870546727603695232882178122940923949722476094437492, 3050674355588866675837156485860725909857036343493426130204788],
    [158485414826817005958432167122, 158466072013703171857342141650, 158504757639930840059589301714, 158466072013703171857279227090, 158543443266158508261903570642, 158620814518613844666532107474, 158620814518613844666532107474, 158466072013703171857409250514, 159085042033345863094303331538, 158485414817593070971623970002, 158504757639930840059589301714, 158466071995255301883658638546],
    [158466071995255302021105980626, 158466071995255301883658638546, 158466071995255302158553322706, 158543443284606380297230096082, 158466071995255304082816111826, 158620814573957456511644079314, 572818032, 295536, 572818032, 295536, 1145340528, 295536],
    [1145340528, 295536, 289702512, 159080206459202495492498003154, 289702512, 574915184, 4489840, 574915184, 4489840, 1145340528, 4489840, 1145340528],
    [4489840, 2650127212600856972351376530, 6051464585059370953769962072229801402343681223589638231365, 5145492957033487100647970258, 12009807336737590716048650547151867179360927523889048933397, 574915184, 295536, 574915184, 295536, 1145340528, 295536, 1145340528],
    [295536, 289702512, 289702512, 574915184, 4489840, 574915184, 4489840, 1145340528, 4489840, 1145340528, 4489840, 24019591766618345888297979386924336306856353877950532376869],
    [570720880, 295536, 570720880, 295536, 1145340528, 295536, 1145340528, 295536]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_8 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 0, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2223276656]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_9 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 0, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [377782896, 1686377072, 1082409584, 1686377072, 1082401392, 5570900773318244708789584627, 1082401392, 6330763229175802549412353217562028028872720004381192030277, 1082409584, 1082393200, 1082409584, 1082409584],
    [377782896, 6051450382042092237139893166481568660146550663206986855268, 5261566878287606901593096403, 12009810180665418064600152787845459722691670887751573321844, 24578186923981564524306070349476917500443034662719991710309, 5571051890486853647880163571, 5261566878215549273197510867, 5571051890486853647913718003, 612663920, 1679065712, 20426634019824473696144212211, 1679065712],
    [1076134512, 295536, 1076134512, 295536, 4489840, 295536, 4489840, 295536, 612663920, 606372464, 295536, 606372464],
    [295536, 4489840, 295536, 4489840, 295536, 1082425968, 8684144, 1082425968, 8684144]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_10 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 1, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2223276656]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_11 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 1, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [293868144, 3095040766102210194620683474, 293868144, 2553478597255097601971328722, 2476031786936037482042627282, 2630849849710434006599865554, 2495375780641492266251326674, 360989296, 2476031786936035557897278674, 360989296, 277086832, 1149518448],
    [1149510256, 1149510256, 12661490943856396230913749971292803827762396416742874807637, 1149518448, 1149518448, 1149518448, 1149518448, 293868144, 4952062981234247661531567314, 293868144, 5029509791553309980416415442, 5106881044008646385044952274],
    [360989296, 5106881044008646385229501650, 360989296, 277086832, 5964169888702695070800756618251055938215223236947234009956, 5571070777574883448898732243, 5964186952310660819686175666728088162550910824221775770468, 25322980467132520944854747935501767717796997974465105756773, 5571070779952785126461018355, 5571070777502825820503146707, 5571070779952785126494572787, 9923543159700330429714404562],
    [10523137890753696183259108562, 9942885982038099483317900754, 572818032, 537166448, 572818032, 572818032, 642024048, 644121200, 642024048, 537166448, 95339395066863525084979466683675516354712972430286983541604, 48411716680474964979107380331806027923422600861781065520453],
    [47672744697544709981703335207538864894926525626620600660836, 1143243376, 295536, 1143243376, 295536, 4489840, 295536, 4489840, 295536, 19827667936893179943494751442, 19847010759230948997098247634, 572818032],
    [537166448, 572818032, 572818032, 642024048, 644121200, 642024048, 537166448, 572818032, 295536, 572818032, 295536, 4489840],
    [295536, 4489840, 295536, 1149534832, 8684144, 1149534832, 8684144]
  ]) (by decide) ?_
  decide +kernel

theorem bound6_10 : TreeBound (n := 3) 21 [((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (2, 0)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_10_0
  · exact bound6_10_1
  · exact bound6_10_2
  · exact bound6_10_3
  · exact bound6_10_4
  · exact bound6_10_5
  · exact bound6_10_6
  · exact bound6_10_7
  · exact bound6_10_8
  · exact bound6_10_9
  · exact bound6_10_10
  · exact bound6_10_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_0 : TreeBound (n := 3) 21 [((2, 1), ⟨0, 0, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714047381851501225889105042, 3714047381779439200516572370, 3714047381923554457316099538, 134483985, 403968273, 403968273, 403968273, 134483985, 138678289, 138678289, 293741104, 293741104],
    [26998765761642865433472607683609724540827674766069486947012, 26812567553427659937182068519810961975017997962724179282628, 344138288, 27045312561323708304122321767469953969340097199870852303556, 344138288, 26998762964876794696123510836083336534130581276985574394564, 2495375778335508519547176146, 79257329622891984296849445075, 79315814951190704135409767123, 79393795388922330586823529683, 2785535684493795433012921554, 79549756264385583489651054803],
    [3095039583781071980318557394, 2476031784630053735340573906, 3714047382355935273574073490, 2495375778335508519547176146, 79257329622891984434296787155, 79315814951190704272857109203, 79393795388922330724270871763, 2785535683917334680692720850, 79549756264385583627098396883, 3095039583204611227998356690, 2476031784630053735340573906, 293880432],
    [361054832, 293880432, 4766861965204298491260230226870033601817665767180175577527221, 2553412482971627439832304786, 5624862490316554192632487700110934242001872362384161005414581, 344277616, 2630802624892899583640865938, 344277616, 361054832, 293741104, 2476031784630051811195225298, 293741104],
    [9995403991578060355511849683, 2630783734273971559824753874, 19976300280682921691531318483, 344416880, 2630783734850467495443301522, 344416880, 2476031784630051811195225298, 293880432, 361054832, 293880432, 2495451338505498005275284626, 2630783736579815393739281618],
    [344277616, 2630821515511822935606301842, 344277616, 361054832, 293601840, 276824624, 293601840, 9995403991578060905301218003, 19976300280682922241320686803, 344003120, 39935675007253415655010207955, 344003120],
    [276824624]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_1 : TreeBound (n := 3) 21 [((2, 1), ⟨0, 0, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714047384085143686431654099]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_2 : TreeBound (n := 3) 21 [((2, 1), ⟨0, 1, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714198497578953054535943314, 6190078576077651578961659090, 3714198497578957452584551570, 403968273, 403968273, 403968273, 403968273, 403968273, 6190078133472887468997084626, 407114001, 6190078281055847257961792978, 407114001],
    [293741104, 293741104, 344138288, 344138288, 3714197916975483070877664402, 3714651265887044754286330067, 134488081, 134488081, 6190078576654112606159766738, 3715255728796852207394767059, 134488081, 134488081],
    [6190078133472887469101942226, 3714198054839089683228656786, 293880432, 361054832, 293880432, 5958351186377675146453408650871028796373409292499898086052, 2553563598699079268479143058, 5964169880384416194426599063045866549657311448739927044772, 344277616, 5106824374458080253171600594, 344277616, 361054832],
    [6190078576654112606277207250, 293880432, 361054832, 293880432, 4990824165325924283933922770, 2553563598699149637256875154, 344277616, 5106852709809899525439100114, 344277616, 361054832, 3714198497506891028223886482]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_3 : TreeBound (n := 3) 21 [((2, 1), ⟨0, 1, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [403968273, 403968273, 403964177, 403968273, 26812567553435786572824766835303159881456076441870669141829, 403968273, 26812567553435787234334318994277483802487388693861774874437, 403968273, 403968273, 403964177, 403968273, 403968273],
    [403968273, 403968273, 402915601, 403968273, 8937528200139326381353512890937661662001271039743281966741, 403968273, 6190077988056018567336853971, 403968273, 403968273, 403964177, 403968273, 1238015597149387802720470162],
    [403968273, 1238015597149388215062496402, 1238015597149388215096050834, 23856668179054072846991839771436902166429966843811682539333, 268730641, 308578161, 4952064752085652137572336083, 308578161, 4952062390902410702749729235, 340033809, 340033809, 287605617],
    [287605617, 337937265, 304382833, 321160049, 304382833, 388268913, 337937265, 337937265, 403968273, 403968273, 403964177, 403968273],
    [21046265225903027478123906258, 3387320716039226996432094761647662448157004470584527494647844, 403968273, 26812567553435785911315372392345914170959499063112970229573, 21046265225903027890465932498, 1239224597336944041869313234, 3339653974736134389381635985114435297598727361690633964949540, 287605617, 287605617, 337937265, 304382833, 321160049],
    [304382833, 388268913, 337937265, 337937265, 3050680171444832904825810764936650195009330188705618910566788, 4990750378313320271162933715, 4952062390902410702749729235, 4952064752085652137572336083, 4952062390902410702749729235, 3052163939831578948173836898387841566121674145662708665000324, 407142673, 3718731674236583939106014418],
    [1242851595593765760908002514, 6194611752879402117304026578, 1242851595593765760975111378, 1242851595593766860486739154, 26812567553435787234334318995461961310420264593785493870405, 407142673]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_4 : TreeBound (n := 3) 21 [((2, 1), ⟨1, 0, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [11142140383638236357103584402, 11142140964638049737990341842, 11142140392934224540976940498, 11142140383638234192307946642, 11142140374342237180127216850, 11142140392934222410543138258, 11142140374342237179053474962, 11142140374342237316500817042, 11142140374342237316509205650, 19495111739455525846253779, 23274798245143713767128784335561698238321430241283676805, 572686896],
    [572686896, 572686896, 572686896, 606241328, 572686896, 606241328, 572686896, 1361348465, 1361348465, 570458672, 536904240, 570458672],
    [536904240, 606241328, 536904240, 606241328, 536904240, 11142140411816727061932934290, 1361348465, 1361348465, 570458672, 536904240, 570458672, 536904240],
    [604144176, 536904240, 604144176, 536904240, 9923468919634539635477187730, 11142083854680343829266173138, 9942812913339924052013354450, 11142083854680343829266173138, 574915184, 541360752, 574915184, 574915184],
    [608600688, 642155120, 608600688, 642155120, 9923469361775362684905194706, 289702161, 9942813355480817469111796946, 289702161, 570458672, 536904240, 570458672, 536904240],
    [610697840, 536904240, 610697840, 536904240, 9923468920796538708082955410, 9923470101388159425494258834, 574915184, 541360752, 574915184, 574915184, 608600688, 642155120],
    [608600688, 642155120, 289702161, 289702161, 570458672, 536904240, 570458672, 536904240, 606241328, 536904240, 606241328, 536904240]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_5 : TreeBound (n := 3) 21 [((2, 1), ⟨1, 0, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [9981609959081597606415110867, 10523208726268951579768984275, 50645958803419360495923028457401256320509953184225930652677, 10523208726268951717216326355, 3050685990138498230204608971532253211271426398098566889397044, 3241364592738876689668717491911948661102469930529761260277988, 3074530998178057984074608153116174570782092893558111080851684, 9904238706626262404450816723, 9923469363536129416751026899, 9923543740808232448867504851, 9981572180149735164680934099, 9981572180149735714470302419],
    [47690061559906354628882494289925388070943640672149707843781, 556040817, 556040817, 556040817, 560236145, 558137969, 558137969, 571572784, 9981500763544589600454415059, 571572784, 572686896, 33587760],
    [572686896, 33587760, 574915184, 33587760, 574915184, 33587760, 9981501344652493769370833619, 571572784, 571572784, 572686896, 33587760, 572686896],
    [33587760, 574915184, 33587760, 574915184, 33587760, 10058877319474312906197243603, 10523133168405227727155696339, 10213629269117951179850062547, 3266661457265239350896238748742409759318342333766329611129156, 9923543159700330444746724051, 69239344, 67142192],
    [69239344, 67142192, 1145340528, 1145340528, 1145340528, 67142192, 10523133168405227727155696339]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_6 : TreeBound (n := 3) 21 [((2, 1), ⟨1, 1, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [11142744846548043671690937490, 135528465, 403968273, 135528465, 403968273, 135528465, 11142744846548611019690869906, 135528465, 403968273, 135528465, 403968273, 11142744837252044631088170130],
    [135528465, 11142744911620020874571285650, 21046265225903028440255300818, 572686896, 572686896, 572686896, 572686896, 606241328, 572686896, 606241328, 572686896, 556040817],
    [556040817, 570458672, 536904240, 570458672, 536904240, 606241328, 536904240, 606241328, 536904240, 134512657, 556040817, 556040817],
    [570458672, 536904240, 570458672, 536904240, 604144176, 536904240, 604144176, 536904240, 9924073382544346950064540818, 17072145, 19846937690532773565793701330, 17072145],
    [574915184, 541360752, 574915184, 574915184, 608600688, 642155120, 608600688, 642155120, 138706961, 9924073382553424518063459474, 19846937839268654859331704274, 574915184],
    [541360752, 574915184, 574915184, 608600688, 642155120, 608600688, 642155120, 138706961]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_7 : TreeBound (n := 3) 21 [((2, 1), ⟨1, 1, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3050685990138498230204608971229026936545071587670209451593524, 19963105988729783387376719059, 20427333503461801093549397203, 20427333503461801230996739283, 190667149887808093589879386696347370767757092491394359570565, 19808363483819111918231229651, 19827594140728978930531439827, 8958980170203942451378438371230576586463937519737542918754372455819887482953553981280303346341198048790, 19827668518001081962647917779, 190853348273594393251603819686537992213710092796017659949189, 19963068209797920945642542291, 19963068209797921495431910611],
    [190690421844868311049895619041001294470898584190491166338373, 556040817, 556040817, 556040817, 560236145, 558137969, 190690421844868311049895619043389048692922716731970033380677, 558137969, 19963001515559258251061236947, 572686896, 33587760, 572686896],
    [33587760, 38044272, 33587760, 38044272, 33587760, 19885626121845343283151247059, 572686896, 33587760, 572686896, 33587760, 38044272, 33587760],
    [38044272, 33587760, 19963002096667162419977655507, 20427257945598077240936109267, 20117754046310800693630475475, 19827667936893179958527136979, 606241328, 67142192, 606241328, 67142192, 71336496, 71336496],
    [71336496, 67142192, 20427257945598077240936109267]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_8 : TreeBound (n := 3) 21 [((2, 1), ⟨2, 0, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [39635843693961967543611690130, 40854458629007824513958808786, 39655187687667351960147856850, 40854440339025539215128661202, 40854441528841094919348162002, 1898219377, 17072145, 1898219377, 17072145, 21266449, 21266449, 1108705904],
    [39693875675051028824564305618, 1108705904, 1109820016, 1114014320, 1109820016, 1111786096, 1111786096, 1114014320, 1111786096, 1111786096, 89213895099285482565026779859, 39693880397444814765876710546],
    [99194791388390343901046248659, 1149534832, 1082425968, 1149534832, 1149534832]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_9 : TreeBound (n := 3) 21 [((2, 1), ⟨2, 0, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2496433007392106219233739922, 2496433007392669169187161234, 19827593622459378134818096338, 5964525030904571325770831472769842246857346121116232503140, 20552919529856688216736914, 5965616036030832295400902383005862802703293340508929930084, 20552919561381885608330386, 39635843695114677958092261587, 23274798396877987973963681169308252236506596492603886980, 23274798396878003478093824325200977665588409803373228100, 19846937616164832919024698578, 23274798396878313560696687640468236887015161731577208292],
    [39896913235311473497081042, 23274798396879305825025849617602664348251213620806836292, 39896913266836670888674514, 4479491637030051514652572078315991732613671510815318696150802286185773801912467708050301776918708475799, 1092912753, 1095009361, 1092912753, 1095009361, 1095009361, 77376565117631696837149906, 572686896, 33587760],
    [572686896, 33587760, 1648788080, 33587760, 1648788080, 33587760, 39693875676231042310712072915, 154752539975761105659233490, 39771251651052861447538482387, 1149534832, 8421936, 1149534832],
    [8421936]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_10 : TreeBound (n := 3) 21 [((2, 1), ⟨2, 1, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [39638261545601267170705280146, 79387779094023436015679706322, 1149518448, 79387779094023436050041541842, 1149510256, 1149510256, 1149518448, 1149518448, 1149518448, 1149518448, 79271686797591671519876093394, 79252417181158324165832479954],
    [79852044387687317641145488594, 79271759994272162665036125650, 79852044387687317091356120274, 79852044387687317641145488594, 43524283327192104297300179, 1108705904, 79310374784984425952291460818, 1108705904, 1109820016, 1114014320, 1109820016, 1111786096],
    [1111786096, 1114014320, 1111786096, 1111786096, 1108705904, 1108705904, 1143243376, 1074037360, 1143243376, 1078231664, 1078231664, 1074037360],
    [1078231664, 1078231664, 39696298249084114392970300562, 1176928880, 1145340528, 1176928880, 1145340528, 1145340528, 1145340528, 1145340528, 1145340528, 1149534832],
    [1082425968, 1149534832, 1149534832]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_11 : TreeBound (n := 3) 21 [((2, 1), ⟨2, 1, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [293671472, 25166384, 293671472, 19344584037296141102089426, 19344584037296141102089426, 1099186800, 1099186800, 25166384, 79252342803886076013213913299, 293671472, 25166384, 293671472],
    [1099186800, 38688577742748726302213330, 1099186800, 25166384, 1525360451171382216673125853197516432906647522963927027648325, 1092912753, 1095009361, 1092912753, 1095009361, 1525360451171382217996144957516649557038506501813206556575557, 1095009361, 77376565117631696837149906],
    [572686896, 33587760, 572686896, 33587760, 1111786096, 33587760, 1111786096, 33587760, 79310374785002440365833720531, 572686896, 33587760, 572686896],
    [33587760, 1111786096, 33587760, 1111786096, 33587760, 79387750759824259502660130003, 75530800, 8421936, 75530800, 8421936]
  ]) (by decide) ?_
  decide +kernel

theorem bound6_11 : TreeBound (n := 3) 21 [((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (2, 1)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_11_0
  · exact bound6_11_1
  · exact bound6_11_2
  · exact bound6_11_3
  · exact bound6_11_4
  · exact bound6_11_5
  · exact bound6_11_6
  · exact bound6_11_7
  · exact bound6_11_8
  · exact bound6_11_9
  · exact bound6_11_10
  · exact bound6_11_11

theorem bound6 : TreeBound (n := 3) 21 [((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (1, 0)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_0
  · exact bound6_1
  · exact bound6_2
  · exact bound6_3
  · exact bound6_4
  · exact bound6_5
  · exact bound6_6
  · exact bound6_7
  · exact bound6_8
  · exact bound6_9
  · exact bound6_10
  · exact bound6_11

theorem initialBound : TreeBound (n := 3) 21 [] := by
  apply canonical_start (by decide) (by decide)
  · intro a
    fin_cases a
    · exact bound0
    · exact bound2
  · intro a
    fin_cases a
    · exact bound4
    · exact bound6

end BeaverBound


theorem OMA.solution : OMA.R_Constant14_c14_ge_4_R1.H2 := by
  intro n _ M hn hnohalt
  have hn3 : n ≤ 3 := Nat.le_of_lt_succ hn
  have hupper := BeaverBound.initialBound (C14H2.padTo3 hn3 M) (BeaverBound.matches_empty _)
  rcases hupper with hhalts | hinv
  · exfalso
    apply hnohalt
    exact (Turing.BusyBeaver.Machine.isHalting_iff_exists_haltsAt M).mpr
      ⟨21, (C14H2.padTo3_haltsAfter hn3 M 21).mp hhalts⟩
  · apply C14Completeness.zfc_complete _
    intro V mem hZFC
    rw [C14Completeness.evalM, C14Completeness.evalRaw_neg]
    let M0 : C14Stage2.ZFCModel := ⟨V, mem, hZFC⟩
    exact C14H2.not_halts_of_invariant M0 M (C14H2.padTo3_invariant M0 hn3 M (hinv M0))
