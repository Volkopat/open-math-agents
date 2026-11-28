import Mathlib

namespace OMA.S_arxiv_1910_05120

/-- Side of a sequent on which the principal formula of a visible rule appears. -/
inductive Side : Type
  | left
  | right
  deriving DecidableEq

/-- A visible inference rule scheme for an `n`-ary connective `C(A_1, ..., A_n)` (without
implication/negation, as in Nishimuta, arXiv:1910.05120):
- `premises` is a finite nonempty set of pairs `(Γ_i, acts_i)` where `Γ_i` is the passive-side
  context variable set and `acts_i` is the nonempty multiset of active subformula indices;
- `conclCtx` is the passive-side context variable set of the conclusion;
- distinct premises do not duplicate the same active multiset with conflicting contexts. -/
structure VisibleRule (n : ℕ) where
  premises : Finset (Finset ℕ × Multiset (Fin n))
  conclCtx : Finset ℕ
  premises_nonempty : premises.Nonempty
  active_nonempty : ∀ p ∈ premises, p.2 ≠ 0
  active_ctx_det : ∀ p₁ ∈ premises, ∀ p₂ ∈ premises, p₁.2 = p₂.2 → p₁.1 = p₂.1
  deriving DecidableEq

/-- The set of active formula multisets occurring in the premises of a rule `F`. -/
def VisibleRule.activeSets {n : ℕ} (F : VisibleRule n) : Finset (Multiset (Fin n)) :=
  F.premises.image Prod.snd

/-- A rule `F` is context-changing (`Cxt_Prem(F) ≠ Cxt_Concl(F)`, Definition 3 of arXiv:1910.05120)
if some premise has a passive context different from the conclusion context. -/
def VisibleRule.IsContextChanging {n : ℕ} (F : VisibleRule n) : Prop :=
  ∃ p ∈ F.premises, p.1 ≠ F.conclCtx

/-- A definitional equation (set of formation rules) `E` is context-changing if some formation rule
in `E` is context-changing. -/
def IsContextChanging {n : ℕ} (E : Finset (VisibleRule n)) : Prop :=
  ∃ F ∈ E, F.IsContextChanging

/-- The unary explicit reflection rule for an active formula multiset `acts` with fresh passive
context `{0}`. -/
def explicitReflectionRule {n : ℕ} (acts : Multiset (Fin n)) (h : acts ≠ 0) : VisibleRule n where
  premises := {({0}, acts)}
  conclCtx := {0}
  premises_nonempty := Finset.singleton_nonempty _
  active_nonempty := by
    intro p hp
    rw [Finset.mem_singleton.mp hp]
    exact h
  active_ctx_det := by
    intro p₁ hp₁ p₂ hp₂ _
    rw [Finset.mem_singleton.mp hp₁, Finset.mem_singleton.mp hp₂]

/-- The set of explicit reflection rules obtained from a set of formation rules `E` via Sambin et
al.'s reflection procedure (substituting `C(A_1, ..., A_n)` for the passive context and cutting
active subformulas against a fresh context `{0}`). -/
def explicitReflectionRules {n : ℕ} (E : Finset (VisibleRule n)) : Finset (VisibleRule n) :=
  E.biUnion (fun F =>
    F.premises.attach.image (fun p => explicitReflectionRule p.1.2 (F.active_nonempty p.1 p.2)))

/-- Main step of cut elimination between a set of left rules `L` and a set of right rules `R`:
for every right rule `rR ∈ R` and every left rule `rL ∈ L`, cutting `rR`'s conclusion against
`rL`'s conclusion reduces to cutting on matching active subformulas without altering the passive
contexts (`Γ_i = rR.conclCtx` and `Δ_j = rL.conclCtx`). -/
def MainStepCutElim {n : ℕ} (L R : Finset (VisibleRule n)) : Prop :=
  ∀ rR ∈ R, ∀ rL ∈ L,
    ∃ pR ∈ rR.premises, ∃ pL ∈ rL.premises,
      pR.2 = pL.2 ∧ pR.1 = rR.conclCtx ∧ pL.1 = rL.conclCtx

/-- Solvability of a definitional equation `E` (Definition 2 of arXiv:1910.05120): `E` is nonempty,
distinct rules in `E` have distinct active premise sets (no trivial context-renaming duplicates),
and the main step of cut elimination holds between `E` and its explicit reflection rules. -/
def IsSolvableDefEq {n : ℕ} (E : Finset (VisibleRule n)) : Prop :=
  E.Nonempty ∧
  (∀ F₁ ∈ E, ∀ F₂ ∈ E, F₁.activeSets = F₂.activeSets → F₁ = F₂) ∧
  MainStepCutElim (explicitReflectionRules E) E

/-- A logical connective presentation `(L, R)` of arity `n` satisfies Sambin et al.'s principle
of reflection if either its right rules form a solvable definitional equation whose explicit
reflection rules are `L`, or dually its left rules form a solvable definitional equation whose
explicit reflection rules are `R`. -/
def SatisfiesReflectionPrinciple {n : ℕ} (L R : Finset (VisibleRule n)) : Prop :=
  (IsSolvableDefEq R ∧ L = explicitReflectionRules R) ∨
  (IsSolvableDefEq L ∧ R = explicitReflectionRules L)

/-- One-sided Deducibility of Identicals (Hacking 1979 / Naibo-Petrolo 2015): there is a
non-context-changing rule `F ∈ E` such that every premise of `F` can be immediately closed by a
matching unary rule in `opp` applied to identity axioms. -/
def SatisfiesDoIOn {n : ℕ} (E opp : Finset (VisibleRule n)) : Prop :=
  ∃ F ∈ E, ¬ F.IsContextChanging ∧
    ∀ p ∈ F.premises, ∃ r ∈ opp,
      r.premises = {(r.conclCtx, p.2)}

/-- Deducibility of Identicals for a pair of rule sets `(L, R)`. -/
def SatisfiesDoI {n : ℕ} (L R : Finset (VisibleRule n)) : Prop :=
  SatisfiesDoIOn R L ∨ SatisfiesDoIOn L R

/-- Uniqueness condition (Belnap 1962 / Lemma 3 of arXiv:1910.05120): for any connective `(L, R)`
and any copy of the same inference rules, both directions `C ⊢ C*` and `C* ⊢ C` are derivable
by composing the formation rule of one with the reflection rules of the other (equivalently, the
two rule sets mutually close each other's formation premises). -/
def SatisfiesUniqueness {n : ℕ} (L R : Finset (VisibleRule n)) : Prop :=
  SatisfiesDoI L R ∧ MainStepCutElim L R

/-- A connective `(L, R)` is a Girard synthetic connective (Definition 1, Schemes I & II of
arXiv:1910.05120) if it consists of a single non-context-changing formation rule `F` on one side
and the corresponding unary reflection rules `{A_{i1}, ..., A_{ik_i} ⊢ Δ / C ⊢ Δ}` on the
opposite side. -/
def IsSyntheticConnective {n : ℕ} (L R : Finset (VisibleRule n)) : Prop :=
  (∃ F : VisibleRule n, ¬ F.IsContextChanging ∧
      R = {F} ∧ L = explicitReflectionRules {F}) ∨
  (∃ F : VisibleRule n, ¬ F.IsContextChanging ∧
      L = {F} ∧ R = explicitReflectionRules {F})

/-- Main results of Yuki Nishimuta (arXiv:1910.05120):
1. Lemma 1: Every context-changing definitional equation is unsolvable.
2. Lemma 2: Every definitional equation with multiple formation rules is unsolvable.
3. Theorem 2 (Characterization of Synthetic Connectives): An `n`-ary connective `(L, R)`
   satisfies the principle of reflection if and only if it is a Girard synthetic connective.
4. Theorem 1 / Corollaries 1 & 2 (Equivalence of Reflection Principle, DoI, and Uniqueness):
   for any connective `(L, R)` whose one side consists of canonical unary reflection rules
   `{0}` and whose opposite side is irredundant, `(L, R)` satisfies the reflection principle
   iff it satisfies the main step of cut elimination and DoI (and iff it satisfies uniqueness).
5. Refutation of Sambin et al.'s conjecture that only 6 connectives satisfy the principle of
   reflection: even at arity `n = 3`, there exist strictly more than `6` distinct connectives
   `(L, R)` satisfying the principle of reflection (in fact, for every `k : ℕ`, there exist at
   least `k` distinct connectives across arities satisfying the principle of reflection). -/
theorem main :
    (∀ (n : ℕ) (E : Finset (VisibleRule n)), IsContextChanging E → ¬ IsSolvableDefEq E) ∧
    (∀ (n : ℕ) (E : Finset (VisibleRule n)), 1 < E.card → ¬ IsSolvableDefEq E) ∧
    (∀ (n : ℕ) (L R : Finset (VisibleRule n)),
      SatisfiesReflectionPrinciple L R ↔ IsSyntheticConnective L R) ∧
    (∀ (n : ℕ) (L R : Finset (VisibleRule n)),
      (∀ F₁ ∈ R, ∀ F₂ ∈ R, F₁.activeSets ⊆ F₂.activeSets → F₁ = F₂) →
      (∀ r ∈ L, ∃ acts : Multiset (Fin n), ∃ h : acts ≠ 0, r = explicitReflectionRule acts h) →
      ((IsSolvableDefEq R ∧ L = explicitReflectionRules R) ↔
        (MainStepCutElim L R ∧ SatisfiesDoIOn R L))) ∧
    (∃ S : Finset (Finset (VisibleRule 3) × Finset (VisibleRule 3)),
      6 < S.card ∧ ∀ p ∈ S, SatisfiesReflectionPrinciple p.1 p.2) := by sorry

end OMA.S_arxiv_1910_05120
