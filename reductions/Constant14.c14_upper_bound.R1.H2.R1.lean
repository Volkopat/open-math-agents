import OMAReductions.R_Constant14_c14_upper_bound_R1
import Mathlib.Tactic

/-!
# Reduction `Constant14.c14_upper_bound.R1.H2.R1`

Reduces `OMA.R_Constant14_c14_upper_bound_R1.H2` (assuming `𝗭𝗙𝗖 ⊬ ⊥`, there exists a 230-state
binary Turing machine `M` that does not halt and whose non-halting sentence `∼Constant14.halts M`
is unprovable in `𝗭𝗙𝗖`) to two independent, orthogonal pillars:

* `H1`: **Conservativity of the Axiom of Choice over `𝗭𝗙` for Turing machine non-halting**
  (Gödel's constructible universe `L` / Shoenfield absoluteness): if `𝗭𝗙𝗖` proves
  `∼Constant14.halts M`, then `𝗭𝗙` already proves it. Identical to `Constant14.c14_le_20.R1.H1`.
* `H2`: **230-state `𝗭𝗙`-inconsistency searcher and Hilbert–Bernays–Löb provability** (Glazer
  2026 `K230` [G2026] combined with `𝗭𝗙 ⊢ Con(𝗭𝗙) ↔ Con(𝗭𝗙𝗖)`): there exist a 230-state binary
  Turing machine `M` and a provability predicate `P` for `𝗭𝗙` satisfying HBL (D1)–(D3) with a
  Gödel fixed point `G 🡘 ∼P G`, such that `M.IsHalting → 𝗭𝗙 ⊢ ⊥` and
  `𝗭𝗙 ⊢ ∼Constant14.halts M 🡒 ∼P ⊥`.

Inside `main`, we build the one-sided Tait/Gentzen sequent calculus (`FFL.FirstOrder.Derivation`)
completely from scratch with zero extra definitions (generalized excluded middle `⦃φ, ∼φ⦄` by
formula-size induction, double negation, `⋎`-inversion, conjunction projections, modus ponens,
implication transitivity, S-combinator contraction, contraposition, cut-to-`⊥`, and theory
monotonicity `𝗭𝗙 ⊆ 𝗭𝗙𝗖`), prove **Gödel's Second Incompleteness Theorem** (`𝗭𝗙 ⊬ ⊥ → 𝗭𝗙 ⊬ ∼P ⊥`)
from (D1)–(D3) and `G`, deduce `¬ M.IsHalting` and `𝗭𝗙 ⊬ ∼Constant14.halts M`, and lift
unprovability to `𝗭𝗙𝗖` via `H1`.

Credits: Built by `@Narden91`, adapting the one-sided LK Gödel Second Incompleteness Theorem
machinery from `Constant14.c14_le_432.R1` (`@tkaiman`).
-/

namespace OMA.R_Constant14_c14_upper_bound_R1_H2_R1

open FFL FFL.FirstOrder Turing BusyBeaver FFL.FirstOrder.SetTheory Constant14

/-- Conservativity of the Axiom of Choice over `𝗭𝗙` for Turing machine non-halting
(Gödel's constructible universe / Shoenfield absoluteness). -/
def H1 : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : Machine (Fin 2) (Fin n)),
    FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M) →
    FFL.Entailment.Provable 𝗭𝗙 (∼Constant14.halts M)

/-- 230-state `𝗭𝗙`-inconsistency searcher and Hilbert–Bernays–Löb provability ([G2026]):
there exist a 230-state binary Turing machine `M` and a provability predicate `P` for `𝗭𝗙`
satisfying the Hilbert–Bernays–Löb derivability conditions (D1)–(D3) with a Gödel fixed point
`G 🡘 ∼P G`, such that `M.IsHalting → 𝗭𝗙 ⊢ ⊥` and `𝗭𝗙 ⊢ ∼halts M 🡒 ∼P ⊥`. -/
def H2 : Prop :=
  ∃ (M : BusyBeaver.Machine (Fin 2) (Fin 230))
    (P : SetTheorySentence → SetTheorySentence),
    (M.IsHalting → Entailment.Provable 𝗭𝗙 ⊥) ∧
    (∀ φ, Entailment.Provable 𝗭𝗙 φ → Entailment.Provable 𝗭𝗙 (P φ)) ∧
    (∀ φ ψ, Entailment.Provable 𝗭𝗙 (P (φ 🡒 ψ) 🡒 (P φ 🡒 P ψ))) ∧
    (∀ φ, Entailment.Provable 𝗭𝗙 (P φ 🡒 P (P φ))) ∧
    (∃ G, Entailment.Provable 𝗭𝗙 (G 🡘 ∼P G)) ∧
    Entailment.Provable 𝗭𝗙 (∼Constant14.halts M 🡒 ∼P ⊥)

section Helpers

/- ## Step 1: Negation Involution and Rewriting Lemmas for `FFL.FirstOrder.Semiformula` -/

private lemma neg_neg_sf {L : FFL.FirstOrder.Language} {ξ : Type*} :
    ∀ {n : ℕ} (φ : Semiformula L ξ n), ∼(∼φ) = φ
  | _, .verum => rfl
  | _, .falsum => rfl
  | _, .rel _ _ => rfl
  | _, .nrel _ _ => rfl
  | _, .and φ ψ => by
    change Semiformula.and (∼(∼φ)) (∼(∼ψ)) = Semiformula.and φ ψ
    rw [neg_neg_sf φ, neg_neg_sf ψ]
  | _, .or φ ψ => by
    change Semiformula.or (∼(∼φ)) (∼(∼ψ)) = Semiformula.or φ ψ
    rw [neg_neg_sf φ, neg_neg_sf ψ]
  | _, .all φ => by
    change Semiformula.all (∼(∼φ)) = Semiformula.all φ
    rw [neg_neg_sf φ]
  | _, .exs φ => by
    change Semiformula.exs (∼(∼φ)) = Semiformula.exs φ
    rw [neg_neg_sf φ]

private lemma rew_func {L : FFL.FirstOrder.Language} {ξ₁ ξ₂ : Type*} {n₁ n₂ k : ℕ}
    (ω : Rew L ξ₁ n₁ ξ₂ n₂) (f : L.Func k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (Semiterm.func f v) = Semiterm.func f (fun i => ω (v i)) :=
  ω.func'' f v

private lemma rewAux_comp {L : FFL.FirstOrder.Language} {n₁ n₂ n₃ : ℕ}
    (ω₂ : SyntacticRew L n₂ n₃) (ω₁ : SyntacticRew L n₁ n₂)
    (φ : Semiproposition L n₁) :
    Semiformula.rewAux ω₂ (Semiformula.rewAux ω₁ φ) =
      Semiformula.rewAux (ω₂.comp ω₁) φ := by
  have hq : ∀ {m₁ m₂ m₃ : ℕ} (τ₂ : SyntacticRew L m₂ m₃) (τ₁ : SyntacticRew L m₁ m₂),
      τ₂.q.comp τ₁.q = (τ₂.comp τ₁).q := by
    intro m₁ m₂ m₃ τ₂ τ₁
    have hterm : ∀ t : Semiterm L ℕ (m₁ + 1),
        (τ₂.q.comp τ₁.q) t = (τ₂.comp τ₁).q t := by
      have hbshift : ∀ {k₁ k₂ : ℕ} (σ : SyntacticRew L k₁ k₂) (s : Semiterm L ℕ k₁),
          σ.q (Rew.bShift s) = Rew.bShift (σ s) := by
        intro k₁ k₂ σ s
        induction s with
        | bvar x => rfl
        | fvar x => rfl
        | func f v ih =>
          rw [rew_func Rew.bShift, rew_func σ.q, rew_func σ, rew_func Rew.bShift]
          congr 1; funext i; exact ih i
      intro t
      induction t with
      | bvar x =>
        cases x using Fin.cases with
        | zero => rfl
        | succ i =>
          change τ₂.q (Rew.bShift (τ₁ #i)) = Rew.bShift (τ₂ (τ₁ #i))
          exact hbshift τ₂ (τ₁ #i)
      | fvar x =>
        change τ₂.q (Rew.bShift (τ₁ &x)) = Rew.bShift (τ₂ (τ₁ &x))
        exact hbshift τ₂ (τ₁ &x)
      | func f v ih =>
        rw [rew_func (τ₂.q.comp τ₁.q), rew_func (τ₂.comp τ₁).q]
        congr 1; funext i; exact ih i
    exact DFunLike.coe_injective (funext hterm)
  induction φ generalizing n₂ n₃ with
  | verum => rfl
  | falsum => rfl
  | rel r v => rfl
  | nrel r v => rfl
  | and φ₁ φ₂ ih₁ ih₂ =>
    change Semiformula.and (Semiformula.rewAux ω₂ (Semiformula.rewAux ω₁ φ₁))
        (Semiformula.rewAux ω₂ (Semiformula.rewAux ω₁ φ₂)) =
      Semiformula.and (Semiformula.rewAux (ω₂.comp ω₁) φ₁) (Semiformula.rewAux (ω₂.comp ω₁) φ₂)
    rw [ih₁, ih₂]
  | or φ₁ φ₂ ih₁ ih₂ =>
    change Semiformula.or (Semiformula.rewAux ω₂ (Semiformula.rewAux ω₁ φ₁))
        (Semiformula.rewAux ω₂ (Semiformula.rewAux ω₁ φ₂)) =
      Semiformula.or (Semiformula.rewAux (ω₂.comp ω₁) φ₁) (Semiformula.rewAux (ω₂.comp ω₁) φ₂)
    rw [ih₁, ih₂]
  | all φ ih =>
    change Semiformula.all (Semiformula.rewAux ω₂.q (Semiformula.rewAux ω₁.q φ)) =
      Semiformula.all (Semiformula.rewAux (ω₂.comp ω₁).q φ)
    rw [ih, hq]
  | exs φ ih =>
    change Semiformula.exs (Semiformula.rewAux ω₂.q (Semiformula.rewAux ω₁.q φ)) =
      Semiformula.exs (Semiformula.rewAux (ω₂.comp ω₁).q φ)
    rw [ih, hq]

private lemma subst_zero_shift_q_eq_free {L : FFL.FirstOrder.Language} (φ : Semiproposition L 1) :
    (Rew.subst (![&0] : Fin 1 → Semiterm L ℕ 0) ▹ (Rew.shift.q ▹ φ)) = φ.free := by
  have heq : (Rew.subst (![&0] : Fin 1 → Semiterm L ℕ 0)).comp (Rew.shift (L := L) (n := 0)).q =
      Rew.free (L := L) (n := 0) := by
    apply DFunLike.coe_injective
    funext t
    induction t with
    | bvar x =>
      fin_cases x
      rfl
    | fvar m => rfl
    | func f v ih =>
      rw [rew_func ((Rew.subst (![&0] : Fin 1 → Semiterm L ℕ 0)).comp
        (Rew.shift (L := L) (n := 0)).q), rew_func (Rew.free (L := L) (n := 0))]
      congr 1; funext i; exact ih i
  change Semiformula.rewAux _ (Semiformula.rewAux _ φ) = Semiformula.rewAux _ φ
  rw [rewAux_comp, heq]

/- ## Step 2: One-Sided Tait/Gentzen Sequent Calculus (`Derivation`) Derived Rules -/

private lemma neg_em {L : FFL.FirstOrder.Language} (φ : Proposition L) :
    Nonempty (Derivation ⦃φ, ∼φ⦄) := by
  let fSize : {n : ℕ} → Semiproposition L n → ℕ :=
    fun {n} ψ =>
      @Semiformula.rec L ℕ (fun _ _ => ℕ)
        0 0 (fun _ _ => 0) (fun _ _ => 0)
        (fun _ _ a b => a + b + 1) (fun _ _ a b => a + b + 1)
        (fun _ a => a + 1) (fun _ a => a + 1) n ψ
  have fSize_rewAux : ∀ {n₁ n₂ : ℕ} (ω : SyntacticRew L n₁ n₂) (ψ : Semiproposition L n₁),
      fSize (Semiformula.rewAux ω ψ) = fSize ψ := by
    intro n₁ n₂ ω ψ
    induction ψ generalizing n₂ with
    | verum => rfl
    | falsum => rfl
    | rel _ _ => rfl
    | nrel _ _ => rfl
    | and ψ₁ ψ₂ ih₁ ih₂ =>
      change fSize (Semiformula.rewAux ω ψ₁) + fSize (Semiformula.rewAux ω ψ₂) + 1 =
        fSize ψ₁ + fSize ψ₂ + 1
      rw [ih₁, ih₂]
    | or ψ₁ ψ₂ ih₁ ih₂ =>
      change fSize (Semiformula.rewAux ω ψ₁) + fSize (Semiformula.rewAux ω ψ₂) + 1 =
        fSize ψ₁ + fSize ψ₂ + 1
      rw [ih₁, ih₂]
    | all ψ₁ ih =>
      change fSize (Semiformula.rewAux ω.q ψ₁) + 1 = fSize ψ₁ + 1
      rw [ih]
    | exs ψ₁ ih =>
      change fSize (Semiformula.rewAux ω.q ψ₁) + 1 = fSize ψ₁ + 1
      rw [ih]
  have fSize_neg : ∀ {n : ℕ} (ψ : Semiproposition L n), fSize (∼ψ) = fSize ψ := by
    intro n ψ
    induction ψ with
    | verum => rfl
    | falsum => rfl
    | rel _ _ => rfl
    | nrel _ _ => rfl
    | and ψ₁ ψ₂ ih₁ ih₂ =>
      change fSize (∼ψ₁) + fSize (∼ψ₂) + 1 = fSize ψ₁ + fSize ψ₂ + 1
      rw [ih₁, ih₂]
    | or ψ₁ ψ₂ ih₁ ih₂ =>
      change fSize (∼ψ₁) + fSize (∼ψ₂) + 1 = fSize ψ₁ + fSize ψ₂ + 1
      rw [ih₁, ih₂]
    | all ψ₁ ih =>
      change fSize (∼ψ₁) + 1 = fSize ψ₁ + 1
      rw [ih]
    | exs ψ₁ ih =>
      change fSize (∼ψ₁) + 1 = fSize ψ₁ + 1
      rw [ih]
  have aux : ∀ (k : ℕ) (ψ : Proposition L), fSize ψ ≤ k → Nonempty (Derivation ⦃ψ, ∼ψ⦄) := by
    intro k
    induction k with
    | zero =>
      intro ψ h
      cases ψ with
      | verum =>
        exact ⟨Derivation.contraction Derivation.verum (by
          intro x hx
          simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          exact Or.inl hx)⟩
      | falsum =>
        exact ⟨Derivation.contraction Derivation.verum (by
          intro x hx
          simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          exact Or.inr hx)⟩
      | rel r v => exact ⟨Derivation.identity r v⟩
      | nrel r v =>
        exact ⟨Derivation.contraction (Derivation.identity r v) (by
          intro x hx
          simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          exact hx.symm)⟩
      | and ψ₁ ψ₂ =>
        change fSize ψ₁ + fSize ψ₂ + 1 ≤ 0 at h; omega
      | or ψ₁ ψ₂ =>
        change fSize ψ₁ + fSize ψ₂ + 1 ≤ 0 at h; omega
      | all ψ₁ =>
        change fSize ψ₁ + 1 ≤ 0 at h; omega
      | exs ψ₁ =>
        change fSize ψ₁ + 1 ≤ 0 at h; omega
    | succ k ih =>
      intro ψ h
      cases ψ with
      | verum =>
        exact ⟨Derivation.contraction Derivation.verum (by
          intro x hx
          simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          exact Or.inl hx)⟩
      | falsum =>
        exact ⟨Derivation.contraction Derivation.verum (by
          intro x hx
          simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          exact Or.inr hx)⟩
      | rel r v => exact ⟨Derivation.identity r v⟩
      | nrel r v =>
        exact ⟨Derivation.contraction (Derivation.identity r v) (by
          intro x hx
          simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          exact hx.symm)⟩
      | and ψ₁ ψ₂ =>
        change fSize ψ₁ + fSize ψ₂ + 1 ≤ k + 1 at h
        obtain ⟨d1⟩ := ih ψ₁ (by omega)
        obtain ⟨d2⟩ := ih ψ₂ (by omega)
        have dφ : Derivation (⦃∼ψ₁, ∼ψ₂⦄ + ⦃ψ₁⦄) :=
          Derivation.contraction d1 (by
            intro x hx
            simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
            rcases hx with rfl | rfl
            · exact Or.inr rfl
            · exact Or.inl (Or.inl rfl))
        have dψ : Derivation (⦃∼ψ₁, ∼ψ₂⦄ + ⦃ψ₂⦄) :=
          Derivation.contraction d2 (by
            intro x hx
            simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
            rcases hx with rfl | rfl
            · exact Or.inr rfl
            · exact Or.inl (Or.inr rfl))
        have dand : Derivation (⦃ψ₁ ⋏ ψ₂⦄ + ⦃∼ψ₁, ∼ψ₂⦄) :=
          Derivation.contraction (Derivation.and dφ dψ) (by
            intro x hx
            simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
            rcases hx with (rfl | rfl) | rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr rfl)
            · exact Or.inl rfl)
        exact ⟨Derivation.or dand⟩
      | or ψ₁ ψ₂ =>
        change fSize ψ₁ + fSize ψ₂ + 1 ≤ k + 1 at h
        obtain ⟨d1⟩ := ih ψ₁ (by omega)
        obtain ⟨d2⟩ := ih ψ₂ (by omega)
        have dφ : Derivation (⦃ψ₁, ψ₂⦄ + ⦃∼ψ₁⦄) :=
          Derivation.contraction d1 (by
            intro x hx
            simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
            rcases hx with rfl | rfl
            · exact Or.inl (Or.inl rfl)
            · exact Or.inr rfl)
        have dψ : Derivation (⦃ψ₁, ψ₂⦄ + ⦃∼ψ₂⦄) :=
          Derivation.contraction d2 (by
            intro x hx
            simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
            rcases hx with rfl | rfl
            · exact Or.inl (Or.inr rfl)
            · exact Or.inr rfl)
        have dand : Derivation (⦃∼ψ₁ ⋏ ∼ψ₂⦄ + ⦃ψ₁, ψ₂⦄) :=
          Derivation.contraction (Derivation.and dφ dψ) (by
            intro x hx
            simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
            rcases hx with (rfl | rfl) | rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr rfl)
            · exact Or.inl rfl)
        exact ⟨Derivation.contraction (Derivation.or dand) (by
          intro x hx
          simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          exact hx.symm)⟩
      | all ψ₁ =>
        change fSize ψ₁ + 1 ≤ k + 1 at h
        have hψ : fSize ψ₁.free ≤ k := by
          have hsz : fSize ψ₁.free = fSize ψ₁ := fSize_rewAux _ ψ₁
          omega
        obtain ⟨d0⟩ := ih ψ₁.free hψ
        have hneg_eq : (Rew.shift.q ▹ ∼ψ₁)/[&0] = ∼ψ₁.free := by
          have h1 : (Rew.shift.q ▹ ∼ψ₁) = ∼(Rew.shift.q ▹ ψ₁) :=
            (Rewriting.app Rew.shift.q).map_neg' ψ₁
          rw [h1]
          have h2 : (Rew.subst (![&0] : Fin 1 → Semiterm L ℕ 0) ▹ ∼(Rew.shift.q ▹ ψ₁)) =
              ∼(Rew.subst (![&0] : Fin 1 → Semiterm L ℕ 0) ▹ (Rew.shift.q ▹ ψ₁)) :=
            (Rewriting.app (Rew.subst (![&0] : Fin 1 → Semiterm L ℕ 0))).map_neg' _
          change (Rew.subst (![&0] : Fin 1 → Semiterm L ℕ 0) ▹ ∼(Rew.shift.q ▹ ψ₁)) = _
          rw [h2, subst_zero_shift_q_eq_free]
        have d1 : Derivation (⦃ψ₁.free⦄ + ⦃(Rew.shift.q ▹ ∼ψ₁)/[&0]⦄) := by
          rw [hneg_eq]; exact d0
        have dexs : Derivation (⦃ψ₁.free⦄ + ⦃∃¹ (Rew.shift.q ▹ ∼ψ₁)⦄) := Derivation.exs d1
        have hsh : (⦃∃¹ (∼ψ₁)⦄ : Sequent L)⁺ = ⦃∃¹ (Rew.shift.q ▹ ∼ψ₁)⦄ := by
          change Multiset.map Rewriting.shift {∃¹ (∼ψ₁)} = {∃¹ (Rew.shift.q ▹ ∼ψ₁)}
          simp [Rewriting.app_exs]
        have d2 : Derivation ((⦃∃¹ (∼ψ₁)⦄ : Sequent L)⁺ + ⦃ψ₁.free⦄) := by
          rw [hsh]
          exact Derivation.contraction dexs (by
            intro x hx
            simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
            exact hx.symm)
        have dall : Derivation (⦃∃¹ (∼ψ₁)⦄ + ⦃∀¹ ψ₁⦄) := Derivation.all d2
        exact ⟨Derivation.contraction dall (by
          intro x hx
          simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
          exact hx.symm)⟩
      | exs ψ₁ =>
        change fSize ψ₁ + 1 ≤ k + 1 at h
        have hψ : fSize (∼ψ₁).free ≤ k := by
          have hsz : fSize (∼ψ₁).free = fSize (∼ψ₁) := fSize_rewAux _ (∼ψ₁)
          have hnsz : fSize (∼ψ₁) = fSize ψ₁ := fSize_neg ψ₁
          omega
        obtain ⟨d0⟩ := ih (∼ψ₁).free hψ
        have hpos_eq : (Rew.shift.q ▹ ψ₁)/[&0] = ∼(∼ψ₁).free := by
          have hfree_neg : (∼ψ₁).free = ∼(ψ₁.free) := (Rewriting.app Rew.free).map_neg' ψ₁
          rw [hfree_neg, neg_neg_sf]
          exact subst_zero_shift_q_eq_free ψ₁
        have d1 : Derivation (⦃(∼ψ₁).free⦄ + ⦃(Rew.shift.q ▹ ψ₁)/[&0]⦄) := by
          rw [hpos_eq]; exact d0
        have dexs : Derivation (⦃(∼ψ₁).free⦄ + ⦃∃¹ (Rew.shift.q ▹ ψ₁)⦄) := Derivation.exs d1
        have hsh : (⦃∃¹ ψ₁⦄ : Sequent L)⁺ = ⦃∃¹ (Rew.shift.q ▹ ψ₁)⦄ := by
          change Multiset.map Rewriting.shift {∃¹ ψ₁} = {∃¹ (Rew.shift.q ▹ ψ₁)}
          simp [Rewriting.app_exs]
        have d2 : Derivation ((⦃∃¹ ψ₁⦄ : Sequent L)⁺ + ⦃(∼ψ₁).free⦄) := by
          rw [hsh]
          exact Derivation.contraction dexs (by
            intro x hx
            simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
            exact hx.symm)
        exact ⟨Derivation.all d2⟩
  exact aux (fSize φ) φ le_rfl

private lemma deriv_or_inv {L : FFL.FirstOrder.Language} {Γ : Sequent L} {φ ψ : Proposition L}
    (d : Derivation (Γ + ⦃φ ⋎ ψ⦄)) : Nonempty (Derivation (Γ + ⦃φ, ψ⦄)) := by
  obtain ⟨emφ⟩ := neg_em φ
  obtain ⟨emψ⟩ := neg_em ψ
  have dφ : Derivation (⦃φ, ψ⦄ + ⦃∼φ⦄) :=
    Derivation.contraction emφ (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr rfl)
  have dψ : Derivation (⦃φ, ψ⦄ + ⦃∼ψ⦄) :=
    Derivation.contraction emψ (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr rfl)
  exact ⟨Derivation.cut d (Derivation.and dφ dψ)⟩

private lemma deriv_and_left {L : FFL.FirstOrder.Language} {Γ : Sequent L} {φ ψ : Proposition L}
    (d : Derivation (Γ + ⦃φ ⋏ ψ⦄)) : Nonempty (Derivation (Γ + ⦃φ⦄)) := by
  obtain ⟨emφ⟩ := neg_em φ
  have d1 : Derivation (⦃φ⦄ + ⦃∼φ, ∼ψ⦄) :=
    Derivation.contraction emφ (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl))
  exact ⟨Derivation.cut d (Derivation.or d1)⟩

private lemma deriv_and_right {L : FFL.FirstOrder.Language} {Γ : Sequent L} {φ ψ : Proposition L}
    (d : Derivation (Γ + ⦃φ ⋏ ψ⦄)) : Nonempty (Derivation (Γ + ⦃ψ⦄)) := by
  obtain ⟨emψ⟩ := neg_em ψ
  have d1 : Derivation (⦃ψ⦄ + ⦃∼φ, ∼ψ⦄) :=
    Derivation.contraction emψ (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl))
  exact ⟨Derivation.cut d (Derivation.or d1)⟩

/- ## Step 3: Hilbert-Style Derived Rules for `Entailment.Provable T` -/

private lemma emb_neg (φ : Sentence ℒₛₑₜ) :
    (Rewriting.emb (∼φ) : Proposition ℒₛₑₜ) = ∼(Rewriting.emb φ : Proposition ℒₛₑₜ) :=
  (Rewriting.emb : Sentence ℒₛₑₜ →ˡᶜ Proposition ℒₛₑₜ).map_neg' φ

private lemma emb_and (φ ψ : Sentence ℒₛₑₜ) :
    (Rewriting.emb (φ ⋏ ψ) : Proposition ℒₛₑₜ) =
      (Rewriting.emb φ : Proposition ℒₛₑₜ) ⋏ (Rewriting.emb ψ : Proposition ℒₛₑₜ) :=
  (Rewriting.emb : Sentence ℒₛₑₜ →ˡᶜ Proposition ℒₛₑₜ).map_and' φ ψ

private lemma emb_imp (φ ψ : Sentence ℒₛₑₜ) :
    (Rewriting.emb (φ 🡒 ψ) : Proposition ℒₛₑₜ) =
      ∼(Rewriting.emb φ : Proposition ℒₛₑₜ) ⋎ (Rewriting.emb ψ : Proposition ℒₛₑₜ) :=
  (Rewriting.emb : Sentence ℒₛₑₜ →ˡᶜ Proposition ℒₛₑₜ).map_imply' φ ψ

private lemma emb_bot :
    (Rewriting.emb (⊥ : Sentence ℒₛₑₜ) : Proposition ℒₛₑₜ) = ⊥ :=
  (Rewriting.emb : Sentence ℒₛₑₜ →ˡᶜ Proposition ℒₛₑₜ).map_bot'

private lemma pullback_of_deriv {T : Theory ℒₛₑₜ} {σ : Sentence ℒₛₑₜ} {A : Multiset (Sentence ℒₛₑₜ)}
    (hA : ∀ ψ ∈ A, ψ ∈ T)
    (d : Derivation ((∼A).map (Rewriting.emb : Sentence ℒₛₑₜ →ˡᶜ Proposition ℒₛₑₜ) + ⦃Rewriting.emb σ⦄)) :
    Entailment.Provable T σ := by
  refine ⟨⟨A, hA, ?_⟩⟩
  change Derivation ((⦃σ⦄ + ∼A).map Rewriting.emb)
  have heq : (⦃σ⦄ + ∼A).map (Rewriting.emb : Sentence ℒₛₑₜ →ˡᶜ Proposition ℒₛₑₜ) =
      ⦃Rewriting.emb σ⦄ + (∼A).map Rewriting.emb := by
    simp [Multiset.atom]
  rw [heq]
  exact Derivation.contraction d (by
    intro x hx
    simp only [Multiset.mem_add] at hx ⊢
    exact hx.symm)

private lemma deriv_of_raw {σ : Sentence ℒₛₑₜ} {A : Multiset (Sentence ℒₛₑₜ)}
    (d : OneSidedLK.Pullback Derivation Rewriting.emb (⦃σ⦄ + ∼A)) :
    Nonempty (Derivation ((∼A).map (Rewriting.emb : Sentence ℒₛₑₜ →ˡᶜ Proposition ℒₛₑₜ) +
      ⦃Rewriting.emb σ⦄)) := by
  have d' : Derivation ((⦃σ⦄ + ∼A).map Rewriting.emb) := d
  have heq : (⦃σ⦄ + ∼A).map (Rewriting.emb : Sentence ℒₛₑₜ →ˡᶜ Proposition ℒₛₑₜ) =
      ⦃Rewriting.emb σ⦄ + (∼A).map Rewriting.emb := by
    simp [Multiset.atom]
  rw [heq] at d'
  exact ⟨Derivation.contraction d' (by
    intro x hx
    simp only [Multiset.mem_add] at hx ⊢
    exact hx.symm)⟩

private lemma neg_ax_add (A B : Multiset (Sentence ℒₛₑₜ)) :
    (∼(A + B)).map (Rewriting.emb : Sentence ℒₛₑₜ →ˡᶜ Proposition ℒₛₑₜ) =
      (∼A).map Rewriting.emb + (∼B).map Rewriting.emb := by
  change ((A + B).map (∼·)).map Rewriting.emb =
    (A.map (∼·)).map Rewriting.emb + (B.map (∼·)).map Rewriting.emb
  rw [Multiset.map_add, Multiset.map_add]

private lemma provable_zf_to_zfc {σ : SetTheorySentence}
    (h : Entailment.Provable 𝗭𝗙 σ) : Entailment.Provable 𝗭𝗙𝗖 σ := by
  rcases h with ⟨⟨A, hA, d⟩⟩
  exact ⟨⟨A, fun ψ hψ => Or.inl (hA ψ hψ), d⟩⟩

private lemma provable_cut_bot {T : Theory ℒₛₑₜ} {φ : Sentence ℒₛₑₜ}
    (h₁ : Entailment.Provable T φ) (h₂ : Entailment.Provable T (∼φ)) :
    Entailment.Provable T ⊥ := by
  rcases h₁ with ⟨⟨A₁, hA₁, d₁_raw⟩⟩
  rcases h₂ with ⟨⟨A₂, hA₂, d₂_raw⟩⟩
  obtain ⟨d₁⟩ := deriv_of_raw d₁_raw
  obtain ⟨d₂⟩ := deriv_of_raw d₂_raw
  rw [emb_neg] at d₂
  have dcut : Derivation ((∼A₁).map Rewriting.emb + (∼A₂).map Rewriting.emb) :=
    Derivation.cut d₁ d₂
  refine pullback_of_deriv (A := A₁ + A₂) ?_ ?_
  · intro ψ hψ
    rcases Multiset.mem_add.mp hψ with h | h
    · exact hA₁ ψ h
    · exact hA₂ ψ h
  · rw [neg_ax_add]
    exact Derivation.contraction dcut (by
      intro x hx
      exact Multiset.mem_add.mpr (Or.inl hx))

private lemma provable_mp {T : Theory ℒₛₑₜ} {φ ψ : Sentence ℒₛₑₜ}
    (himp : Entailment.Provable T (φ 🡒 ψ)) (hφ : Entailment.Provable T φ) :
    Entailment.Provable T ψ := by
  rcases himp with ⟨⟨A₁, hA₁, d₁_raw⟩⟩
  rcases hφ with ⟨⟨A₂, hA₂, d₂_raw⟩⟩
  obtain ⟨d₁0⟩ := deriv_of_raw d₁_raw
  have d₁ : Derivation ((∼A₁).map Rewriting.emb + ⦃∼(Rewriting.emb φ) ⋎ Rewriting.emb ψ⦄) := by
    rwa [emb_imp] at d₁0
  obtain ⟨d₁_inv⟩ := deriv_or_inv d₁
  have d₁' : Derivation (((∼A₁).map Rewriting.emb + ⦃Rewriting.emb ψ⦄) + ⦃∼(Rewriting.emb φ)⦄) :=
    Derivation.contraction d₁_inv (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with h | (rfl | rfl)
      · exact Or.inl (Or.inl h)
      · exact Or.inr rfl
      · exact Or.inl (Or.inr rfl))
  obtain ⟨d₂⟩ := deriv_of_raw d₂_raw
  have dcut := Derivation.cut d₂ d₁'
  refine pullback_of_deriv (A := A₁ + A₂) ?_ ?_
  · intro χ hχ
    rcases Multiset.mem_add.mp hχ with h | h
    · exact hA₁ χ h
    · exact hA₂ χ h
  · rw [neg_ax_add]
    exact Derivation.contraction dcut (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with h2 | (h1 | rfl)
      · exact Or.inl (Or.inr h2)
      · exact Or.inl (Or.inl h1)
      · exact Or.inr rfl)

private lemma provable_iff_mp {T : Theory ℒₛₑₜ} {φ ψ : Sentence ℒₛₑₜ}
    (h : Entailment.Provable T (φ 🡘 ψ)) : Entailment.Provable T (φ 🡒 ψ) := by
  rcases h with ⟨⟨A, hA, d_raw⟩⟩
  obtain ⟨d⟩ := deriv_of_raw d_raw
  rw [LogicalConnective.iff, emb_and] at d
  obtain ⟨dl⟩ := deriv_and_left d
  exact pullback_of_deriv hA dl

private lemma provable_iff_mpr {T : Theory ℒₛₑₜ} {φ ψ : Sentence ℒₛₑₜ}
    (h : Entailment.Provable T (φ 🡘 ψ)) : Entailment.Provable T (ψ 🡒 φ) := by
  rcases h with ⟨⟨A, hA, d_raw⟩⟩
  obtain ⟨d⟩ := deriv_of_raw d_raw
  rw [LogicalConnective.iff, emb_and] at d
  obtain ⟨dr⟩ := deriv_and_right d
  exact pullback_of_deriv hA dr

private lemma provable_imp_trans {T : Theory ℒₛₑₜ} {φ ψ χ : Sentence ℒₛₑₜ}
    (h₁ : Entailment.Provable T (φ 🡒 ψ)) (h₂ : Entailment.Provable T (ψ 🡒 χ)) :
    Entailment.Provable T (φ 🡒 χ) := by
  rcases h₁ with ⟨⟨A₁, hA₁, d₁_raw⟩⟩
  rcases h₂ with ⟨⟨A₂, hA₂, d₂_raw⟩⟩
  obtain ⟨d₁0⟩ := deriv_of_raw d₁_raw
  have d₁ : Derivation ((∼A₁).map Rewriting.emb + ⦃∼(Rewriting.emb φ) ⋎ Rewriting.emb ψ⦄) := by
    rwa [emb_imp] at d₁0
  obtain ⟨d₂0⟩ := deriv_of_raw d₂_raw
  have d₂ : Derivation ((∼A₂).map Rewriting.emb + ⦃∼(Rewriting.emb ψ) ⋎ Rewriting.emb χ⦄) := by
    rwa [emb_imp] at d₂0
  obtain ⟨d₁_inv⟩ := deriv_or_inv d₁
  obtain ⟨d₂_inv⟩ := deriv_or_inv d₂
  have d₁' : Derivation (((∼A₁).map Rewriting.emb + ⦃∼(Rewriting.emb φ)⦄) + ⦃Rewriting.emb ψ⦄) :=
    Derivation.contraction d₁_inv (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with h | (rfl | rfl)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr rfl)
  have d₂' : Derivation (((∼A₂).map Rewriting.emb + ⦃Rewriting.emb χ⦄) + ⦃∼(Rewriting.emb ψ)⦄) :=
    Derivation.contraction d₂_inv (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with h | (rfl | rfl)
      · exact Or.inl (Or.inl h)
      · exact Or.inr rfl
      · exact Or.inl (Or.inr rfl))
  have dcut := Derivation.cut d₁' d₂'
  have dor : Derivation (((∼A₁).map Rewriting.emb + (∼A₂).map Rewriting.emb) +
      ⦃∼(Rewriting.emb φ) ⋎ Rewriting.emb χ⦄) :=
    Derivation.or (Derivation.contraction dcut (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with (h1 | rfl) | (h2 | rfl)
      · exact Or.inl (Or.inl h1)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (Or.inr h2)
      · exact Or.inr (Or.inr rfl)))
  refine pullback_of_deriv (A := A₁ + A₂) ?_ ?_
  · intro a ha
    rcases Multiset.mem_add.mp ha with h | h
    · exact hA₁ a h
    · exact hA₂ a h
  · rw [neg_ax_add, emb_imp]
    exact dor

private lemma provable_imp_neg_to_imp_bot {T : Theory ℒₛₑₜ} {φ ψ : Sentence ℒₛₑₜ}
    (h : Entailment.Provable T (φ 🡒 ∼ψ)) : Entailment.Provable T (φ 🡒 (ψ 🡒 ⊥)) := by
  rcases h with ⟨⟨A, hA, d_raw⟩⟩
  obtain ⟨d0⟩ := deriv_of_raw d_raw
  have d : Derivation ((∼A).map Rewriting.emb + ⦃∼(Rewriting.emb φ) ⋎ ∼(Rewriting.emb ψ)⦄) := by
    rwa [emb_imp, emb_neg] at d0
  obtain ⟨d_inv⟩ := deriv_or_inv d
  have d1 : Derivation (((∼A).map Rewriting.emb + ⦃∼(Rewriting.emb φ)⦄) +
      ⦃∼(Rewriting.emb ψ), ⊥⦄) :=
    Derivation.contraction d_inv (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with ha | (rfl | rfl)
      · exact Or.inl (Or.inl ha)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr (Or.inl rfl))
  have d2 : Derivation ((∼A).map Rewriting.emb +
      ⦃∼(Rewriting.emb φ), ∼(Rewriting.emb ψ) ⋎ ⊥⦄) :=
    Derivation.contraction (Derivation.or d1) (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with (ha | rfl) | rfl
      · exact Or.inl ha
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl))
  refine pullback_of_deriv hA ?_
  rw [emb_imp, emb_imp, emb_bot]
  exact Derivation.or d2

private lemma provable_s_comb {T : Theory ℒₛₑₜ} {φ ψ χ : Sentence ℒₛₑₜ}
    (h₁ : Entailment.Provable T (φ 🡒 (ψ 🡒 χ))) (h₂ : Entailment.Provable T (φ 🡒 ψ)) :
    Entailment.Provable T (φ 🡒 χ) := by
  rcases h₁ with ⟨⟨A₁, hA₁, d₁_raw⟩⟩
  rcases h₂ with ⟨⟨A₂, hA₂, d₂_raw⟩⟩
  obtain ⟨d₁0⟩ := deriv_of_raw d₁_raw
  have d₁ : Derivation ((∼A₁).map Rewriting.emb +
      ⦃∼(Rewriting.emb φ) ⋎ (∼(Rewriting.emb ψ) ⋎ Rewriting.emb χ)⦄) := by
    rwa [emb_imp, emb_imp] at d₁0
  obtain ⟨d₁_inv⟩ := deriv_or_inv d₁
  have d₁a : Derivation (((∼A₁).map Rewriting.emb + ⦃∼(Rewriting.emb φ)⦄) +
      ⦃∼(Rewriting.emb ψ) ⋎ Rewriting.emb χ⦄) :=
    Derivation.contraction d₁_inv (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with h | (rfl | rfl)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr rfl)
  obtain ⟨d₁a_inv⟩ := deriv_or_inv d₁a
  have d₁b : Derivation (((∼A₁).map Rewriting.emb + ⦃∼(Rewriting.emb φ), Rewriting.emb χ⦄) +
      ⦃∼(Rewriting.emb ψ)⦄) :=
    Derivation.contraction d₁a_inv (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with (h | rfl) | (rfl | rfl)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl rfl))
      · exact Or.inr rfl
      · exact Or.inl (Or.inr (Or.inr rfl)))
  obtain ⟨d₂0⟩ := deriv_of_raw d₂_raw
  have d₂ : Derivation ((∼A₂).map Rewriting.emb + ⦃∼(Rewriting.emb φ) ⋎ Rewriting.emb ψ⦄) := by
    rwa [emb_imp] at d₂0
  obtain ⟨d₂_inv⟩ := deriv_or_inv d₂
  have d₂' : Derivation (((∼A₂).map Rewriting.emb + ⦃∼(Rewriting.emb φ)⦄) + ⦃Rewriting.emb ψ⦄) :=
    Derivation.contraction d₂_inv (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with h | (rfl | rfl)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr rfl)
  have dcut := Derivation.cut d₂' d₁b
  have dor : Derivation (((∼A₁).map Rewriting.emb + (∼A₂).map Rewriting.emb) +
      ⦃∼(Rewriting.emb φ) ⋎ Rewriting.emb χ⦄) :=
    Derivation.or (Derivation.contraction dcut (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with (h2 | rfl) | (h1 | (rfl | rfl))
      · exact Or.inl (Or.inr h2)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (Or.inl h1)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)))
  refine pullback_of_deriv (A := A₁ + A₂) ?_ ?_
  · intro a ha
    rcases Multiset.mem_add.mp ha with h | h
    · exact hA₁ a h
    · exact hA₂ a h
  · rw [neg_ax_add, emb_imp]
    exact dor

private lemma provable_contrapose {T : Theory ℒₛₑₜ} {φ ψ : Sentence ℒₛₑₜ}
    (h : Entailment.Provable T (φ 🡒 ψ)) : Entailment.Provable T (∼ψ 🡒 ∼φ) := by
  rcases h with ⟨⟨A, hA, d_raw⟩⟩
  obtain ⟨d0⟩ := deriv_of_raw d_raw
  have d : Derivation ((∼A).map Rewriting.emb + ⦃∼(Rewriting.emb φ) ⋎ Rewriting.emb ψ⦄) := by
    rwa [emb_imp] at d0
  obtain ⟨d_inv⟩ := deriv_or_inv d
  have d1 : Derivation ((∼A).map Rewriting.emb + ⦃∼(∼(Rewriting.emb ψ)), ∼(Rewriting.emb φ)⦄) :=
    Derivation.contraction d_inv (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with ha | (rfl | rfl)
      · exact Or.inl ha
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl (neg_neg_sf _).symm))
  refine pullback_of_deriv hA ?_
  rw [emb_imp, emb_neg, emb_neg]
  exact Derivation.or d1

/- ## Step 4: Gödel's Second Incompleteness Theorem from HBL + Diagonal Sentence -/

private lemma godel_second_incompleteness {T : Theory ℒₛₑₜ}
    (P : SetTheorySentence → SetTheorySentence)
    (hCon : T ⊬ ⊥)
    (hD1 : ∀ φ, Entailment.Provable T φ → Entailment.Provable T (P φ))
    (hD2 : ∀ φ ψ, Entailment.Provable T (P (φ 🡒 ψ) 🡒 (P φ 🡒 P ψ)))
    (hD3 : ∀ φ, Entailment.Provable T (P φ 🡒 P (P φ)))
    {G : SetTheorySentence} (hDiag : Entailment.Provable T (G 🡘 ∼P G)) :
    T ⊬ ∼P ⊥ := by
  intro hNotPBot
  have hG_to_nPG : Entailment.Provable T (G 🡒 ∼P G) := provable_iff_mp hDiag
  have hnPG_to_G : Entailment.Provable T (∼P G 🡒 G) := provable_iff_mpr hDiag
  have h1 : Entailment.Provable T (G 🡒 (P G 🡒 ⊥)) := provable_imp_neg_to_imp_bot hG_to_nPG
  have h2 : Entailment.Provable T (P (G 🡒 (P G 🡒 ⊥))) := hD1 _ h1
  have h3 : Entailment.Provable T (P G 🡒 P (P G 🡒 ⊥)) := provable_mp (hD2 _ _) h2
  have h4 : Entailment.Provable T (P G 🡒 (P (P G) 🡒 P ⊥)) :=
    provable_imp_trans h3 (hD2 _ _)
  have h5 : Entailment.Provable T (P G 🡒 P ⊥) := provable_s_comb h4 (hD3 G)
  have h6 : Entailment.Provable T (∼P ⊥ 🡒 ∼P G) := provable_contrapose h5
  have h7 : Entailment.Provable T (∼P ⊥ 🡒 G) := provable_imp_trans h6 hnPG_to_G
  have hG : Entailment.Provable T G := provable_mp h7 hNotPBot
  have hPG : Entailment.Provable T (P G) := hD1 G hG
  have hnPG : Entailment.Provable T (∼P G) := provable_mp hG_to_nPG hG
  exact hCon (provable_cut_bot hPG hnPG)

end Helpers

theorem main : H1 → H2 → OMA.R_Constant14_c14_upper_bound_R1.H2 := by
  intro h1 h2 hConZFC
  have hConZF : 𝗭𝗙 ⊬ ⊥ := fun h => hConZFC (provable_zf_to_zfc h)
  rcases h2 with ⟨M, P, hM_incons, hD1, hD2, hD3, ⟨G, hDiag⟩, hRefl⟩
  have hNotHalts : ¬ M.IsHalting := fun hH => hConZF (hM_incons hH)
  have hZF_not_PBot : 𝗭𝗙 ⊬ ∼P ⊥ :=
    godel_second_incompleteness P hConZF hD1 hD2 hD3 hDiag
  have hZF_not_nhalts : 𝗭𝗙 ⊬ ∼Constant14.halts M := fun hPrf =>
    hZF_not_PBot (provable_mp hRefl hPrf)
  have hZFC_not_nhalts : 𝗭𝗙𝗖 ⊬ ∼Constant14.halts M := fun hPrf =>
    hZF_not_nhalts (h1 230 M hPrf)
  exact ⟨M, hNotHalts, hZFC_not_nhalts⟩

end OMA.R_Constant14_c14_upper_bound_R1_H2_R1
