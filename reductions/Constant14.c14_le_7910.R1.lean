import FormalConjectures.OptimizationConstants.«14»

/-!
# Reduction of `Constant14.c14_le_7910` ($C_{14} \le 7910$, Yedidia–Aaronson 2016)

Following A. Yedidia and S. Aaronson (*A relatively small Turing machine whose behavior is
independent of set theory*, arXiv:1605.04343, 2016) and K. Gödel (1931), we reduce
`Constant14.c14_le_7910` ($C_{14} \le 7910$, i.e., there exists a 7910-state two-symbol Turing
machine whose halting is independent of `𝗭𝗙𝗖`) to two independent pillars in proof theory and
computability:
1. `H1`: **Consistency and $\Sigma_1$-soundness of `𝗭𝗙𝗖`**: `𝗭𝗙𝗖` does not prove `⊥`, and
   whenever `𝗭𝗙𝗖` proves `halts M`, `M` actually halts (`M.IsHalting`).
2. `H2`: **Yedidia–Aaronson's 7910-state `𝗭𝗙𝗖`-independence machine and Hilbert–Bernays–Löb
   provability** ([YS2016]): there exist a 7910-state binary Turing machine `M` (searching for a
   counterexample to Harvey Friedman's graph-theoretic statement equiconsistent with `SRP`, and
   hence implying `Incon(ZFC)`) and a formal provability predicate `P` for `𝗭𝗙𝗖` satisfying the
   Hilbert–Bernays–Löb derivability conditions (D1)–(D3) with a Gödel fixed point `G 🡘 ∼P G`,
   such that `M.IsHalting → 𝗭𝗙𝗖 ⊢ ⊥` and `𝗭𝗙𝗖 ⊢ ∼halts M 🡒 ∼P ⊥`.

Inside `main`, we build the one-sided Tait/Gentzen sequent calculus (`FFL.FirstOrder.Derivation`)
from scratch (generalized law of excluded middle `⦃φ, ∼φ⦄` by formula-size induction, double
negation, `⋎`-inversion, modus ponens, conjunction projections, implication transitivity,
S-combinator contraction, contraposition, and cut-to-`⊥`), prove **Gödel's Second Incompleteness
Theorem** (`𝗭𝗙𝗖 ⊬ ⊥ → 𝗭𝗙𝗖 ⊬ ∼P ⊥`) from (D1)–(D3) and `G`, deduce `𝗭𝗙𝗖`-independence of
`halts M`, and conclude `C14 ≤ 7910` via `Nat.sInf_le`.

Credit: @tkaiman
-/

namespace OMA.R_Constant14_c14_le_7910_R1

open FFL FFL.FirstOrder Turing BusyBeaver FFL.FirstOrder.SetTheory Constant14

/- ### Step 1: Formula size and rewriting lemmas for `FFL.FirstOrder.Semiformula` -/

private def fSize {L : FFL.FirstOrder.Language} : {n : ℕ} → Semiproposition L n → ℕ
  | _, .verum => 0
  | _, .falsum => 0
  | _, .rel _ _ => 0
  | _, .nrel _ _ => 0
  | _, .and φ ψ => fSize φ + fSize ψ + 1
  | _, .or φ ψ => fSize φ + fSize ψ + 1
  | _, .all φ => fSize φ + 1
  | _, .exs φ => fSize φ + 1

private lemma fSize_rewAux {L : FFL.FirstOrder.Language} {n₁ n₂ : ℕ} (ω : SyntacticRew L n₁ n₂)
    (φ : Semiproposition L n₁) :
    fSize (Semiformula.rewAux ω φ) = fSize φ := by
  induction φ generalizing n₂ with
  | verum => rfl
  | falsum => rfl
  | rel _ _ => rfl
  | nrel _ _ => rfl
  | and φ₁ φ₂ ih₁ ih₂ =>
    change fSize (Semiformula.and (Semiformula.rewAux ω φ₁) (Semiformula.rewAux ω φ₂)) =
      fSize φ₁ + fSize φ₂ + 1
    simp only [fSize, ih₁, ih₂]
  | or φ₁ φ₂ ih₁ ih₂ =>
    change fSize (Semiformula.or (Semiformula.rewAux ω φ₁) (Semiformula.rewAux ω φ₂)) =
      fSize φ₁ + fSize φ₂ + 1
    simp only [fSize, ih₁, ih₂]
  | all φ₁ ih =>
    change fSize (Semiformula.all (Semiformula.rewAux ω.q φ₁)) = fSize φ₁ + 1
    simp only [fSize, ih]
  | exs φ₁ ih =>
    change fSize (Semiformula.exs (Semiformula.rewAux ω.q φ₁)) = fSize φ₁ + 1
    simp only [fSize, ih]

private lemma fSize_neg {L : FFL.FirstOrder.Language} :
    ∀ {n : ℕ} (φ : Semiproposition L n), fSize (∼φ) = fSize φ
  | _, .verum => rfl
  | _, .falsum => rfl
  | _, .rel _ _ => rfl
  | _, .nrel _ _ => rfl
  | _, .and φ₁ φ₂ => by
    change fSize (Semiformula.or (∼φ₁) (∼φ₂)) = fSize φ₁ + fSize φ₂ + 1
    simp only [fSize, fSize_neg φ₁, fSize_neg φ₂]
  | _, .or φ₁ φ₂ => by
    change fSize (Semiformula.and (∼φ₁) (∼φ₂)) = fSize φ₁ + fSize φ₂ + 1
    simp only [fSize, fSize_neg φ₁, fSize_neg φ₂]
  | _, .all φ₁ => by
    change fSize (Semiformula.exs (∼φ₁)) = fSize φ₁ + 1
    simp only [fSize, fSize_neg φ₁]
  | _, .exs φ₁ => by
    change fSize (Semiformula.all (∼φ₁)) = fSize φ₁ + 1
    simp only [fSize, fSize_neg φ₁]

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

/- ### Step 2: One-sided Tait/Gentzen sequent calculus (`Derivation`) derived rules -/

private def neg_em_aux {L : FFL.FirstOrder.Language} :
    ∀ (k : ℕ) (φ : Proposition L), fSize φ ≤ k → Derivation ⦃φ, ∼φ⦄
  | _, .verum, _ =>
    Derivation.contraction Derivation.verum (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      exact Or.inl hx)
  | _, .falsum, _ =>
    Derivation.contraction Derivation.verum (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      exact Or.inr hx)
  | _, .rel r v, _ => Derivation.identity r v
  | _, .nrel r v, _ =>
    Derivation.contraction (Derivation.identity r v) (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      exact hx.symm)
  | 0, .and _ _, h => by simp [fSize] at h
  | k + 1, .and φ ψ, h => by
    have hφ : fSize φ ≤ k := by simp [fSize] at h; omega
    have hψ : fSize ψ ≤ k := by simp [fSize] at h; omega
    have dφ : Derivation (⦃∼φ, ∼ψ⦄ + ⦃φ⦄) :=
      Derivation.contraction (neg_em_aux k φ hφ) (by
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (Or.inl rfl))
    have dψ : Derivation (⦃∼φ, ∼ψ⦄ + ⦃ψ⦄) :=
      Derivation.contraction (neg_em_aux k ψ hψ) (by
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (Or.inr rfl))
    have dand : Derivation (⦃φ ⋏ ψ⦄ + ⦃∼φ, ∼ψ⦄) :=
      Derivation.contraction (Derivation.and dφ dψ) (by
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        rcases hx with (rfl | rfl) | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl)
    exact Derivation.or dand
  | 0, .or _ _, h => by simp [fSize] at h
  | k + 1, .or φ ψ, h => by
    have hφ : fSize φ ≤ k := by simp [fSize] at h; omega
    have hψ : fSize ψ ≤ k := by simp [fSize] at h; omega
    have dφ : Derivation (⦃φ, ψ⦄ + ⦃∼φ⦄) :=
      Derivation.contraction (neg_em_aux k φ hφ) (by
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr rfl)
    have dψ : Derivation (⦃φ, ψ⦄ + ⦃∼ψ⦄) :=
      Derivation.contraction (neg_em_aux k ψ hψ) (by
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr rfl)
    have dand : Derivation (⦃∼φ ⋏ ∼ψ⦄ + ⦃φ, ψ⦄) :=
      Derivation.contraction (Derivation.and dφ dψ) (by
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        rcases hx with (rfl | rfl) | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl)
    exact Derivation.contraction (Derivation.or dand) (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      exact hx.symm)
  | 0, .all _, h => by simp [fSize] at h
  | k + 1, .all φ, h => by
    have hφ : fSize φ.free ≤ k := by
      have hsz : fSize φ.free = fSize φ := fSize_rewAux _ φ
      simp [fSize] at h
      omega
    have d0 : Derivation ⦃φ.free, ∼φ.free⦄ := neg_em_aux k φ.free hφ
    have hneg_eq : (Rew.shift.q ▹ ∼φ)/[&0] = ∼φ.free := by
      have h1 : (Rew.shift.q ▹ ∼φ) = ∼(Rew.shift.q ▹ φ) := (Rewriting.app Rew.shift.q).map_neg' φ
      rw [h1]
      have h2 : (Rew.subst (![&0] : Fin 1 → Semiterm L ℕ 0) ▹ ∼(Rew.shift.q ▹ φ)) =
          ∼(Rew.subst (![&0] : Fin 1 → Semiterm L ℕ 0) ▹ (Rew.shift.q ▹ φ)) :=
        (Rewriting.app (Rew.subst (![&0] : Fin 1 → Semiterm L ℕ 0))).map_neg' _
      change (Rew.subst (![&0] : Fin 1 → Semiterm L ℕ 0) ▹ ∼(Rew.shift.q ▹ φ)) = _
      rw [h2, subst_zero_shift_q_eq_free]
    have d1 : Derivation (⦃φ.free⦄ + ⦃(Rew.shift.q ▹ ∼φ)/[&0]⦄) := by
      rw [hneg_eq]; exact d0
    have dexs : Derivation (⦃φ.free⦄ + ⦃∃¹ (Rew.shift.q ▹ ∼φ)⦄) := Derivation.exs d1
    have hsh : (⦃∃¹ (∼φ)⦄ : Sequent L)⁺ = ⦃∃¹ (Rew.shift.q ▹ ∼φ)⦄ := by
      change Multiset.map Rewriting.shift {∃¹ (∼φ)} = {∃¹ (Rew.shift.q ▹ ∼φ)}
      simp [Rewriting.app_exs]
    have d2 : Derivation ((⦃∃¹ (∼φ)⦄ : Sequent L)⁺ + ⦃φ.free⦄) := by
      rw [hsh]
      exact Derivation.contraction dexs (by
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        exact hx.symm)
    have dall : Derivation (⦃∃¹ (∼φ)⦄ + ⦃∀¹ φ⦄) := Derivation.all d2
    exact Derivation.contraction dall (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      exact hx.symm)
  | 0, .exs _, h => by simp [fSize] at h
  | k + 1, .exs φ, h => by
    have hφ : fSize (∼φ).free ≤ k := by
      have hsz : fSize (∼φ).free = fSize (∼φ) := fSize_rewAux _ (∼φ)
      have hnsz : fSize (∼φ) = fSize φ := fSize_neg φ
      simp [fSize] at h
      omega
    have d0 : Derivation ⦃(∼φ).free, ∼(∼φ).free⦄ := neg_em_aux k (∼φ).free hφ
    have hpos_eq : (Rew.shift.q ▹ φ)/[&0] = ∼(∼φ).free := by
      have hfree_neg : (∼φ).free = ∼(φ.free) := (Rewriting.app Rew.free).map_neg' φ
      rw [hfree_neg, neg_neg_sf]
      exact subst_zero_shift_q_eq_free φ
    have d1 : Derivation (⦃(∼φ).free⦄ + ⦃(Rew.shift.q ▹ φ)/[&0]⦄) := by
      rw [hpos_eq]; exact d0
    have dexs : Derivation (⦃(∼φ).free⦄ + ⦃∃¹ (Rew.shift.q ▹ φ)⦄) := Derivation.exs d1
    have hsh : (⦃∃¹ φ⦄ : Sequent L)⁺ = ⦃∃¹ (Rew.shift.q ▹ φ)⦄ := by
      change Multiset.map Rewriting.shift {∃¹ φ} = {∃¹ (Rew.shift.q ▹ φ)}
      simp [Rewriting.app_exs]
    have d2 : Derivation ((⦃∃¹ φ⦄ : Sequent L)⁺ + ⦃(∼φ).free⦄) := by
      rw [hsh]
      exact Derivation.contraction dexs (by
        intro x hx
        simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
        exact hx.symm)
    exact Derivation.all d2

private def neg_em {L : FFL.FirstOrder.Language} (φ : Proposition L) : Derivation ⦃φ, ∼φ⦄ :=
  neg_em_aux (fSize φ) φ le_rfl

private def deriv_or_inv {L : FFL.FirstOrder.Language} {Γ : Sequent L} {φ ψ : Proposition L}
    (d : Derivation (Γ + ⦃φ ⋎ ψ⦄)) : Derivation (Γ + ⦃φ, ψ⦄) := by
  have dφ : Derivation (⦃φ, ψ⦄ + ⦃∼φ⦄) :=
    Derivation.contraction (neg_em φ) (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr rfl)
  have dψ : Derivation (⦃φ, ψ⦄ + ⦃∼ψ⦄) :=
    Derivation.contraction (neg_em ψ) (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr rfl)
  exact Derivation.cut d (Derivation.and dφ dψ)

private def deriv_and_left {L : FFL.FirstOrder.Language} {Γ : Sequent L} {φ ψ : Proposition L}
    (d : Derivation (Γ + ⦃φ ⋏ ψ⦄)) : Derivation (Γ + ⦃φ⦄) := by
  have d1 : Derivation (⦃φ⦄ + ⦃∼φ, ∼ψ⦄) :=
    Derivation.contraction (neg_em φ) (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl))
  exact Derivation.cut d (Derivation.or d1)

private def deriv_and_right {L : FFL.FirstOrder.Language} {Γ : Sequent L} {φ ψ : Proposition L}
    (d : Derivation (Γ + ⦃φ ⋏ ψ⦄)) : Derivation (Γ + ⦃ψ⦄) := by
  have d1 : Derivation (⦃ψ⦄ + ⦃∼φ, ∼ψ⦄) :=
    Derivation.contraction (neg_em ψ) (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl))
  exact Derivation.cut d (Derivation.or d1)

/- ### Step 3: Hilbert-style derived rules for `Entailment.Provable T` -/

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

private def deriv_of_raw {σ : Sentence ℒₛₑₜ} {A : Multiset (Sentence ℒₛₑₜ)}
    (d : OneSidedLK.Pullback Derivation Rewriting.emb (⦃σ⦄ + ∼A)) :
    Derivation ((∼A).map (Rewriting.emb : Sentence ℒₛₑₜ →ˡᶜ Proposition ℒₛₑₜ) + ⦃Rewriting.emb σ⦄) := by
  have d' : Derivation ((⦃σ⦄ + ∼A).map Rewriting.emb) := d
  have heq : (⦃σ⦄ + ∼A).map (Rewriting.emb : Sentence ℒₛₑₜ →ˡᶜ Proposition ℒₛₑₜ) =
      ⦃Rewriting.emb σ⦄ + (∼A).map Rewriting.emb := by
    simp [Multiset.atom]
  rw [heq] at d'
  exact Derivation.contraction d' (by
    intro x hx
    simp only [Multiset.mem_add] at hx ⊢
    exact hx.symm)

private lemma neg_ax_add (A B : Multiset (Sentence ℒₛₑₜ)) :
    (∼(A + B)).map (Rewriting.emb : Sentence ℒₛₑₜ →ˡᶜ Proposition ℒₛₑₜ) =
      (∼A).map Rewriting.emb + (∼B).map Rewriting.emb := by
  change ((A + B).map (∼·)).map Rewriting.emb =
    (A.map (∼·)).map Rewriting.emb + (B.map (∼·)).map Rewriting.emb
  rw [Multiset.map_add, Multiset.map_add]

private lemma provable_cut_bot {T : Theory ℒₛₑₜ} {φ : Sentence ℒₛₑₜ}
    (h₁ : Entailment.Provable T φ) (h₂ : Entailment.Provable T (∼φ)) :
    Entailment.Provable T ⊥ := by
  rcases h₁ with ⟨⟨A₁, hA₁, d₁_raw⟩⟩
  rcases h₂ with ⟨⟨A₂, hA₂, d₂_raw⟩⟩
  have d₁ := deriv_of_raw d₁_raw
  have d₂ := deriv_of_raw d₂_raw
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
  have d₁ : Derivation ((∼A₁).map Rewriting.emb + ⦃∼(Rewriting.emb φ) ⋎ Rewriting.emb ψ⦄) := by
    have h := deriv_of_raw d₁_raw
    rwa [emb_imp] at h
  have d₁' : Derivation (((∼A₁).map Rewriting.emb + ⦃Rewriting.emb ψ⦄) + ⦃∼(Rewriting.emb φ)⦄) :=
    Derivation.contraction (deriv_or_inv d₁) (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with h | (rfl | rfl)
      · exact Or.inl (Or.inl h)
      · exact Or.inr rfl
      · exact Or.inl (Or.inr rfl))
  have d₂ := deriv_of_raw d₂_raw
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
  have d := deriv_of_raw d_raw
  rw [LogicalConnective.iff, emb_and] at d
  exact pullback_of_deriv hA (deriv_and_left d)

private lemma provable_iff_mpr {T : Theory ℒₛₑₜ} {φ ψ : Sentence ℒₛₑₜ}
    (h : Entailment.Provable T (φ 🡘 ψ)) : Entailment.Provable T (ψ 🡒 φ) := by
  rcases h with ⟨⟨A, hA, d_raw⟩⟩
  have d := deriv_of_raw d_raw
  rw [LogicalConnective.iff, emb_and] at d
  exact pullback_of_deriv hA (deriv_and_right d)

private lemma provable_imp_trans {T : Theory ℒₛₑₜ} {φ ψ χ : Sentence ℒₛₑₜ}
    (h₁ : Entailment.Provable T (φ 🡒 ψ)) (h₂ : Entailment.Provable T (ψ 🡒 χ)) :
    Entailment.Provable T (φ 🡒 χ) := by
  rcases h₁ with ⟨⟨A₁, hA₁, d₁_raw⟩⟩
  rcases h₂ with ⟨⟨A₂, hA₂, d₂_raw⟩⟩
  have d₁ : Derivation ((∼A₁).map Rewriting.emb + ⦃∼(Rewriting.emb φ) ⋎ Rewriting.emb ψ⦄) := by
    have h := deriv_of_raw d₁_raw
    rwa [emb_imp] at h
  have d₂ : Derivation ((∼A₂).map Rewriting.emb + ⦃∼(Rewriting.emb ψ) ⋎ Rewriting.emb χ⦄) := by
    have h := deriv_of_raw d₂_raw
    rwa [emb_imp] at h
  have d₁' : Derivation (((∼A₁).map Rewriting.emb + ⦃∼(Rewriting.emb φ)⦄) + ⦃Rewriting.emb ψ⦄) :=
    Derivation.contraction (deriv_or_inv d₁) (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with h | (rfl | rfl)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr rfl)
  have d₂' : Derivation (((∼A₂).map Rewriting.emb + ⦃Rewriting.emb χ⦄) + ⦃∼(Rewriting.emb ψ)⦄) :=
    Derivation.contraction (deriv_or_inv d₂) (by
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
  have d : Derivation ((∼A).map Rewriting.emb + ⦃∼(Rewriting.emb φ) ⋎ ∼(Rewriting.emb ψ)⦄) := by
    have h' := deriv_of_raw d_raw
    rwa [emb_imp, emb_neg] at h'
  have d1 : Derivation (((∼A).map Rewriting.emb + ⦃∼(Rewriting.emb φ)⦄) +
      ⦃∼(Rewriting.emb ψ), ⊥⦄) :=
    Derivation.contraction (deriv_or_inv d) (by
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
  have d₁ : Derivation ((∼A₁).map Rewriting.emb +
      ⦃∼(Rewriting.emb φ) ⋎ (∼(Rewriting.emb ψ) ⋎ Rewriting.emb χ)⦄) := by
    have h' := deriv_of_raw d₁_raw
    rwa [emb_imp, emb_imp] at h'
  have d₁a : Derivation (((∼A₁).map Rewriting.emb + ⦃∼(Rewriting.emb φ)⦄) +
      ⦃∼(Rewriting.emb ψ) ⋎ Rewriting.emb χ⦄) :=
    Derivation.contraction (deriv_or_inv d₁) (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with h | (rfl | rfl)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr rfl)
  have d₁b : Derivation (((∼A₁).map Rewriting.emb + ⦃∼(Rewriting.emb φ), Rewriting.emb χ⦄) +
      ⦃∼(Rewriting.emb ψ)⦄) :=
    Derivation.contraction (deriv_or_inv d₁a) (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with (h | rfl) | (rfl | rfl)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl rfl))
      · exact Or.inr rfl
      · exact Or.inl (Or.inr (Or.inr rfl)))
  have d₂ : Derivation ((∼A₂).map Rewriting.emb + ⦃∼(Rewriting.emb φ) ⋎ Rewriting.emb ψ⦄) := by
    have h' := deriv_of_raw d₂_raw
    rwa [emb_imp] at h'
  have d₂' : Derivation (((∼A₂).map Rewriting.emb + ⦃∼(Rewriting.emb φ)⦄) + ⦃Rewriting.emb ψ⦄) :=
    Derivation.contraction (deriv_or_inv d₂) (by
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
  have d : Derivation ((∼A).map Rewriting.emb + ⦃∼(Rewriting.emb φ) ⋎ Rewriting.emb ψ⦄) := by
    have h' := deriv_of_raw d_raw
    rwa [emb_imp] at h'
  have d1 : Derivation ((∼A).map Rewriting.emb + ⦃∼(∼(Rewriting.emb ψ)), ∼(Rewriting.emb φ)⦄) :=
    Derivation.contraction (deriv_or_inv d) (by
      intro x hx
      simp only [Multiset.atom, Multiset.mem_add, Multiset.mem_singleton] at hx ⊢
      rcases hx with ha | (rfl | rfl)
      · exact Or.inl ha
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl (neg_neg_sf _).symm))
  refine pullback_of_deriv hA ?_
  rw [emb_imp, emb_neg, emb_neg]
  exact Derivation.or d1

/- ### Step 4: Gödel's Second Incompleteness Theorem from HBL + Diagonal Sentence -/

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

/- ### Hypotheses and main reduction theorem -/

/-- **Consistency and $\Sigma_1$-soundness of `𝗭𝗙𝗖`**:
`𝗭𝗙𝗖` does not prove `⊥`, and every binary Turing machine `M` proved to halt in `𝗭𝗙𝗖` actually
halts (`M.IsHalting`). -/
def H1 : Prop :=
  (𝗭𝗙𝗖 ⊬ ⊥) ∧
    ∀ (n : ℕ) [NeZero n] (M : BusyBeaver.Machine (Fin 2) (Fin n)),
      Entailment.Provable 𝗭𝗙𝗖 (Constant14.halts M) → M.IsHalting

/-- **Yedidia–Aaronson's 7910-state `𝗭𝗙𝗖`-independence machine and HBL provability** ([YS2016]):
there exist a 7910-state binary Turing machine `M` and a provability predicate `P` for `𝗭𝗙𝗖`
satisfying the Hilbert–Bernays–Löb derivability conditions (D1)–(D3) with a Gödel fixed point
`G 🡘 ∼P G`, such that `M.IsHalting → 𝗭𝗙𝗖 ⊢ ⊥` and `𝗭𝗙𝗖 ⊢ ∼halts M 🡒 ∼P ⊥`. -/
def H2 : Prop :=
  ∃ (M : BusyBeaver.Machine (Fin 2) (Fin 7910))
    (P : SetTheorySentence → SetTheorySentence),
    (M.IsHalting → Entailment.Provable 𝗭𝗙𝗖 ⊥) ∧
    (∀ φ, Entailment.Provable 𝗭𝗙𝗖 φ → Entailment.Provable 𝗭𝗙𝗖 (P φ)) ∧
    (∀ φ ψ, Entailment.Provable 𝗭𝗙𝗖 (P (φ 🡒 ψ) 🡒 (P φ 🡒 P ψ))) ∧
    (∀ φ, Entailment.Provable 𝗭𝗙𝗖 (P φ 🡒 P (P φ))) ∧
    (∃ G, Entailment.Provable 𝗭𝗙𝗖 (G 🡘 ∼P G)) ∧
    Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M 🡒 ∼P ⊥)

theorem main : H1 → H2 → type_of% @Constant14.c14_le_7910 := by
  intro h1 h2
  rcases h1 with ⟨hCon, hSound⟩
  rcases h2 with ⟨M, P, hM_incons, hD1, hD2, hD3, ⟨G, hDiag⟩, hRefl⟩
  have hZFC_not_halts : 𝗭𝗙𝗖 ⊬ Constant14.halts M := by
    intro hPrf
    exact hCon (hM_incons (hSound 7910 M hPrf))
  have hZFC_not_PBot : 𝗭𝗙𝗖 ⊬ ∼P ⊥ :=
    godel_second_incompleteness P hCon hD1 hD2 hD3 hDiag
  have hZFC_not_nhalts : 𝗭𝗙𝗖 ⊬ ∼Constant14.halts M := by
    intro hPrf
    exact hZFC_not_PBot (provable_mp hRefl hPrf)
  exact Nat.sInf_le ⟨inferInstance, M, hZFC_not_halts, hZFC_not_nhalts⟩

end OMA.R_Constant14_c14_le_7910_R1
