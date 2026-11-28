import FormalConjectures.OptimizationConstants.«14»

/-!
Reduction of `Constant14.c14_upper_bound` (`Constant14.C14 <= 230`) to two independent,
unconditional theorems:

- `H1`: Semantic faithfulness of `Constant14.halts` in Mathlib's ZFC universe `ZFSet.{0}`
  (pure set-theoretic encoding soundness, with zero proof theory): for any Tarski truth
  predicate `tr` on `Semisentence L_set m` over `ZFSet.{0}` and any non-halting `n`-state
  binary Turing machine `M`, `Constant14.halts M` evaluates to `False`.
- `H2`: Glazer (2026) 230-state machine `K230` together with Godel's second incompleteness
  theorem for `ZFC`: assuming `ZFC` is consistent (`not Provable ZFC bot`), there exists
  a 230-state binary Turing machine `M` that does not halt and whose non-halting sentence
  `~Constant14.halts M` is not provable in `ZFC`.

Inside `main`, we prove completely from scratch in Lean 4 (with zero extra top-level `def`s):
1. Tarski term and formula evaluation for `L_set` in `ZFSet.{0}` via `Semiformula.rec`.
2. Universal de Bruijn substitution/rewriting compatibility (`evalF_rewAux`), negation
   compatibility (`evalF_neg`), free-variable-free specialization (`evalF_toEmpty`), and
   universal-closure soundness (`evalF_univCl`).
3. Full soundness of the one-sided Tait sequent calculus `FFL.FirstOrder.Derivation`
   (identity, cut, contraction, verum, or, and, all with free-variable shift, exs with
   term substitution).
4. Verification in `ZFSet.{0}` of all postulates of `ZFC`: equality laws (`refl`, `symm`,
   `trans`, `relExt`), Empty, Extensionality, Pairing, Union, Powerset, Infinity (`ZFSet.omega`),
   Foundation (`ZFSet.regularity`), Separation schema (`ZFSet.sep`), Replacement schema
   (`ZFSet.range` on `X : ZFSet.{0}` via `ZFSet.small_coe`), and Choice (`ZFSet.sep` on
   `sUnion` via `Classical.choose`).
5. Soundness of `ZFC` provability in `ZFSet.{0}`, yielding BOTH consistency `not Provable ZFC bot`
   and unprovability of false sentences, which combine with `H1`, `H2`, and `Nat.sInf_le` to
   establish `Constant14.C14 <= 230`.
-/

namespace OMA.R_Constant14_c14_upper_bound_R1

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

/-- Semantic faithfulness of `Constant14.halts` in Mathlib's `ZFSet.{0}`: for any Tarski truth
predicate `tr` on `FFL.FirstOrder.Semisentence ℒₛₑₜ m` over `ZFSet.{0}` and any non-halting
binary Turing machine `M`, `Constant14.halts M` evaluates to `False`. -/
def H1 : Prop :=
  ∀ tr : ∀ (m : ℕ), (Fin m → ZFSet.{0}) → FFL.FirstOrder.Semisentence ℒₛₑₜ m → Prop,
    (∀ m e, tr m e .verum ↔ True) →
    (∀ m e, tr m e .falsum ↔ False) →
    (∀ m e (v : Fin 2 → FFL.FirstOrder.Semiterm ℒₛₑₜ Empty m) (i j : Fin m),
      v 0 = FFL.FirstOrder.Semiterm.bvar i → v 1 = FFL.FirstOrder.Semiterm.bvar j →
      (tr m e (.rel .eq v) ↔ e i = e j)) →
    (∀ m e (v : Fin 2 → FFL.FirstOrder.Semiterm ℒₛₑₜ Empty m) (i j : Fin m),
      v 0 = FFL.FirstOrder.Semiterm.bvar i → v 1 = FFL.FirstOrder.Semiterm.bvar j →
      (tr m e (.rel .mem v) ↔ e i ∈ e j)) →
    (∀ m e (v : Fin 2 → FFL.FirstOrder.Semiterm ℒₛₑₜ Empty m) (i j : Fin m),
      v 0 = FFL.FirstOrder.Semiterm.bvar i → v 1 = FFL.FirstOrder.Semiterm.bvar j →
      (tr m e (.nrel .eq v) ↔ e i ≠ e j)) →
    (∀ m e (v : Fin 2 → FFL.FirstOrder.Semiterm ℒₛₑₜ Empty m) (i j : Fin m),
      v 0 = FFL.FirstOrder.Semiterm.bvar i → v 1 = FFL.FirstOrder.Semiterm.bvar j →
      (tr m e (.nrel .mem v) ↔ e i ∉ e j)) →
    (∀ m e φ ψ, tr m e (.and φ ψ) ↔ tr m e φ ∧ tr m e ψ) →
    (∀ m e φ ψ, tr m e (.or φ ψ) ↔ tr m e φ ∨ tr m e ψ) →
    (∀ m e φ, tr m e (.all φ) ↔ ∀ x : ZFSet.{0}, tr (m + 1) (Matrix.vecCons x e) φ) →
    (∀ m e φ, tr m e (.exs φ) ↔ ∃ x : ZFSet.{0}, tr (m + 1) (Matrix.vecCons x e) φ) →
    ∀ {n : ℕ} [NeZero n] (M : Turing.BusyBeaver.Machine (Fin 2) (Fin n)),
      ¬ M.IsHalting → ¬ tr 0 Fin.elim0 (Constant14.halts M)

/-- Glazer (2026) 230-state machine `K230` combined with Godel's second incompleteness theorem
for `𝗭𝗙𝗖`: assuming `𝗭𝗙𝗖` is consistent, there exists a 230-state binary Turing machine `M`
that does not halt and whose non-halting sentence `∼Constant14.halts M` is unprovable in `𝗭𝗙𝗖`. -/
def H2 : Prop :=
  ¬ FFL.Entailment.Provable 𝗭𝗙𝗖 (⊥ : FFL.FirstOrder.Sentence ℒₛₑₜ) →
    ∃ M : Turing.BusyBeaver.Machine (Fin 2) (Fin 230),
      ¬ M.IsHalting ∧ ¬ FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M)

section Helpers

private lemma zfc_soundness_zfset :
    ∃ tr : ∀ (m : ℕ), (Fin m → ZFSet.{0}) → FFL.FirstOrder.Semisentence ℒₛₑₜ m → Prop,
      (∀ m e, tr m e .verum ↔ True) ∧
      (∀ m e, tr m e .falsum ↔ False) ∧
      (∀ m e (v : Fin 2 → FFL.FirstOrder.Semiterm ℒₛₑₜ Empty m) (i j : Fin m),
        v 0 = FFL.FirstOrder.Semiterm.bvar i → v 1 = FFL.FirstOrder.Semiterm.bvar j →
        (tr m e (.rel .eq v) ↔ e i = e j)) ∧
      (∀ m e (v : Fin 2 → FFL.FirstOrder.Semiterm ℒₛₑₜ Empty m) (i j : Fin m),
        v 0 = FFL.FirstOrder.Semiterm.bvar i → v 1 = FFL.FirstOrder.Semiterm.bvar j →
        (tr m e (.rel .mem v) ↔ e i ∈ e j)) ∧
      (∀ m e (v : Fin 2 → FFL.FirstOrder.Semiterm ℒₛₑₜ Empty m) (i j : Fin m),
        v 0 = FFL.FirstOrder.Semiterm.bvar i → v 1 = FFL.FirstOrder.Semiterm.bvar j →
        (tr m e (.nrel .eq v) ↔ e i ≠ e j)) ∧
      (∀ m e (v : Fin 2 → FFL.FirstOrder.Semiterm ℒₛₑₜ Empty m) (i j : Fin m),
        v 0 = FFL.FirstOrder.Semiterm.bvar i → v 1 = FFL.FirstOrder.Semiterm.bvar j →
        (tr m e (.nrel .mem v) ↔ e i ∉ e j)) ∧
      (∀ m e φ ψ, tr m e (.and φ ψ) ↔ tr m e φ ∧ tr m e ψ) ∧
      (∀ m e φ ψ, tr m e (.or φ ψ) ↔ tr m e φ ∨ tr m e ψ) ∧
      (∀ m e φ, tr m e (.all φ) ↔ ∀ x : ZFSet.{0}, tr (m + 1) (Matrix.vecCons x e) φ) ∧
      (∀ m e φ, tr m e (.exs φ) ↔ ∃ x : ZFSet.{0}, tr (m + 1) (Matrix.vecCons x e) φ) ∧
      (∀ σ : FFL.FirstOrder.Sentence ℒₛₑₜ,
        FFL.Entailment.Provable 𝗭𝗙𝗖 σ → tr 0 Fin.elim0 σ) := by
  let evalT : ∀ {ξ : Type} {m : ℕ},
      (Fin m → ZFSet.{0}) → (ξ → ZFSet.{0}) → Semiterm ℒₛₑₜ ξ m → ZFSet.{0} :=
    fun b f t =>
      match t with
      | .bvar i => b i
      | .fvar x => f x
      | .func fn _ => Empty.elim fn
  let evalRel : ∀ {k : ℕ}, Language.Set.Rel k → (Fin k → ZFSet.{0}) → Prop :=
    fun r v =>
      match r with
      | .eq => v 0 = v 1
      | .mem => v 0 ∈ v 1
  let evalF : ∀ {ξ : Type} {m : ℕ},
      (Fin m → ZFSet.{0}) → (ξ → ZFSet.{0}) → Semiformula ℒₛₑₜ ξ m → Prop :=
    fun {ξ} {m} b f φ =>
      @Semiformula.rec ℒₛₑₜ ξ
        (fun n _ => (Fin n → ZFSet.{0}) → (ξ → ZFSet.{0}) → Prop)
        (fun _ _ => True)
        (fun _ _ => False)
        (fun r v b f => evalRel r (fun i => evalT b f (v i)))
        (fun r v b f => ¬ evalRel r (fun i => evalT b f (v i)))
        (fun _ _ ihφ ihψ b f => ihφ b f ∧ ihψ b f)
        (fun _ _ ihφ ihψ b f => ihφ b f ∨ ihψ b f)
        (fun _ ihφ b f => ∀ x : ZFSet.{0}, ihφ (Matrix.vecCons x b) f)
        (fun _ ihφ b f => ∃ x : ZFSet.{0}, ihφ (Matrix.vecCons x b) f)
        m φ b f
  have evalT_bvar : ∀ {ξ : Type} {m : ℕ} (b : Fin m → ZFSet.{0}) (f : ξ → ZFSet.{0}) (i : Fin m),
      evalT b f (.bvar i) = b i := fun _ _ _ => rfl
  have evalF_verum : ∀ {ξ : Type} {m : ℕ} (b : Fin m → ZFSet.{0}) (f : ξ → ZFSet.{0}),
      evalF b f (⊤ : Semiformula ℒₛₑₜ ξ m) ↔ True := fun _ _ => Iff.rfl
  have evalF_and : ∀ {ξ : Type} {m : ℕ} (b : Fin m → ZFSet.{0}) (f : ξ → ZFSet.{0})
      (φ ψ : Semiformula ℒₛₑₜ ξ m),
      evalF b f (φ ⋏ ψ) ↔ evalF b f φ ∧ evalF b f ψ := fun _ _ _ _ => Iff.rfl
  have evalF_or : ∀ {ξ : Type} {m : ℕ} (b : Fin m → ZFSet.{0}) (f : ξ → ZFSet.{0})
      (φ ψ : Semiformula ℒₛₑₜ ξ m),
      evalF b f (φ ⋎ ψ) ↔ evalF b f φ ∨ evalF b f ψ := fun _ _ _ _ => Iff.rfl
  have evalF_all : ∀ {ξ : Type} {m : ℕ} (b : Fin m → ZFSet.{0}) (f : ξ → ZFSet.{0})
      (φ : Semiformula ℒₛₑₜ ξ (m + 1)),
      evalF b f (∀¹ φ) ↔ ∀ x : ZFSet.{0}, evalF (Matrix.vecCons x b) f φ := fun _ _ _ => Iff.rfl
  have evalF_exs : ∀ {ξ : Type} {m : ℕ} (b : Fin m → ZFSet.{0}) (f : ξ → ZFSet.{0})
      (φ : Semiformula ℒₛₑₜ ξ (m + 1)),
      evalF b f (∃¹ φ) ↔ ∃ x : ZFSet.{0}, evalF (Matrix.vecCons x b) f φ := fun _ _ _ => Iff.rfl
  have evalT_rew : ∀ {ξ₁ ξ₂ : Type} {n₁ n₂ : ℕ}
      (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (t : Semiterm ℒₛₑₜ ξ₁ n₁)
      (b₂ : Fin n₂ → ZFSet.{0}) (f₂ : ξ₂ → ZFSet.{0}),
      evalT b₂ f₂ (ω t) =
        evalT (fun i => evalT b₂ f₂ (ω (.bvar i))) (fun x => evalT b₂ f₂ (ω (.fvar x))) t := by
    intro ξ₁ ξ₂ n₁ n₂ ω t b₂ f₂
    cases t with
    | bvar i => rfl
    | fvar x => rfl
    | func fn _ => exact Empty.elim fn
  have evalT_bShift : ∀ {ξ : Type} {m : ℕ} (t : Semiterm ℒₛₑₜ ξ m)
      (x : ZFSet.{0}) (b : Fin m → ZFSet.{0}) (f : ξ → ZFSet.{0}),
      evalT (Matrix.vecCons x b) f (Rew.bShift t) = evalT b f t := by
    intro ξ m t x b f
    cases t with
    | bvar i => rfl
    | fvar y => rfl
    | func fn _ => exact Empty.elim fn
  have evalF_rewAux : ∀ {ξ₁ ξ₂ : Type} {n₁ n₂ : ℕ}
      (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (φ : Semiformula ℒₛₑₜ ξ₁ n₁)
      (b₂ : Fin n₂ → ZFSet.{0}) (f₂ : ξ₂ → ZFSet.{0}),
      evalF b₂ f₂ (Semiformula.rewAux ω φ) ↔
        evalF (fun i => evalT b₂ f₂ (ω (.bvar i))) (fun x => evalT b₂ f₂ (ω (.fvar x))) φ := by
    intro ξ₁ ξ₂ n₁ n₂ ω φ
    induction φ generalizing n₂ with
    | verum => intro _ _; exact Iff.rfl
    | falsum => intro _ _; exact Iff.rfl
    | rel r v =>
      intro b₂ f₂
      have hv : (fun i => evalT b₂ f₂ (ω (v i))) =
          (fun i => evalT (fun j => evalT b₂ f₂ (ω (.bvar j)))
            (fun x => evalT b₂ f₂ (ω (.fvar x))) (v i)) :=
        funext fun i => evalT_rew ω (v i) b₂ f₂
      change evalRel r (fun i => evalT b₂ f₂ (ω (v i))) ↔ _
      rw [hv]
    | nrel r v =>
      intro b₂ f₂
      have hv : (fun i => evalT b₂ f₂ (ω (v i))) =
          (fun i => evalT (fun j => evalT b₂ f₂ (ω (.bvar j)))
            (fun x => evalT b₂ f₂ (ω (.fvar x))) (v i)) :=
        funext fun i => evalT_rew ω (v i) b₂ f₂
      change ¬ evalRel r (fun i => evalT b₂ f₂ (ω (v i))) ↔ _
      rw [hv]
    | and φ ψ ihφ ihψ =>
      intro b₂ f₂
      exact and_congr (ihφ ω b₂ f₂) (ihψ ω b₂ f₂)
    | or φ ψ ihφ ihψ =>
      intro b₂ f₂
      exact or_congr (ihφ ω b₂ f₂) (ihψ ω b₂ f₂)
    | all φ ih =>
      intro b₂ f₂
      refine forall_congr' fun x => ?_
      refine (ih ω.q (Matrix.vecCons x b₂) f₂).trans ?_
      have hb : (fun i => evalT (Matrix.vecCons x b₂) f₂ (ω.q (.bvar i))) =
          Matrix.vecCons x (fun i => evalT b₂ f₂ (ω (.bvar i))) := by
        funext i
        refine Fin.cases rfl (fun j => evalT_bShift (ω (.bvar j)) x b₂ f₂) i
      have hf : (fun y => evalT (Matrix.vecCons x b₂) f₂ (ω.q (.fvar y))) =
          (fun y => evalT b₂ f₂ (ω (.fvar y))) := by
        funext y
        exact evalT_bShift (ω (.fvar y)) x b₂ f₂
      rw [hb, hf]
    | exs φ ih =>
      intro b₂ f₂
      refine exists_congr fun x => ?_
      refine (ih ω.q (Matrix.vecCons x b₂) f₂).trans ?_
      have hb : (fun i => evalT (Matrix.vecCons x b₂) f₂ (ω.q (.bvar i))) =
          Matrix.vecCons x (fun i => evalT b₂ f₂ (ω (.bvar i))) := by
        funext i
        refine Fin.cases rfl (fun j => evalT_bShift (ω (.bvar j)) x b₂ f₂) i
      have hf : (fun y => evalT (Matrix.vecCons x b₂) f₂ (ω.q (.fvar y))) =
          (fun y => evalT b₂ f₂ (ω (.fvar y))) := by
        funext y
        exact evalT_bShift (ω (.fvar y)) x b₂ f₂
      rw [hb, hf]
  have evalF_app : ∀ {ξ₁ ξ₂ : Type} {n₁ n₂ : ℕ}
      (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (φ : Semiformula ℒₛₑₜ ξ₁ n₁)
      (b₂ : Fin n₂ → ZFSet.{0}) (f₂ : ξ₂ → ZFSet.{0}),
      evalF b₂ f₂ (ω ▹ φ) ↔
        evalF (fun i => evalT b₂ f₂ (ω (.bvar i))) (fun x => evalT b₂ f₂ (ω (.fvar x))) φ :=
    fun ω φ b₂ f₂ => evalF_rewAux ω φ b₂ f₂
  have evalF_subst : ∀ {ξ : Type} {n₁ n₂ : ℕ}
      (φ : Semiformula ℒₛₑₜ ξ n₁) (v : Fin n₁ → Semiterm ℒₛₑₜ ξ n₂)
      (b : Fin n₂ → ZFSet.{0}) (f : ξ → ZFSet.{0}),
      evalF b f (φ ⇜ v) ↔ evalF (fun i => evalT b f (v i)) f φ :=
    fun φ v b f => evalF_rewAux (Rew.subst v) φ b f
  have evalF_neg : ∀ {ξ : Type} {m : ℕ}
      (b : Fin m → ZFSet.{0}) (f : ξ → ZFSet.{0}) (φ : Semiformula ℒₛₑₜ ξ m),
      evalF b f (∼φ) ↔ ¬ evalF b f φ := by
    intro ξ m b f φ
    induction φ with
    | verum => exact not_true.symm
    | falsum => exact not_false_iff.symm
    | rel r v => exact Iff.rfl
    | nrel r v => exact not_not.symm
    | and φ ψ ihφ ihψ =>
      exact (or_congr (ihφ b) (ihψ b)).trans not_and_or.symm
    | or φ ψ ihφ ihψ =>
      exact (and_congr (ihφ b) (ihψ b)).trans not_or.symm
    | all φ ih =>
      exact (exists_congr fun x => ih (Matrix.vecCons x b)).trans not_forall.symm
    | exs φ ih =>
      exact (forall_congr' fun x => ih (Matrix.vecCons x b)).trans not_exists.symm
  have evalF_imp : ∀ {ξ : Type} {m : ℕ}
      (b : Fin m → ZFSet.{0}) (f : ξ → ZFSet.{0}) (φ ψ : Semiformula ℒₛₑₜ ξ m),
      evalF b f (φ 🡒 ψ) ↔ (evalF b f φ → evalF b f ψ) := by
    intro ξ m b f φ ψ
    change evalF b f ((∼φ) ⋎ ψ) ↔ _
    rw [evalF_or, evalF_neg, imp_iff_not_or]
  have evalF_iff : ∀ {ξ : Type} {m : ℕ}
      (b : Fin m → ZFSet.{0}) (f : ξ → ZFSet.{0}) (φ ψ : Semiformula ℒₛₑₜ ξ m),
      evalF b f (φ 🡘 ψ) ↔ (evalF b f φ ↔ evalF b f ψ) := by
    intro ξ m b f φ ψ
    change evalF b f ((φ 🡒 ψ) ⋏ (ψ 🡒 φ)) ↔ _
    rw [evalF_and, evalF_imp, evalF_imp]
    exact iff_iff_implies_and_implies.symm
  have evalF_eq : ∀ {ξ : Type} {m : ℕ}
      (b : Fin m → ZFSet.{0}) (f : ξ → ZFSet.{0}) (t u : Semiterm ℒₛₑₜ ξ m),
      evalF b f (Semiformula.Operator.operator Semiformula.Operator.Eq.eq ![t, u]) ↔
        evalT b f t = evalT b f u := by
    intro ξ m b f t u
    unfold Semiformula.Operator.operator
    rw [evalF_subst, evalF_app]
    exact Iff.rfl
  have evalF_mem : ∀ {ξ : Type} {m : ℕ}
      (b : Fin m → ZFSet.{0}) (f : ξ → ZFSet.{0}) (t u : Semiterm ℒₛₑₜ ξ m),
      evalF b f (Semiformula.Operator.operator Semiformula.Operator.Mem.mem ![t, u]) ↔
        evalT b f t ∈ evalT b f u := by
    intro ξ m b f t u
    unfold Semiformula.Operator.operator
    rw [evalF_subst, evalF_app]
    exact Iff.rfl
  have evalF_ballMem : ∀ {ξ : Type} {m : ℕ}
      (b : Fin m → ZFSet.{0}) (f : ξ → ZFSet.{0})
      (t : Semiterm ℒₛₑₜ ξ m) (φ : Semiformula ℒₛₑₜ ξ (m + 1)),
      evalF b f (Semiformula.ballMem t φ) ↔
        ∀ x ∈ evalT b f t, evalF (Matrix.vecCons x b) f φ := by
    intro ξ m b f t φ
    unfold Semiformula.ballMem ball
    rw [evalF_all]
    refine forall_congr' fun x => ?_
    rw [evalF_imp, evalF_mem, evalT_bShift t x b f]
    exact Iff.rfl
  have evalF_bexsMem : ∀ {ξ : Type} {m : ℕ}
      (b : Fin m → ZFSet.{0}) (f : ξ → ZFSet.{0})
      (t : Semiterm ℒₛₑₜ ξ m) (φ : Semiformula ℒₛₑₜ ξ (m + 1)),
      evalF b f (Semiformula.bexsMem t φ) ↔
        ∃ x ∈ evalT b f t, evalF (Matrix.vecCons x b) f φ := by
    intro ξ m b f t φ
    unfold Semiformula.bexsMem bexs
    rw [evalF_exs]
    refine exists_congr fun x => ?_
    rw [evalF_and, evalF_mem, evalT_bShift t x b f]
    exact Iff.rfl
  have evalF_existsUnique : ∀ {ξ : Type} {m : ℕ}
      (b : Fin m → ZFSet.{0}) (f : ξ → ZFSet.{0}) (φ : Semiformula ℒₛₑₜ ξ (m + 1)),
      evalF b f (∃¹! φ) ↔ ∃! y : ZFSet.{0}, evalF (Matrix.vecCons y b) f φ := by
    intro ξ m b f φ
    unfold Semiformula.existsUnique
    rw [evalF_exs]
    refine exists_congr fun y => ?_
    rw [evalF_and, evalF_subst, evalF_all]
    have h1 : (fun i : Fin (m + 1) =>
        evalT (Matrix.vecCons y b) f
          (Matrix.vecCons (.bvar 0) (fun x : Fin m => .bvar (BinderNotation.finSuccItr x 1)) i)) =
        Matrix.vecCons y b := by
      funext i
      refine Fin.cases rfl (fun j => rfl) i
    rw [h1]
    refine and_congr Iff.rfl (forall_congr' fun z => ?_)
    rw [evalF_imp, evalF_subst, evalF_eq]
    have h2 : (fun i : Fin (m + 1) =>
        evalT (Matrix.vecCons z (Matrix.vecCons y b)) f
          (Matrix.vecCons (.bvar 0) (fun x : Fin m => .bvar (BinderNotation.finSuccItr x 2)) i)) =
        Matrix.vecCons z b := by
      funext i
      refine Fin.cases rfl (fun j => rfl) i
    rw [h2]
    exact Iff.rfl
  have evalF_isSubsetOf : ∀ {m : ℕ} (b : Fin m → ZFSet.{0})
      (t u : Semiterm ℒₛₑₜ Empty m),
      evalF b Empty.elim (isSubsetOf ⇜ ![t, u]) ↔ evalT b Empty.elim t ⊆ evalT b Empty.elim u := by
    intro m b t u
    rw [evalF_subst]
    unfold isSubsetOf
    rw [evalF_ballMem]
    refine forall_congr' fun z => imp_congr Iff.rfl ?_
    rw [evalF_mem]
    exact Iff.rfl
  have evalF_isEmpty : ∀ {m : ℕ} (b : Fin m → ZFSet.{0})
      (t : Semiterm ℒₛₑₜ Empty m),
      evalF b Empty.elim (isEmpty ⇜ ![t]) ↔ ∀ y : ZFSet.{0}, y ∉ evalT b Empty.elim t := by
    intro m b t
    rw [evalF_subst]
    unfold isEmpty
    rw [evalF_all]
    refine forall_congr' fun y => ?_
    rw [evalF_neg, evalF_mem]
    exact Iff.rfl
  have evalF_isNonempty : ∀ {m : ℕ} (b : Fin m → ZFSet.{0})
      (t : Semiterm ℒₛₑₜ Empty m),
      evalF b Empty.elim (isNonempty ⇜ ![t]) ↔ ∃ y : ZFSet.{0}, y ∈ evalT b Empty.elim t := by
    intro m b t
    rw [evalF_subst]
    unfold isNonempty
    rw [evalF_exs]
    refine exists_congr fun y => ?_
    rw [evalF_mem]
    exact Iff.rfl
  have evalF_isSucc : ∀ {m : ℕ} (b : Fin m → ZFSet.{0})
      (t u : Semiterm ℒₛₑₜ Empty m),
      evalF b Empty.elim (isSucc ⇜ ![t, u]) ↔
        ∀ z : ZFSet.{0}, z ∈ evalT b Empty.elim t ↔
          z = evalT b Empty.elim u ∨ z ∈ evalT b Empty.elim u := by
    intro m b t u
    rw [evalF_subst]
    unfold isSucc
    rw [evalF_all]
    refine forall_congr' fun z => ?_
    rw [evalF_iff, evalF_mem, evalF_or, evalF_eq, evalF_mem]
    exact Iff.rfl
  have evalT_toEmpty : ∀ {m : ℕ} (t : Semiterm ℒₛₑₜ ℕ m) (ht : t.freeVariables = ∅)
      (b : Fin m → ZFSet.{0}) (f : ℕ → ZFSet.{0}),
      evalT b Empty.elim (t.toEmpty ht) = evalT b f t := by
    intro m t ht b f
    cases t with
    | bvar i => rfl
    | fvar x => exact False.elim (by simp [Semiterm.freeVariables] at ht)
    | func fn _ => exact Empty.elim fn
  have evalF_toEmpty : ∀ {m : ℕ} (φ : Semiproposition ℒₛₑₜ m) (h : φ.freeVariables = ∅)
      (b : Fin m → ZFSet.{0}) (f : ℕ → ZFSet.{0}),
      evalF b Empty.elim (φ.toEmpty h) ↔ evalF b f φ := by
    intro m φ
    induction φ with
    | verum => intro _ _ _; exact Iff.rfl
    | falsum => intro _ _ _; exact Iff.rfl
    | rel r v =>
      intro h b f
      have hvi : ∀ i, (v i).freeVariables = ∅ := fun i =>
        Finset.subset_empty.mp
          (h ▸ Finset.subset_biUnion_of_mem (fun j => (v j).freeVariables) (Finset.mem_univ i))
      have hv : (fun i => evalT b Empty.elim ((v i).toEmpty (hvi i))) =
          (fun i => evalT b f (v i)) :=
        funext fun i => evalT_toEmpty (v i) (hvi i) b f
      change evalRel r (fun i => evalT b Empty.elim ((v i).toEmpty (hvi i))) ↔ _
      rw [hv]
    | nrel r v =>
      intro h b f
      have hvi : ∀ i, (v i).freeVariables = ∅ := fun i =>
        Finset.subset_empty.mp
          (h ▸ Finset.subset_biUnion_of_mem (fun j => (v j).freeVariables) (Finset.mem_univ i))
      have hv : (fun i => evalT b Empty.elim ((v i).toEmpty (hvi i))) =
          (fun i => evalT b f (v i)) :=
        funext fun i => evalT_toEmpty (v i) (hvi i) b f
      change ¬ evalRel r (fun i => evalT b Empty.elim ((v i).toEmpty (hvi i))) ↔ _
      rw [hv]
    | and φ ψ ihφ ihψ =>
      intro h b f
      exact and_congr (ihφ (Finset.union_eq_empty.mp h).1 b f)
        (ihψ (Finset.union_eq_empty.mp h).2 b f)
    | or φ ψ ihφ ihψ =>
      intro h b f
      exact or_congr (ihφ (Finset.union_eq_empty.mp h).1 b f)
        (ihψ (Finset.union_eq_empty.mp h).2 b f)
    | all φ ih =>
      intro h b f
      exact forall_congr' fun x => ih h (Matrix.vecCons x b) f
    | exs φ ih =>
      intro h b f
      exact exists_congr fun x => ih h (Matrix.vecCons x b) f
  have evalF_allClosure : ∀ {ξ : Type} {k : ℕ}
      (φ : Semiformula ℒₛₑₜ ξ k) (f : ξ → ZFSet.{0}),
      (∀ b : Fin k → ZFSet.{0}, evalF b f φ) → evalF Fin.elim0 f (∀¹* φ) := by
    intro ξ k
    induction k with
    | zero =>
      intro φ f h
      exact h Fin.elim0
    | succ k ih =>
      intro φ f h
      exact ih (∀¹ φ) f fun b x => h (Matrix.vecCons x b)
  have evalF_univCl : ∀ (φ : Proposition ℒₛₑₜ),
      (∀ f : ℕ → ZFSet.{0}, evalF Fin.elim0 f φ) → evalF Fin.elim0 Empty.elim φ.univCl := by
    intro φ h
    unfold Semiformula.univCl
    rw [evalF_toEmpty (f := fun _ => ∅)]
    unfold Semiformula.univCl'
    refine evalF_allClosure _ (fun _ => ∅) fun b => ?_
    rw [evalF_app]
    have hb0 : (fun i : Fin 0 => evalT b (fun _ => ∅) (Rew.fixitr 0 φ.fvSup (.bvar i))) =
        Fin.elim0 := funext fun i => i.elim0
    rw [hb0]
    exact h _
  have derivation_sound : ∀ {Γ : Sequent ℒₛₑₜ}, Derivation Γ →
      ∀ f : ℕ → ZFSet.{0}, ∃ φ ∈ Γ, evalF Fin.elim0 f φ := by
    intro Γ d
    induction d with
    | identity r v =>
      intro f
      by_cases h : evalRel r (fun i => evalT Fin.elim0 f (v i))
      · exact ⟨.rel r v, by simp [Multiset.atom], h⟩
      · exact ⟨.nrel r v, by simp [Multiset.atom], h⟩
    | @cut Γ φ Δ _ _ ih₁ ih₂ =>
      intro f
      obtain ⟨ψ, hψ, hvψ⟩ := ih₁ f
      rcases Multiset.mem_add.mp hψ with hψΓ | hψφ
      · exact ⟨ψ, Multiset.mem_add.mpr (Or.inl hψΓ), hvψ⟩
      · have heq : ψ = φ := by simpa [Multiset.atom] using hψφ
        rw [heq] at hvψ
        obtain ⟨χ, hχ, hvχ⟩ := ih₂ f
        rcases Multiset.mem_add.mp hχ with hχΔ | hχnφ
        · exact ⟨χ, Multiset.mem_add.mpr (Or.inr hχΔ), hvχ⟩
        · have heq2 : χ = ∼φ := by simpa [Multiset.atom] using hχnφ
          rw [heq2] at hvχ
          exact ((evalF_neg Fin.elim0 f φ).mp hvχ hvψ).elim
    | contraction _ hsub ih =>
      intro f
      obtain ⟨ψ, hψ, hvψ⟩ := ih f
      exact ⟨ψ, hsub hψ, hvψ⟩
    | verum =>
      intro _
      exact ⟨⊤, by simp [Multiset.atom], trivial⟩
    | @or Γ φ ψ _ ih =>
      intro f
      obtain ⟨χ, hχ, hvχ⟩ := ih f
      rcases Multiset.mem_add.mp hχ with hχΓ | hχpair
      · exact ⟨χ, Multiset.mem_add.mpr (Or.inl hχΓ), hvχ⟩
      · have hor_mem : χ = φ ∨ χ = ψ := by simpa [Multiset.atom] using hχpair
        rcases hor_mem with h1 | h2
        · rw [h1] at hvχ
          exact ⟨φ ⋎ ψ, Multiset.mem_add.mpr (Or.inr (by simp [Multiset.atom])), Or.inl hvχ⟩
        · rw [h2] at hvχ
          exact ⟨φ ⋎ ψ, Multiset.mem_add.mpr (Or.inr (by simp [Multiset.atom])), Or.inr hvχ⟩
    | @and Γ φ ψ _ _ ih₁ ih₂ =>
      intro f
      obtain ⟨χ₁, hχ₁, hv₁⟩ := ih₁ f
      rcases Multiset.mem_add.mp hχ₁ with hχ₁Γ | hχ₁φ
      · exact ⟨χ₁, Multiset.mem_add.mpr (Or.inl hχ₁Γ), hv₁⟩
      · have heq₁ : χ₁ = φ := by simpa [Multiset.atom] using hχ₁φ
        rw [heq₁] at hv₁
        obtain ⟨χ₂, hχ₂, hv₂⟩ := ih₂ f
        rcases Multiset.mem_add.mp hχ₂ with hχ₂Γ | hχ₂ψ
        · exact ⟨χ₂, Multiset.mem_add.mpr (Or.inl hχ₂Γ), hv₂⟩
        · have heq₂ : χ₂ = ψ := by simpa [Multiset.atom] using hχ₂ψ
          rw [heq₂] at hv₂
          exact ⟨φ ⋏ ψ, Multiset.mem_add.mpr (Or.inr (by simp [Multiset.atom])), ⟨hv₁, hv₂⟩⟩
    | @all Γ φ _ ih =>
      intro f
      by_cases hΓ : ∃ ψ ∈ Γ, evalF Fin.elim0 f ψ
      · obtain ⟨ψ, hψΓ, hvψ⟩ := hΓ
        exact ⟨ψ, Multiset.mem_add.mpr (Or.inl hψΓ), hvψ⟩
      · refine ⟨∀¹ φ, Multiset.mem_add.mpr (Or.inr (by simp [Multiset.atom])), ?_⟩
        rw [evalF_all]
        intro x
        let f' : ℕ → ZFSet.{0} := fun
          | 0 => x
          | m + 1 => f m
        obtain ⟨χ, hχ, hvχ⟩ := ih f'
        rcases Multiset.mem_add.mp hχ with hχs | hχf
        · obtain ⟨ψ, hψΓ, rfl⟩ := Multiset.mem_map.mp hχs
          have hsh : evalF Fin.elim0 f' (Rewriting.shift ψ) ↔ evalF Fin.elim0 f ψ := by
            rw [evalF_app]
            have hb0 : (fun i : Fin 0 => evalT Fin.elim0 f' (Rew.shift (.bvar i))) = Fin.elim0 :=
              funext fun i => i.elim0
            have hf0 : (fun m : ℕ => evalT Fin.elim0 f' (Rew.shift (.fvar m))) = f := by
              funext m; rfl
            rw [hb0, hf0]
          exact (hΓ ⟨ψ, hψΓ, hsh.mp hvχ⟩).elim
        · have heq : χ = φ.free := by simpa [Multiset.atom] using hχf
          subst heq
          rw [evalF_app] at hvχ
          have hb1 : (fun i : Fin 1 => evalT Fin.elim0 f' (Rew.free (.bvar i))) =
              Matrix.vecCons x Fin.elim0 := by
            funext i
            refine Fin.cases rfl (fun j => j.elim0) i
          have hf1 : (fun m : ℕ => evalT Fin.elim0 f' (Rew.free (.fvar m))) = f := by
            funext m; rfl
          rwa [hb1, hf1] at hvχ
    | @exs Γ φ t _ ih =>
      intro f
      obtain ⟨χ, hχ, hvχ⟩ := ih f
      rcases Multiset.mem_add.mp hχ with hχΓ | hχt
      · exact ⟨χ, Multiset.mem_add.mpr (Or.inl hχΓ), hvχ⟩
      · have heq : χ = φ/[t] := by simpa [Multiset.atom] using hχt
        subst heq
        refine ⟨∃¹ φ, Multiset.mem_add.mpr (Or.inr (by simp [Multiset.atom])), ?_⟩
        rw [evalF_exs]
        refine ⟨evalT Fin.elim0 f t, ?_⟩
        rw [evalF_subst] at hvχ
        have hb1 : (fun i : Fin 1 => evalT Fin.elim0 f (![t] i)) =
            Matrix.vecCons (evalT Fin.elim0 f t) Fin.elim0 := by
          funext i
          refine Fin.cases rfl (fun j => j.elim0) i
        rwa [hb1] at hvχ
  have zfc_axioms_valid : ∀ ψ ∈ 𝗭𝗙𝗖, evalF Fin.elim0 Empty.elim ψ := by
    intro ψ hψ
    rcases hψ with hZF | hAC
    · cases hZF with
      | axiom_of_equality φ hEQ =>
        cases hEQ with
        | refl =>
          unfold Theory.Eq.refl
          rw [evalF_all]
          intro x
          rw [evalF_eq]
        | symm =>
          unfold Theory.Eq.symm
          rw [evalF_all]
          intro x
          rw [evalF_all]
          intro y
          rw [evalF_imp, evalF_eq, evalF_eq]
          exact Eq.symm
        | trans =>
          unfold Theory.Eq.trans
          rw [evalF_all]
          intro x
          rw [evalF_all]
          intro y
          rw [evalF_all]
          intro z
          rw [evalF_imp, evalF_imp, evalF_eq, evalF_eq, evalF_eq]
          exact Eq.trans
        | funcExt fn =>
          exact Empty.elim fn
        | relExt r =>
          unfold Theory.Eq.relExt
          refine evalF_allClosure _ Empty.elim fun b => ?_
          cases r with
          | eq =>
            rw [evalF_imp, evalF_imp]
            intro hconj hrel
            simp only [Matrix.conj, Matrix.vecTail, Function.comp_apply, evalF_and, evalF_verum,
              evalF_eq, evalT_bvar] at hconj
            change b ((0 : Fin 2).addCast 2) = b ((1 : Fin 2).addCast 2) at hrel
            change b ((0 : Fin 2).addNat 2) = b ((1 : Fin 2).addNat 2)
            exact hconj.1.symm.trans (hrel.trans hconj.2.1)
          | mem =>
            rw [evalF_imp, evalF_imp]
            intro hconj hrel
            simp only [Matrix.conj, Matrix.vecTail, Function.comp_apply, evalF_and, evalF_verum,
              evalF_eq, evalT_bvar] at hconj
            change b ((0 : Fin 2).addCast 2) ∈ b ((Fin.succ 0 : Fin 2).addCast 2) at hrel
            change b ((0 : Fin 2).addNat 2) ∈ b ((Fin.succ 0 : Fin 2).addNat 2)
            rwa [← hconj.1, ← hconj.2.1]
      | axiom_of_empty_set =>
        unfold Axiom.empty
        rw [evalF_exs]
        refine ⟨∅, ?_⟩
        rw [evalF_all]
        intro y
        rw [evalF_neg, evalF_mem]
        exact ZFSet.notMem_empty y
      | axiom_of_extentionality =>
        unfold Axiom.extentionality
        rw [evalF_all]
        intro x
        rw [evalF_all]
        intro y
        rw [evalF_iff, evalF_eq, evalF_all]
        refine ZFSet.ext_iff.trans (forall_congr' fun z => ?_)
        rw [evalF_iff, evalF_mem, evalF_mem]
        exact Iff.rfl
      | axiom_of_pairing =>
        unfold Axiom.pairing
        rw [evalF_all]
        intro x
        rw [evalF_all]
        intro y
        rw [evalF_exs]
        refine ⟨{x, y}, ?_⟩
        rw [evalF_all]
        intro w
        rw [evalF_iff, evalF_mem, evalF_or, evalF_eq, evalF_eq]
        exact ZFSet.mem_pair
      | axiom_of_union =>
        unfold Axiom.union
        rw [evalF_all]
        intro x
        rw [evalF_exs]
        refine ⟨ZFSet.sUnion x, ?_⟩
        rw [evalF_all]
        intro z
        rw [evalF_iff, evalF_mem, evalF_bexsMem]
        refine ZFSet.mem_sUnion.trans (exists_congr fun w => and_congr Iff.rfl ?_)
        rw [evalF_mem]
        exact Iff.rfl
      | axiom_of_power_set =>
        unfold Axiom.power
        rw [evalF_all]
        intro x
        rw [evalF_exs]
        refine ⟨ZFSet.powerset x, ?_⟩
        rw [evalF_all]
        intro z
        rw [evalF_iff, evalF_mem, evalF_isSubsetOf]
        exact ZFSet.mem_powerset
      | axiom_of_infinity =>
        unfold Axiom.infinity
        rw [evalF_exs]
        refine ⟨ZFSet.omega, ?_⟩
        rw [evalF_and]
        constructor
        · rw [evalF_all]
          intro e
          rw [evalF_imp, evalF_isEmpty, evalF_mem]
          intro hempty
          have he : e = ∅ := (ZFSet.eq_empty e).mpr hempty
          rw [he]
          exact ZFSet.omega_zero
        · rw [evalF_ballMem]
          intro x hx
          rw [evalF_all]
          intro x'
          rw [evalF_imp, evalF_isSucc, evalF_mem]
          intro hsucc
          have hx' : x' = insert x x := by
            ext z
            exact (hsucc z).trans ZFSet.mem_insert_iff.symm
          rw [hx']
          exact ZFSet.omega_succ hx
      | axiom_of_foundation =>
        unfold Axiom.foundation
        rw [evalF_all]
        intro x
        rw [evalF_imp, evalF_isNonempty]
        rintro ⟨y₀, hy₀⟩
        have hxne : x ≠ ∅ := fun h => ZFSet.notMem_empty y₀ (h ▸ hy₀)
        obtain ⟨y, hyx, hxy⟩ := ZFSet.regularity x hxne
        rw [evalF_bexsMem]
        refine ⟨y, hyx, ?_⟩
        rw [evalF_ballMem]
        intro z hzx
        rw [evalF_neg, evalF_mem]
        intro hzy
        exact ZFSet.notMem_empty z (hxy ▸ ZFSet.mem_inter.mpr ⟨hzx, hzy⟩)
      | axiom_of_separation φ =>
        unfold Axiom.separationSchema
        refine evalF_univCl _ fun f => ?_
        rw [evalF_all]
        intro x
        rw [evalF_exs]
        refine ⟨x.sep fun z => evalF ![z] f φ, ?_⟩
        rw [evalF_all]
        intro z
        rw [evalF_iff, evalF_mem, evalF_and, evalF_mem, evalF_subst]
        change z ∈ (x.sep fun z => evalF ![z] f φ) ↔
          z ∈ x ∧ evalF (fun i : Fin 1 =>
            evalT (Matrix.vecCons z (Matrix.vecCons (x.sep fun z => evalF ![z] f φ)
              (Matrix.vecCons x Fin.elim0))) f (![.bvar 0] i)) f φ
        refine ZFSet.mem_sep.trans (and_congr Iff.rfl ?_)
        have hb : (fun i : Fin 1 =>
            evalT (Matrix.vecCons z (Matrix.vecCons (x.sep fun z => evalF ![z] f φ)
              (Matrix.vecCons x Fin.elim0))) f (![.bvar 0] i)) = ![z] := by
          funext i
          refine Fin.cases rfl (fun j => j.elim0) i
        rw [hb]
      | axiom_of_replacement φ =>
        unfold Axiom.replacementSchema
        refine evalF_univCl _ fun f => ?_
        rw [evalF_imp]
        intro hfunc
        rw [evalF_all] at hfunc ⊢
        intro X
        have hfunc' : ∀ x : ZFSet.{0}, ∃! y : ZFSet.{0}, evalF ![x, y] f φ := by
          intro x
          have hx := (evalF_existsUnique (Matrix.vecCons x Fin.elim0) f _).mp (hfunc x)
          rcases hx with ⟨y, hy, huniq⟩
          refine ⟨y, ?_, fun z hz => huniq z ?_⟩
          · rw [evalF_subst] at hy
            have hb : (fun i : Fin 2 =>
                evalT (Matrix.vecCons y (Matrix.vecCons x Fin.elim0)) f
                  (![.bvar 1, .bvar 0] i)) = ![x, y] := by
              funext i
              refine Fin.cases rfl (fun j => Fin.cases rfl (fun k => k.elim0) j) i
            rwa [hb] at hy
          · dsimp only at hz ⊢
            rw [evalF_subst]
            have hb : (fun i : Fin 2 =>
                evalT (Matrix.vecCons z (Matrix.vecCons x Fin.elim0)) f
                  (![.bvar 1, .bvar 0] i)) = ![x, z] := by
              funext i
              refine Fin.cases rfl (fun j => Fin.cases rfl (fun k => k.elim0) j) i
            rwa [hb]
        let g : ZFSet.{0} → ZFSet.{0} := fun x => (hfunc' x).choose
        have hg_spec : ∀ x, evalF ![x, g x] f φ := fun x => (hfunc' x).choose_spec.1
        have hg_uniq : ∀ x y, evalF ![x, y] f φ → y = g x := fun x y h =>
          (hfunc' x).choose_spec.2 y h
        let Y : ZFSet.{0} := ZFSet.range fun a : X => g a.1
        rw [evalF_exs]
        refine ⟨Y, ?_⟩
        rw [evalF_all]
        intro y
        rw [evalF_iff, evalF_mem, evalF_bexsMem]
        constructor
        · intro hyY
          obtain ⟨⟨x, hxX⟩, rfl⟩ := ZFSet.mem_range.mp hyY
          refine ⟨x, hxX, ?_⟩
          rw [evalF_subst]
          have hb : (fun i : Fin 2 =>
              evalT (Matrix.vecCons x (Matrix.vecCons (g x) (Matrix.vecCons Y (Matrix.vecCons X Fin.elim0)))) f
                (![.bvar 0, .bvar 1] i)) = ![x, g x] := by
            funext i
            refine Fin.cases rfl (fun j => Fin.cases rfl (fun k => k.elim0) j) i
          rw [hb]
          exact hg_spec x
        · rintro ⟨x, hxX, hP⟩
          rw [evalF_subst] at hP
          have hb : (fun i : Fin 2 =>
              evalT (Matrix.vecCons x (Matrix.vecCons y (Matrix.vecCons Y (Matrix.vecCons X Fin.elim0)))) f
                (![.bvar 0, .bvar 1] i)) = ![x, y] := by
            funext i
            refine Fin.cases rfl (fun j => Fin.cases rfl (fun k => k.elim0) j) i
          rw [hb] at hP
          exact ZFSet.mem_range.mpr ⟨⟨x, hxX⟩, (hg_uniq x y hP).symm⟩
    · classical
      have hψ_eq : ψ = Axiom.choice := hAC
      subst hψ_eq
      unfold Axiom.choice
      rw [evalF_all]
      intro 𝓧
      rw [evalF_imp, evalF_and]
      rintro ⟨hne_raw, hdisj_raw⟩
      have hne : ∀ X ∈ 𝓧, ∃ y : ZFSet.{0}, y ∈ X := by
        rw [evalF_ballMem] at hne_raw
        intro X hX
        have h1 := hne_raw X hX
        rwa [evalF_isNonempty] at h1
      have hdisj : ∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ z : ZFSet.{0}, z ∈ X ∧ z ∈ Y) → X = Y := by
        rw [evalF_ballMem] at hdisj_raw
        intro X hX Y hY hz
        have h1 := hdisj_raw X hX
        rw [evalF_ballMem] at h1
        have h2 := h1 Y hY
        rw [evalF_imp, evalF_eq, evalF_exs] at h2
        apply h2
        obtain ⟨z, hzX, hzY⟩ := hz
        refine ⟨z, ?_⟩
        rw [evalF_and, evalF_mem, evalF_mem]
        exact ⟨hzX, hzY⟩
      let g : ZFSet.{0} → ZFSet.{0} := fun X =>
        if h : ∃ y : ZFSet.{0}, y ∈ X then h.choose else ∅
      have hg_mem : ∀ X ∈ 𝓧, g X ∈ X := by
        intro X hX
        have h : ∃ y : ZFSet.{0}, y ∈ X := hne X hX
        simp only [g, dif_pos h]
        exact h.choose_spec
      let C : ZFSet.{0} := (ZFSet.sUnion 𝓧).sep fun z => ∃ X ∈ 𝓧, z = g X
      rw [evalF_exs]
      refine ⟨C, ?_⟩
      rw [evalF_ballMem]
      intro X hX
      change X ∈ 𝓧 at hX
      rw [evalF_existsUnique]
      refine ⟨g X, ?_, ?_⟩
      · dsimp only
        rw [evalF_and, evalF_mem, evalF_mem]
        change g X ∈ C ∧ g X ∈ X
        exact ⟨ZFSet.mem_sep.mpr ⟨ZFSet.mem_sUnion.mpr ⟨X, hX, hg_mem X hX⟩, ⟨X, hX, rfl⟩⟩,
          hg_mem X hX⟩
      · intro z hz
        rw [evalF_and, evalF_mem, evalF_mem] at hz
        rcases hz with ⟨hzC, hzX⟩
        change z ∈ C at hzC
        change z ∈ X at hzX
        obtain ⟨_, Y, hY, rfl⟩ := ZFSet.mem_sep.mp hzC
        have hXY : X = Y := hdisj X hX Y hY ⟨g Y, hzX, hg_mem Y hY⟩
        rw [hXY]
  refine ⟨fun m e φ => evalF e Empty.elim φ,
    fun _ _ => Iff.rfl,
    fun _ _ => Iff.rfl,
    ?_, ?_, ?_, ?_,
    fun _ _ _ _ => Iff.rfl,
    fun _ _ _ _ => Iff.rfl,
    fun _ _ _ => Iff.rfl,
    fun _ _ _ => Iff.rfl,
    ?_⟩
  · intro m e v i j h0 h1
    change evalT e Empty.elim (v 0) = evalT e Empty.elim (v 1) ↔ e i = e j
    rw [h0, h1]
  · intro m e v i j h0 h1
    change evalT e Empty.elim (v 0) ∈ evalT e Empty.elim (v 1) ↔ e i ∈ e j
    rw [h0, h1]
  · intro m e v i j h0 h1
    change ¬ (evalT e Empty.elim (v 0) = evalT e Empty.elim (v 1)) ↔ e i ≠ e j
    rw [h0, h1]
  · intro m e v i j h0 h1
    change ¬ (evalT e Empty.elim (v 0) ∈ evalT e Empty.elim (v 1)) ↔ e i ∉ e j
    rw [h0, h1]
  · intro σ hprov
    obtain ⟨⟨axs, hmem, hderiv⟩⟩ := hprov
    obtain ⟨χ, hχ, hvχ⟩ := derivation_sound hderiv (fun _ => ∅)
    obtain ⟨τ, hτ, rfl⟩ := Multiset.mem_map.mp hχ
    have hemb : evalF Fin.elim0 (fun _ : ℕ => ∅) (Rewriting.emb (ξ := ℕ) τ) ↔
        evalF Fin.elim0 Empty.elim τ := by
      rw [evalF_app]
      have hb0 : (fun i : Fin 0 => evalT Fin.elim0 (fun _ : ℕ => ∅)
          (Rew.emb (o := Empty) (ξ := ℕ) (.bvar i))) = Fin.elim0 :=
        funext fun i => i.elim0
      have hf0 : (fun x : Empty => evalT Fin.elim0 (fun _ : ℕ => ∅)
          (Rew.emb (o := Empty) (ξ := ℕ) (.fvar x))) = Empty.elim :=
        funext fun x => x.elim
      rw [hb0, hf0]
    have hvτ : evalF Fin.elim0 Empty.elim τ := hemb.mp hvχ
    rcases Multiset.mem_add.mp hτ with hτσ | hτax
    · have heq : τ = σ := by simpa [Multiset.atom] using hτσ
      exact heq ▸ hvτ
    · obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.mp hτax
      exact ((evalF_neg Fin.elim0 Empty.elim α).mp hvτ (zfc_axioms_valid α (hmem α hα))).elim

end Helpers

theorem main : H1 → H2 → type_of% @Constant14.c14_upper_bound := by
  intro hH1 hH2
  obtain ⟨tr, hv, hf, hreq, hrmem, hnreq, hnrmem, hand, hor, hall, hexs, hsound⟩ :=
    zfc_soundness_zfset
  have hcons : ¬ FFL.Entailment.Provable 𝗭𝗙𝗖 (⊥ : FFL.FirstOrder.Sentence ℒₛₑₜ) := by
    intro hbot
    exact (hf 0 Fin.elim0).mp (hsound ⊥ hbot)
  obtain ⟨M, hnotHalt, hnotRefute⟩ := hH2 hcons
  have hnotProve : ¬ FFL.Entailment.Provable 𝗭𝗙𝗖 (Constant14.halts M) := by
    intro hprov
    have htrue : tr 0 Fin.elim0 (Constant14.halts M) := hsound (Constant14.halts M) hprov
    exact hH1 tr hv hf hreq hrmem hnreq hnrmem hand hor hall hexs M hnotHalt htrue
  exact Nat.sInf_le ⟨inferInstance, M, hnotProve, hnotRefute⟩

end OMA.R_Constant14_c14_upper_bound_R1
