import OMAStatements.S_arxiv_2312_14661
import Mathlib

namespace OMA.P_arxiv_2312_14661

open FirstOrder OMA.S_arxiv_2312_14661

private lemma realize_bf1 {L : FirstOrder.Language} {α M : Type*} [L.Structure M] {n : ℕ}
    (r : L.Relations 1) (t : L.Term (α ⊕ Fin n)) (v : α → M) (xs : Fin n → M) :
    (FirstOrder.Language.Relations.boundedFormula₁ r t).Realize v xs ↔
      FirstOrder.Language.Structure.RelMap r ![t.realize (Sum.elim v xs)] := by
  change FirstOrder.Language.Structure.RelMap r (fun i => (![t] i).realize (Sum.elim v xs)) ↔ _
  refine iff_of_eq (congrArg (FirstOrder.Language.Structure.RelMap r) (funext fun i => ?_))
  fin_cases i; rfl

private lemma realize_bf2 {L : FirstOrder.Language} {α M : Type*} [L.Structure M] {n : ℕ}
    (r : L.Relations 2) (t₁ t₂ : L.Term (α ⊕ Fin n)) (v : α → M) (xs : Fin n → M) :
    (FirstOrder.Language.Relations.boundedFormula₂ r t₁ t₂).Realize v xs ↔
      FirstOrder.Language.Structure.RelMap r ![t₁.realize (Sum.elim v xs), t₂.realize (Sum.elim v xs)] := by
  change FirstOrder.Language.Structure.RelMap r (fun i => (![t₁, t₂] i).realize (Sum.elim v xs)) ↔ _
  refine iff_of_eq (congrArg (FirstOrder.Language.Structure.RelMap r) (funext fun i => ?_))
  fin_cases i <;> rfl

/-! ### Part 1: Hybrid formula helpers & Standard Translation to First-Order Logic -/

private def hTrue {P N : Type} {k : ℕ} : HybridFormula P N k :=
  .neg .bot

private def hAnd {P N : Type} {k : ℕ} (φ ψ : HybridFormula P N k) : HybridFormula P N k :=
  .neg (.or (.neg φ) (.neg ψ))

private def hBigAnd {P N : Type} {k : ℕ} : List (HybridFormula P N k) → HybridFormula P N k
  | [] => hTrue
  | φ :: l => hAnd φ (hBigAnd l)

private def hBigOr {P N : Type} {k : ℕ} : List (HybridFormula P N k) → HybridFormula P N k
  | [] => .bot
  | φ :: l => .or φ (hBigOr l)

private lemma usesFeatures_hTrue {P N : Type} {F : HybridFeatures} {k : ℕ} :
    UsesFeatures F (hTrue (P := P) (N := N) (k := k)) := trivial

private lemma usesFeatures_hAnd {P N : Type} {F : HybridFeatures} {k : ℕ}
    {φ ψ : HybridFormula P N k} (h1 : UsesFeatures F φ) (h2 : UsesFeatures F ψ) :
    UsesFeatures F (hAnd φ ψ) := ⟨h1, h2⟩

private lemma usesFeatures_hBigAnd {P N : Type} {F : HybridFeatures} {k : ℕ}
    {l : List (HybridFormula P N k)} (hl : ∀ φ ∈ l, UsesFeatures F φ) :
    UsesFeatures F (hBigAnd l) := by
  induction l with
  | nil => trivial
  | cons a as ih =>
    exact usesFeatures_hAnd (hl a (List.mem_cons_self ..))
      (ih (fun φ hφ => hl φ (List.mem_cons_of_mem _ hφ)))

private lemma usesFeatures_hBigOr {P N : Type} {F : HybridFeatures} {k : ℕ}
    {l : List (HybridFormula P N k)} (hl : ∀ φ ∈ l, UsesFeatures F φ) :
    UsesFeatures F (hBigOr l) := by
  induction l with
  | nil => trivial
  | cons a as ih =>
    exact ⟨hl a (List.mem_cons_self ..), ih (fun φ hφ => hl φ (List.mem_cons_of_mem _ hφ))⟩

private lemma hybridSat_hTrue {P N M : Type} [(hybridLang P N).Structure M] {k : ℕ}
    (ms : Fin k → M) (m : M) : HybridSat ms m (hTrue (P := P) (N := N)) ↔ True := by
  simp [hTrue, HybridSat]

private lemma hybridSat_hAnd {P N M : Type} [(hybridLang P N).Structure M] {k : ℕ}
    (ms : Fin k → M) (m : M) (φ ψ : HybridFormula P N k) :
    HybridSat ms m (hAnd φ ψ) ↔ HybridSat ms m φ ∧ HybridSat ms m ψ := by
  simp only [hAnd, HybridSat]; tauto

private lemma hybridSat_hBigAnd {P N M : Type} [(hybridLang P N).Structure M] {k : ℕ}
    (ms : Fin k → M) (m : M) (l : List (HybridFormula P N k)) :
    HybridSat ms m (hBigAnd l) ↔ ∀ φ ∈ l, HybridSat ms m φ := by
  induction l with
  | nil => simp [hBigAnd, hybridSat_hTrue]
  | cons a as ih => simp [hBigAnd, hybridSat_hAnd, ih]

private lemma hybridSat_hBigOr {P N M : Type} [(hybridLang P N).Structure M] {k : ℕ}
    (ms : Fin k → M) (m : M) (l : List (HybridFormula P N k)) :
    HybridSat ms m (hBigOr l) ↔ ∃ φ ∈ l, HybridSat ms m φ := by
  induction l with
  | nil => simp [hBigOr, HybridSat]
  | cons a as ih => simp [hBigOr, HybridSat, ih]

private def liftTerm1 {L : FirstOrder.Language} {α : Type*} {n : ℕ} (t : L.Term (α ⊕ Fin n)) :
    L.Term (α ⊕ Fin (n + 1)) :=
  t.relabel (Sum.map id Fin.castSucc)

private lemma realize_liftTerm1 {L : FirstOrder.Language} {α M : Type*} [L.Structure M] {n : ℕ}
    (t : L.Term (α ⊕ Fin n)) (v : α → M) (xs : Fin n → M) (a : M) :
    (liftTerm1 t).realize (Sum.elim v (Fin.snoc xs a)) = t.realize (Sum.elim v xs) := by
  rw [liftTerm1, FirstOrder.Language.Term.realize_relabel]
  congr 1; funext x
  cases x with
  | inl y => rfl
  | inr i => simp [Fin.snoc_castSucc]

private def stdTransAux {P N : Type} :
    ∀ {k n : ℕ},
      (Fin k → (hybridLang P N).Term (Fin 1 ⊕ Fin n)) →
      (hybridLang P N).Term (Fin 1 ⊕ Fin n) →
      HybridFormula P N k → (hybridLang P N).BoundedFormula (Fin 1) n
  | _, _, _, _, .bot => ⊥
  | _, _, _, cur, .prop p =>
      FirstOrder.Language.Relations.boundedFormula₁ (L := hybridLang P N) (r := p) cur
  | _, _, _, cur, .nom s =>
      cur.bdEqual (FirstOrder.Language.Term.func (L := hybridLang P N) (l := 0) s Fin.elim0)
  | _, _, env, cur, .wvar j => cur.bdEqual (env j)
  | _, _, env, cur, .neg φ => (stdTransAux env cur φ).not
  | _, _, env, cur, .or φ ψ => (stdTransAux env cur φ) ⊔ (stdTransAux env cur ψ)
  | _, n, env, cur, .diam φ =>
      (FirstOrder.Language.Relations.boundedFormula₂ (L := hybridLang P N) (r := ())
        (liftTerm1 cur) (FirstOrder.Language.Term.var (Sum.inr (Fin.last n))) ⊓
       stdTransAux (fun j => liftTerm1 (env j))
         (FirstOrder.Language.Term.var (Sum.inr (Fin.last n))) φ).ex
  | _, _, env, cur, .bind j φ => stdTransAux (Function.update env j cur) cur φ
  | _, _, env, cur, .bindExt φ => stdTransAux (Fin.snoc env cur) cur φ
  | _, _, env, _, .jumpVar j φ => stdTransAux env (env j) φ
  | _, _, env, _, .jumpNom s φ =>
      stdTransAux env (FirstOrder.Language.Term.func (L := hybridLang P N) (l := 0) s Fin.elim0) φ
  | _, n, env, cur, .existsVar j φ =>
      (stdTransAux (Function.update (fun i => liftTerm1 (env i)) j
        (FirstOrder.Language.Term.var (Sum.inr (Fin.last n)))) (liftTerm1 cur) φ).ex
  | _, n, env, cur, .existsExt φ =>
      (stdTransAux (Fin.snoc (fun i => liftTerm1 (env i))
        (FirstOrder.Language.Term.var (Sum.inr (Fin.last n)))) (liftTerm1 cur) φ).ex

private lemma realize_stdTransAux {P N M : Type} [(hybridLang P N).Structure M] :
    ∀ {k n : ℕ} (φ : HybridFormula P N k)
      (env : Fin k → (hybridLang P N).Term (Fin 1 ⊕ Fin n))
      (cur : (hybridLang P N).Term (Fin 1 ⊕ Fin n))
      (v : Fin 1 → M) (xs : Fin n → M),
      (stdTransAux env cur φ).Realize v xs ↔
        HybridSat (fun j => (env j).realize (Sum.elim v xs)) (cur.realize (Sum.elim v xs)) φ
  | _, _, .bot, _, _, _, _ => by simp [stdTransAux, HybridSat]
  | _, _, .prop p, _, cur, v, xs => by
      simp only [stdTransAux, HybridSat, propVal]
      exact realize_bf1 (L := hybridLang P N) p cur v xs
  | _, _, .nom s, _, cur, v, xs => by
      simp only [stdTransAux, FirstOrder.Language.BoundedFormula.realize_bdEqual, HybridSat, nomVal]
      change cur.realize (Sum.elim v xs) =
        FirstOrder.Language.Structure.funMap (L := hybridLang P N) (n := 0) s
          (fun i : Fin 0 => FirstOrder.Language.Term.realize (L := hybridLang P N) (Sum.elim v xs) (Fin.elim0 i)) ↔ _
      have : (fun i : Fin 0 => FirstOrder.Language.Term.realize (L := hybridLang P N) (Sum.elim v xs) (Fin.elim0 i)) = Fin.elim0 :=
        funext (fun i => Fin.elim0 i)
      rw [this]
  | _, _, .wvar j, env, cur, v, xs => by simp [stdTransAux, HybridSat]
  | _, _, .neg φ, env, cur, v, xs => by
      simp [stdTransAux, HybridSat, realize_stdTransAux φ]
  | _, _, .or φ ψ, env, cur, v, xs => by
      simp [stdTransAux, HybridSat, realize_stdTransAux φ, realize_stdTransAux ψ]
  | _, n, .diam φ, env, cur, v, xs => by
      simp only [stdTransAux, FirstOrder.Language.BoundedFormula.realize_ex, FirstOrder.Language.BoundedFormula.realize_inf,
        realize_liftTerm1, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last,
        realize_stdTransAux φ, HybridSat, accRel]
      refine exists_congr (fun a => and_congr ?_ Iff.rfl)
      change FirstOrder.Language.Structure.RelMap (L := hybridLang P N) (n := 2) ()
        (fun i => FirstOrder.Language.Term.realize (L := hybridLang P N) (Sum.elim v (Fin.snoc xs a))
          (![liftTerm1 cur, FirstOrder.Language.Term.var (Sum.inr (Fin.last n))] i)) ↔ _
      exact iff_of_eq (congrArg _ (funext (fun i => by fin_cases i <;> simp [realize_liftTerm1])))
  | _, _, .bind j φ, env, cur, v, xs => by
      simp only [stdTransAux, realize_stdTransAux φ, HybridSat]
      have hupd : (fun i => (Function.update env j cur i).realize (Sum.elim v xs)) =
          Function.update (fun i => (env i).realize (Sum.elim v xs)) j (cur.realize (Sum.elim v xs)) := by
        funext i; by_cases h : i = j <;> simp [h]
      rw [hupd]
  | _, _, .bindExt φ, env, cur, v, xs => by
      simp only [stdTransAux, realize_stdTransAux φ, HybridSat]
      have hsn : (fun i => FirstOrder.Language.Term.realize (L := hybridLang P N) (Sum.elim v xs)
          (Fin.snoc (α := fun _ => (hybridLang P N).Term _) env cur i)) =
          Fin.snoc (fun i => (env i).realize (Sum.elim v xs)) (cur.realize (Sum.elim v xs)) := by
        funext i; refine Fin.lastCases ?_ ?_ i <;> simp
      rw [hsn]
  | _, _, .jumpVar j φ, env, cur, v, xs => by
      simp [stdTransAux, HybridSat, realize_stdTransAux φ]
  | _, _, .jumpNom s φ, env, cur, v, xs => by
      simp only [stdTransAux, realize_stdTransAux φ, HybridSat, nomVal]
      change HybridSat (fun j => (env j).realize (Sum.elim v xs))
        (FirstOrder.Language.Structure.funMap (L := hybridLang P N) (n := 0) s
          (fun i : Fin 0 => FirstOrder.Language.Term.realize (L := hybridLang P N) (Sum.elim v xs) (Fin.elim0 i))) φ ↔ _
      have : (fun i : Fin 0 => FirstOrder.Language.Term.realize (L := hybridLang P N) (Sum.elim v xs) (Fin.elim0 i)) = Fin.elim0 :=
        funext (fun i => Fin.elim0 i)
      rw [this]
  | _, n, .existsVar j φ, env, cur, v, xs => by
      simp only [stdTransAux, FirstOrder.Language.BoundedFormula.realize_ex, realize_stdTransAux φ,
        realize_liftTerm1, HybridSat]
      refine exists_congr (fun a => ?_)
      have hupd : (fun i => (Function.update (fun r => liftTerm1 (env r)) j
          (FirstOrder.Language.Term.var (Sum.inr (Fin.last n))) i).realize (Sum.elim v (Fin.snoc xs a))) =
          Function.update (fun i => (env i).realize (Sum.elim v xs)) j a := by
        funext i; by_cases h : i = j <;> simp [h, realize_liftTerm1]
      rw [hupd]
  | _, n, .existsExt φ, env, cur, v, xs => by
      simp only [stdTransAux, FirstOrder.Language.BoundedFormula.realize_ex, realize_stdTransAux φ,
        realize_liftTerm1, HybridSat]
      refine exists_congr (fun a => ?_)
      have hsn : (fun i => FirstOrder.Language.Term.realize (L := hybridLang P N) (Sum.elim v (Fin.snoc xs a))
          (Fin.snoc (α := fun _ => (hybridLang P N).Term _) (fun r => liftTerm1 (env r))
            (FirstOrder.Language.Term.var (Sum.inr (Fin.last n))) i)) =
          Fin.snoc (fun i => (env i).realize (Sum.elim v xs)) a := by
        funext i; refine Fin.lastCases ?_ ?_ i <;> simp [realize_liftTerm1]
      rw [hsn]

private def stdTrans {P N : Type} (ψ : HybridFormula P N 0) :
    (hybridLang P N).Formula (Fin 1) :=
  stdTransAux Fin.elim0 (FirstOrder.Language.Term.var (Sum.inl 0)) ψ

private lemma realize_stdTrans {P N M : Type} [(hybridLang P N).Structure M]
    (ψ : HybridFormula P N 0) (m : M) :
    (stdTrans ψ).Realize ![m] ↔ HybridSat Fin.elim0 m ψ := by
  unfold stdTrans
  change (stdTransAux Fin.elim0 (FirstOrder.Language.Term.var (Sum.inl 0)) ψ).Realize ![m] Fin.elim0 ↔ _
  rw [realize_stdTransAux]
  have hel : (fun j : Fin 0 => FirstOrder.Language.Term.realize (L := hybridLang P N) (Sum.elim ![m] Fin.elim0) (Fin.elim0 j)) = Fin.elim0 :=
    funext (fun j => Fin.elim0 j)
  rw [hel]
  rfl

/-! ### Part 2: Forward direction (invariance of hybrid sentences under `F`-`ω`-bisimulations) -/

private lemma hybridSat_iff_of_bisim {P N M M' : Type}
    [(hybridLang P N).Structure M] [(hybridLang P N).Structure M']
    {F : HybridFeatures}
    {B : ∀ k : ℕ, (Fin k → M) → M → (Fin k → M') → M' → Prop}
    (hB : IsFOmegaBisim (P := P) (N := N) F B) :
    ∀ {k : ℕ} (φ : HybridFormula P N k), UsesFeatures F φ →
      ∀ {ms m ms' m'}, B k ms m ms' m' →
        (HybridSat ms m φ ↔ HybridSat ms' m' φ)
  | _, .bot, _, _, _, _, _, _ => Iff.rfl
  | _, .prop p, _, _, _, _, _, h => hB.prop h p
  | _, .nom s, hF, _, _, _, _, h => hB.nom hF h s
  | _, .wvar j, _, _, _, _, _, h => by
      simp only [HybridSat]; constructor <;> intro heq
      · exact ((hB.wvar h j).mp heq.symm).symm
      · exact ((hB.wvar h j).mpr heq.symm).symm
  | _, .neg φ, hF, _, _, _, _, h =>
      not_congr (hybridSat_iff_of_bisim hB φ hF h)
  | _, .or φ ψ, hF, _, _, _, _, h =>
      or_congr (hybridSat_iff_of_bisim hB φ hF.1 h) (hybridSat_iff_of_bisim hB ψ hF.2 h)
  | _, .diam φ, hF, _, _, _, _, h => by
      constructor
      · rintro ⟨n, hr, hs⟩
        obtain ⟨n', hr', hn'⟩ := hB.forth h n hr
        exact ⟨n', hr', (hybridSat_iff_of_bisim hB φ hF hn').mp hs⟩
      · rintro ⟨n', hr', hs'⟩
        obtain ⟨n, hr, hn⟩ := hB.back h n' hr'
        exact ⟨n, hr, (hybridSat_iff_of_bisim hB φ hF hn).mpr hs'⟩
  | _, .bind j φ, hF, _, _, _, _, h =>
      hybridSat_iff_of_bisim hB φ hF.2 (hB.bind hF.1 h j)
  | _, .bindExt φ, hF, _, _, _, _, h =>
      hybridSat_iff_of_bisim hB φ hF.2 (hB.ext (Or.inl hF.1) h)
  | _, .jumpVar j φ, hF, _, _, _, _, h =>
      hybridSat_iff_of_bisim hB φ hF.2 (hB.atv hF.1 h j)
  | _, .jumpNom s φ, hF, _, _, _, _, h =>
      hybridSat_iff_of_bisim hB φ hF.2.2 (hB.atn hF.1 hF.2.1 h s)
  | _, .existsVar j φ, hF, _, _, _, _, h => by
      constructor
      · rintro ⟨a, ha⟩
        obtain ⟨a', ha'⟩ := hB.ex_forth hF.1 h j a
        exact ⟨a', (hybridSat_iff_of_bisim hB φ hF.2 ha').mp ha⟩
      · rintro ⟨a', ha'⟩
        obtain ⟨a, ha⟩ := hB.ex_back hF.1 h j a'
        exact ⟨a, (hybridSat_iff_of_bisim hB φ hF.2 ha).mpr ha'⟩
  | k, .existsExt φ, hF, ms, m, ms', m', h => by
      have hext := hB.ext (Or.inr hF.1) h
      constructor
      · rintro ⟨a, ha⟩
        obtain ⟨a', ha'⟩ := hB.ex_forth hF.1 hext (Fin.last k) a
        have h1 : Function.update (Fin.snoc (α := fun _ => M) ms m) (Fin.last k) a =
            Fin.snoc (α := fun _ => M) ms a := by
          funext i; refine Fin.lastCases ?_ ?_ i <;> simp
        have h2 : Function.update (Fin.snoc (α := fun _ => M') ms' m') (Fin.last k) a' =
            Fin.snoc (α := fun _ => M') ms' a' := by
          funext i; refine Fin.lastCases ?_ ?_ i <;> simp
        rw [h1, h2] at ha'
        exact ⟨a', (hybridSat_iff_of_bisim hB φ hF.2 ha').mp ha⟩
      · rintro ⟨a', ha'⟩
        obtain ⟨a, ha⟩ := hB.ex_back hF.1 hext (Fin.last k) a'
        have h1 : Function.update (Fin.snoc (α := fun _ => M) ms m) (Fin.last k) a =
            Fin.snoc (α := fun _ => M) ms a := by
          funext i; refine Fin.lastCases ?_ ?_ i <;> simp
        have h2 : Function.update (Fin.snoc (α := fun _ => M') ms' m') (Fin.last k) a' =
            Fin.snoc (α := fun _ => M') ms' a' := by
          funext i; refine Fin.lastCases ?_ ?_ i <;> simp
        rw [h1, h2] at ha
        exact ⟨a, (hybridSat_iff_of_bisim hB φ hF.2 ha).mpr ha'⟩

/-! ### Part 3: Degree, finite canonical basis, and finite `(ω, L)`-bisimulation (`Lemmas 2 & 4`) -/

private def hdeg {P N : Type} : ∀ {k : ℕ}, HybridFormula P N k → ℕ
  | _, .bot => 0
  | _, .prop _ => 0
  | _, .nom _ => 0
  | _, .wvar _ => 0
  | _, .neg φ => hdeg φ
  | _, .or φ ψ => max (hdeg φ) (hdeg ψ)
  | _, .diam φ => hdeg φ + 1
  | _, .bind _ φ => hdeg φ + 1
  | _, .bindExt φ => hdeg φ + 1
  | _, .jumpVar _ φ => hdeg φ
  | _, .jumpNom _ φ => hdeg φ
  | _, .existsVar _ φ => hdeg φ + 1
  | _, .existsExt φ => hdeg φ + 1

private lemma hdeg_hTrue {P N : Type} {k : ℕ} : hdeg (hTrue (P := P) (N := N) (k := k)) = 0 := rfl

private lemma hdeg_hAnd {P N : Type} {k : ℕ} (φ ψ : HybridFormula P N k) :
    hdeg (hAnd φ ψ) = max (hdeg φ) (hdeg ψ) := rfl

private lemma hdeg_hBigAnd_le {P N : Type} {k : ℕ} (l : List (HybridFormula P N k)) (d : ℕ)
    (hl : ∀ φ ∈ l, hdeg φ ≤ d) : hdeg (hBigAnd l) ≤ d := by
  induction l with
  | nil => simp [hBigAnd, hdeg_hTrue]
  | cons a as ih =>
    simp only [hBigAnd, hdeg_hAnd, max_le_iff]
    exact ⟨hl a (List.mem_cons_self ..), ih (fun φ hφ => hl φ (List.mem_cons_of_mem _ hφ))⟩

/-- Given a finite list `L` of formulas, construct the state-description formula for a boolean
assignment `b : List Bool` (or simply from a subset `T` via `L.map`). -/
private def stateDescriptions {P N : Type} {k : ℕ} :
    List (HybridFormula P N k) → List (HybridFormula P N k)
  | [] => [hTrue]
  | φ :: rest =>
      (stateDescriptions rest).map (fun χ => hAnd φ χ) ++
      (stateDescriptions rest).map (fun χ => hAnd (.neg φ) χ)

private lemma stateDescriptions_props {P N : Type} {F : HybridFeatures} {k d : ℕ}
    (L : List (HybridFormula P N k))
    (hL : ∀ ψ ∈ L, UsesFeatures F ψ ∧ hdeg ψ ≤ d) :
    ∀ χ ∈ stateDescriptions L, UsesFeatures F χ ∧ hdeg χ ≤ d := by
  induction L with
  | nil =>
    intro χ hχ
    simp only [stateDescriptions, List.mem_singleton] at hχ
    subst hχ; exact ⟨trivial, Nat.zero_le d⟩
  | cons a as ih =>
    have ha := hL a (List.mem_cons_self ..)
    have has := ih (fun ψ hψ => hL ψ (List.mem_cons_of_mem _ hψ))
    intro χ hχ
    simp only [stateDescriptions, List.mem_append, List.mem_map] at hχ
    rcases hχ with ⟨ψ, hψ, rfl⟩ | ⟨ψ, hψ, rfl⟩
    · exact ⟨usesFeatures_hAnd ha.1 (has ψ hψ).1, max_le ha.2 (has ψ hψ).2⟩
    · exact ⟨usesFeatures_hAnd ha.1 (has ψ hψ).1, max_le ha.2 (has ψ hψ).2⟩

private lemma exists_stateDescription {P N M : Type} [(hybridLang P N).Structure M] {k : ℕ}
    (L : List (HybridFormula P N k)) (ms : Fin k → M) (m : M) :
    ∃ χ ∈ stateDescriptions L, HybridSat ms m χ ∧
      ∀ {M' : Type} [(hybridLang P N).Structure M'] (ms' : Fin k → M') (m' : M'),
        HybridSat ms' m' χ → ∀ ψ ∈ L, HybridSat ms m ψ ↔ HybridSat ms' m' ψ := by
  induction L with
  | nil =>
    refine ⟨hTrue, by simp [stateDescriptions], by simp [hybridSat_hTrue], ?_⟩
    intro _ _ _ _ _ ψ hψ; simp at hψ
  | cons a as ih =>
    obtain ⟨χ, hχ_mem, hχ_sat, hχ_iff⟩ := ih
    by_cases ha : HybridSat ms m a
    · refine ⟨hAnd a χ, ?_, (hybridSat_hAnd ms m a χ).mpr ⟨ha, hχ_sat⟩, ?_⟩
      · simp only [stateDescriptions, List.mem_append, List.mem_map]
        exact Or.inl ⟨χ, hχ_mem, rfl⟩
      · intro M' _ ms' m' hsat' ψ hψ
        rw [hybridSat_hAnd] at hsat'
        simp only [List.mem_cons] at hψ
        rcases hψ with rfl | hψ'
        · exact ⟨fun _ => hsat'.1, fun _ => ha⟩
        · exact hχ_iff ms' m' hsat'.2 ψ hψ'
    · refine ⟨hAnd (.neg a) χ, ?_, (hybridSat_hAnd ms m (.neg a) χ).mpr ⟨ha, hχ_sat⟩, ?_⟩
      · simp only [stateDescriptions, List.mem_append, List.mem_map]
        exact Or.inr ⟨χ, hχ_mem, rfl⟩
      · intro M' _ ms' m' hsat' ψ hψ
        rw [hybridSat_hAnd] at hsat'
        simp only [List.mem_cons] at hψ
        rcases hψ with rfl | hψ'
        · exact ⟨fun h => absurd h ha, fun h => absurd h hsat'.1⟩
        · exact hχ_iff ms' m' hsat'.2 ψ hψ'

/-- Wrap a finite list of formulas with all `@_{x_j}` and `@_s` prefixes allowed by `F`. -/
private noncomputable def wrapJump {P N : Type} [Fintype N] (F : HybridFeatures) {k : ℕ}
    (L : List (HybridFormula P N k)) : List (HybridFormula P N k) :=
  L ++
  (if F.hasJump then (List.finRange k).flatMap (fun j => L.map (HybridFormula.jumpVar j)) else []) ++
  (if F.hasJump ∧ F.hasNom then
    (Finset.univ.toList : List N).flatMap (fun s => L.map (HybridFormula.jumpNom s)) else [])

private lemma wrapJump_props {P N : Type} [Fintype N] {F : HybridFeatures} {k d : ℕ}
    (L : List (HybridFormula P N k))
    (hL : ∀ ψ ∈ L, UsesFeatures F ψ ∧ hdeg ψ ≤ d) :
    ∀ ψ ∈ wrapJump F L, UsesFeatures F ψ ∧ hdeg ψ ≤ d := by
  intro ψ hψ
  simp only [wrapJump, List.mem_append] at hψ
  rcases hψ with (h1 | h2) | h3
  · exact hL ψ h1
  · split_ifs at h2 with hj
    · simp only [List.mem_flatMap, List.mem_map] at h2
      rcases h2 with ⟨j, _, φ, hφ, rfl⟩
      exact ⟨⟨hj, (hL φ hφ).1⟩, (hL φ hφ).2⟩
    · simp at h2
  · split_ifs at h3 with hjn
    · simp only [List.mem_flatMap, List.mem_map] at h3
      rcases h3 with ⟨s, _, φ, hφ, rfl⟩
      exact ⟨⟨hjn.1, hjn.2, (hL φ hφ).1⟩, (hL φ hφ).2⟩
    · simp at h3

/-- Finite canonical basis of `F`-formulas of degree `≤ d` with `k` world variables. -/
private noncomputable def basisFormulas {P N : Type} [Fintype P] [Fintype N]
    (F : HybridFeatures) : ℕ → (k : ℕ) → List (HybridFormula P N k)
  | 0, k =>
      let atoms : List (HybridFormula P N k) :=
        (Finset.univ.toList : List P).map HybridFormula.prop ++
        (if F.hasNom then (Finset.univ.toList : List N).map HybridFormula.nom else []) ++
        (List.finRange k).map HybridFormula.wvar
      wrapJump F atoms
  | d + 1, k =>
      let prev := basisFormulas F d k
      let prevExt := basisFormulas F d (k + 1)
      let states := stateDescriptions prev
      let statesExt := stateDescriptions prevExt
      let step : List (HybridFormula P N k) :=
        prev ++
        states.map HybridFormula.diam ++
        (if F.hasBind then
          (List.finRange k).flatMap (fun j => prev.map (HybridFormula.bind j)) ++
          prevExt.map HybridFormula.bindExt
        else []) ++
        (if F.hasExists then
          (List.finRange k).flatMap (fun j => states.map (HybridFormula.existsVar j)) ++
          statesExt.map HybridFormula.existsExt
        else [])
      wrapJump F step

private lemma basisFormulas_props {P N : Type} [Fintype P] [Fintype N]
    (F : HybridFeatures) :
    ∀ (d k : ℕ) (ψ : HybridFormula P N k), ψ ∈ basisFormulas F d k →
      UsesFeatures F ψ ∧ hdeg ψ ≤ d
  | 0, k => by
      refine wrapJump_props _ (fun ψ hψ => ?_)
      simp only [List.mem_append, List.mem_map] at hψ
      rcases hψ with (⟨p, _, rfl⟩ | hnom) | ⟨j, _, rfl⟩
      · exact ⟨trivial, le_refl 0⟩
      · split_ifs at hnom with hn
        · simp only [List.mem_map] at hnom
          rcases hnom with ⟨s, _, rfl⟩
          exact ⟨hn, le_refl 0⟩
        · simp at hnom
      · exact ⟨trivial, le_refl 0⟩
  | d + 1, k => by
      have ihk := basisFormulas_props (P := P) (N := N) F d k
      have ihk1 := basisFormulas_props (P := P) (N := N) F d (k + 1)
      have hst := stateDescriptions_props (basisFormulas (P := P) (N := N) F d k) ihk
      have hst1 := stateDescriptions_props (basisFormulas (P := P) (N := N) F d (k + 1)) ihk1
      refine wrapJump_props _ (fun ψ hψ => ?_)
      simp only [List.mem_append] at hψ
      rcases hψ with ((hprev | hdiam) | hbind) | hex
      · exact ⟨(ihk ψ hprev).1, Nat.le_succ_of_le (ihk ψ hprev).2⟩
      · simp only [List.mem_map] at hdiam
        rcases hdiam with ⟨χ, hχ, rfl⟩
        exact ⟨(hst χ hχ).1, Nat.succ_le_succ (hst χ hχ).2⟩
      · split_ifs at hbind with hb
        · simp only [List.mem_append, List.mem_flatMap, List.mem_map] at hbind
          rcases hbind with ⟨j, _, φ, hφ, rfl⟩ | ⟨φ, hφ, rfl⟩
          · exact ⟨⟨hb, (ihk φ hφ).1⟩, Nat.succ_le_succ (ihk φ hφ).2⟩
          · exact ⟨⟨hb, (ihk1 φ hφ).1⟩, Nat.succ_le_succ (ihk1 φ hφ).2⟩
        · simp at hbind
      · split_ifs at hex with he
        · simp only [List.mem_append, List.mem_flatMap, List.mem_map] at hex
          rcases hex with ⟨j, _, χ, hχ, rfl⟩ | ⟨χ, hχ, rfl⟩
          · exact ⟨⟨he, (hst χ hχ).1⟩, Nat.succ_le_succ (hst χ hχ).2⟩
          · exact ⟨⟨he, (hst1 χ hχ).1⟩, Nat.succ_le_succ (hst1 χ hχ).2⟩
        · simp at hex

private lemma mem_wrapJump_self {P N : Type} [Fintype N] {F : HybridFeatures} {k : ℕ}
    {L : List (HybridFormula P N k)} {ψ : HybridFormula P N k} (h : ψ ∈ L) :
    ψ ∈ wrapJump F L := by
  simp only [wrapJump, List.mem_append]; exact Or.inl (Or.inl h)

private lemma mem_wrapJump_jumpVar {P N : Type} [Fintype N] {F : HybridFeatures} {k : ℕ}
    {L : List (HybridFormula P N k)} {ψ : HybridFormula P N k} (hF : F.hasJump = true)
    (j : Fin k) (h : ψ ∈ L) :
    .jumpVar j ψ ∈ wrapJump F L := by
  simp only [wrapJump, List.mem_append, if_pos hF, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inr ⟨j, List.mem_finRange j, ψ, h, rfl⟩)

private lemma mem_wrapJump_jumpNom {P N : Type} [Fintype N] {F : HybridFeatures} {k : ℕ}
    {L : List (HybridFormula P N k)} {ψ : HybridFormula P N k}
    (hJ : F.hasJump = true) (hN : F.hasNom = true) (s : N) (h : ψ ∈ L) :
    .jumpNom s ψ ∈ wrapJump F L := by
  simp only [wrapJump, List.mem_append, if_pos (And.intro hJ hN), List.mem_flatMap, List.mem_map]
  exact Or.inr ⟨s, Finset.mem_toList.mpr (Finset.mem_univ s), ψ, h, rfl⟩

/-- Agreement on `basisFormulas F d k` implies agreement on ALL `F`-formulas of degree `≤ d`. -/
private lemma agree_all_of_agree_basis {P N : Type} [Fintype P] [Fintype N]
    {F : HybridFeatures} {M M' : Type} [(hybridLang P N).Structure M]
    [(hybridLang P N).Structure M'] :
    ∀ {d k : ℕ} (φ : HybridFormula P N k), UsesFeatures F φ → hdeg φ ≤ d →
      ∀ (ms : Fin k → M) (m : M) (ms' : Fin k → M') (m' : M'),
        (∀ ψ ∈ basisFormulas (P := P) (N := N) F d k, HybridSat ms m ψ ↔ HybridSat ms' m' ψ) →
        (HybridSat ms m φ ↔ HybridSat ms' m' φ) := by
  intro d
  induction d with
  | zero =>
    intro k φ₀ hF₀ hdeg₀ ms m ms' m' hbase
    let atoms : List (HybridFormula P N k) :=
      (Finset.univ.toList : List P).map HybridFormula.prop ++
      (if F.hasNom then (Finset.univ.toList : List N).map HybridFormula.nom else []) ++
      (List.finRange k).map HybridFormula.wvar
    let rec go : ∀ (φ : HybridFormula P N k), UsesFeatures F φ → hdeg φ ≤ 0 →
        ∀ (w : M) (w' : M'),
          (∀ ψ ∈ atoms, HybridSat ms w ψ ↔ HybridSat ms' w' ψ) →
          (HybridSat ms w φ ↔ HybridSat ms' w' φ)
      | .bot, _, _, _, _, _ => Iff.rfl
      | .prop p, _, _, w, w', ha => ha (.prop p) (by simp [atoms])
      | .nom s, hFn, _, w, w', ha => by
          have hFn' : F.hasNom = true := hFn
          exact ha (.nom s) (by simp [atoms, hFn'])
      | .wvar j, _, _, w, w', ha => ha (.wvar j) (by simp [atoms])
      | .neg φ, hF, hd, w, w', ha => not_congr (go φ hF hd w w' ha)
      | .or φ ψ, hF, hd, w, w', ha => by
          simp only [hdeg, max_le_iff] at hd
          exact or_congr (go φ hF.1 hd.1 w w' ha) (go ψ hF.2 hd.2 w w' ha)
      | .diam _, _, hd, _, _, _ => by simp [hdeg] at hd
      | .bind _ _, _, hd, _, _, _ => by simp [hdeg] at hd
      | .bindExt _, _, hd, _, _, _ => by simp [hdeg] at hd
      | .existsVar _ _, _, hd, _, _, _ => by simp [hdeg] at hd
      | .existsExt _, _, hd, _, _, _ => by simp [hdeg] at hd
      | .jumpVar j φ, hF, hd, _, _, _ =>
          go φ hF.2 hd (ms j) (ms' j) (fun ψ hψ =>
            hbase (.jumpVar j ψ) (mem_wrapJump_jumpVar hF.1 j hψ))
      | .jumpNom s φ, hF, hd, _, _, _ =>
          go φ hF.2.2 hd (nomVal (P := P) (N := N) s) (nomVal (P := P) (N := N) s) (fun ψ hψ =>
            hbase (.jumpNom s ψ) (mem_wrapJump_jumpNom hF.1 hF.2.1 s hψ))
    exact go φ₀ hF₀ hdeg₀ m m' (fun ψ hψ => hbase ψ (mem_wrapJump_self hψ))
  | succ d ih =>
    intro k φ₀ hF₀ hdegS ms m ms' m' hbase
    set prev := basisFormulas (P := P) (N := N) F d k
    set prevExt := basisFormulas (P := P) (N := N) F d (k + 1)
    set states := stateDescriptions prev
    set statesExt := stateDescriptions prevExt
    set step : List (HybridFormula P N k) :=
      prev ++
      states.map HybridFormula.diam ++
      (if F.hasBind then
        (List.finRange k).flatMap (fun j => prev.map (HybridFormula.bind j)) ++
        prevExt.map HybridFormula.bindExt
      else []) ++
      (if F.hasExists then
        (List.finRange k).flatMap (fun j => states.map (HybridFormula.existsVar j)) ++
        statesExt.map HybridFormula.existsExt
      else [])
    have hprev_step : ∀ ψ ∈ prev, ψ ∈ step := fun ψ hψ => by
      simp only [step, List.mem_append]; exact Or.inl (Or.inl (Or.inl hψ))
    let rec goS : ∀ (φ : HybridFormula P N k), UsesFeatures F φ → hdeg φ ≤ d + 1 →
        ∀ (w : M) (w' : M'),
          (∀ ψ ∈ step, HybridSat ms w ψ ↔ HybridSat ms' w' ψ) →
          (HybridSat ms w φ ↔ HybridSat ms' w' φ)
      | .bot, _, _, _, _, _ => Iff.rfl
      | .prop p, hF, _, w, w', hst =>
          ih (.prop p) hF (Nat.zero_le d) ms w ms' w'
            (fun ψ hψ => hst ψ (hprev_step ψ hψ))
      | .nom s, hFn, _, w, w', hst =>
          ih (.nom s) hFn (Nat.zero_le d) ms w ms' w' (fun ψ hψ => hst ψ (hprev_step ψ hψ))
      | .wvar j, hF, _, w, w', hst =>
          ih (.wvar j) hF (Nat.zero_le d) ms w ms' w'
            (fun ψ hψ => hst ψ (hprev_step ψ hψ))
      | .neg φ, hF, hd, w, w', hst => not_congr (goS φ hF hd w w' hst)
      | .or φ ψ, hF, hd, w, w', hst => by
          simp only [hdeg, max_le_iff] at hd
          exact or_congr (goS φ hF.1 hd.1 w w' hst) (goS ψ hF.2 hd.2 w w' hst)
      | .diam φ, hF, hd, w, w', hst => by
          simp only [hdeg] at hd
          have hd' : hdeg φ ≤ d := Nat.le_of_succ_le_succ hd
          constructor
          · rintro ⟨n, hr, hs⟩
            obtain ⟨χ, hχ_mem, hχ_sat, hχ_iff⟩ := exists_stateDescription prev ms n
            have hdiam_mem : HybridFormula.diam χ ∈ step := by
              simp only [step, List.mem_append, List.mem_map]
              exact Or.inl (Or.inl (Or.inr ⟨χ, hχ_mem, rfl⟩))
            have hd_sat : HybridSat ms w (.diam χ) := ⟨n, hr, hχ_sat⟩
            obtain ⟨n', hr', hχ_sat'⟩ := (hst (.diam χ) hdiam_mem).mp hd_sat
            exact ⟨n', hr', (ih φ hF hd' ms n ms' n' (hχ_iff ms' n' hχ_sat')).mp hs⟩
          · rintro ⟨n', hr', hs'⟩
            obtain ⟨χ, hχ_mem, hχ_sat', hχ_iff'⟩ := exists_stateDescription prev ms' n'
            have hdiam_mem : HybridFormula.diam χ ∈ step := by
              simp only [step, List.mem_append, List.mem_map]
              exact Or.inl (Or.inl (Or.inr ⟨χ, hχ_mem, rfl⟩))
            have hd_sat' : HybridSat ms' w' (.diam χ) := ⟨n', hr', hχ_sat'⟩
            obtain ⟨n, hr, hχ_sat⟩ := (hst (.diam χ) hdiam_mem).mpr hd_sat'
            exact ⟨n, hr, (ih φ hF hd' ms n ms' n' (fun ψ hψ => (hχ_iff' ms n hχ_sat ψ hψ).symm)).mpr hs'⟩
      | .bind j φ, hF, hd, w, w', hst => by
          simp only [hdeg] at hd
          have hd' : hdeg φ ≤ d := Nat.le_of_succ_le_succ hd
          exact ih φ hF.2 hd' (Function.update ms j w) w (Function.update ms' j w') w' (fun ψ hψ => by
            have hmem : HybridFormula.bind j ψ ∈ step := by
              simp only [step, List.mem_append, if_pos hF.1, List.mem_flatMap, List.mem_map]
              exact Or.inl (Or.inr (Or.inl ⟨j, List.mem_finRange j, ψ, hψ, rfl⟩))
            exact hst (.bind j ψ) hmem)
      | .bindExt φ, hF, hd, w, w', hst => by
          simp only [hdeg] at hd
          have hd' : hdeg φ ≤ d := Nat.le_of_succ_le_succ hd
          exact ih φ hF.2 hd' (Fin.snoc ms w) w (Fin.snoc ms' w') w' (fun ψ hψ => by
            have hmem : HybridFormula.bindExt ψ ∈ step := by
              simp only [step, List.mem_append, if_pos hF.1, List.mem_map]
              exact Or.inl (Or.inr (Or.inr ⟨ψ, hψ, rfl⟩))
            exact hst (.bindExt ψ) hmem)
      | .jumpVar j φ, hF, hd, _, _, _ =>
          goS φ hF.2 hd (ms j) (ms' j) (fun ψ hψ =>
            hbase (.jumpVar j ψ) (mem_wrapJump_jumpVar hF.1 j hψ))
      | .jumpNom s φ, hF, hd, _, _, _ =>
          goS φ hF.2.2 hd (nomVal (P := P) (N := N) s) (nomVal (P := P) (N := N) s) (fun ψ hψ =>
            hbase (.jumpNom s ψ) (mem_wrapJump_jumpNom hF.1 hF.2.1 s hψ))
      | .existsVar j φ, hF, hd, w, w', hst => by
          simp only [hdeg] at hd
          have hd' : hdeg φ ≤ d := Nat.le_of_succ_le_succ hd
          constructor
          · rintro ⟨a, ha⟩
            obtain ⟨χ, hχ_mem, hχ_sat, hχ_iff⟩ :=
              exists_stateDescription prev (Function.update ms j a) w
            have hex_mem : HybridFormula.existsVar j χ ∈ step := by
              simp only [step, List.mem_append, if_pos hF.1, List.mem_flatMap, List.mem_map]
              exact Or.inr (Or.inl ⟨j, List.mem_finRange j, χ, hχ_mem, rfl⟩)
            obtain ⟨a', hχ_sat'⟩ := (hst (.existsVar j χ) hex_mem).mp ⟨a, hχ_sat⟩
            exact ⟨a', (ih φ hF.2 hd' _ w _ w' (hχ_iff _ w' hχ_sat')).mp ha⟩
          · rintro ⟨a', ha'⟩
            obtain ⟨χ, hχ_mem, hχ_sat', hχ_iff'⟩ :=
              exists_stateDescription prev (Function.update ms' j a') w'
            have hex_mem : HybridFormula.existsVar j χ ∈ step := by
              simp only [step, List.mem_append, if_pos hF.1, List.mem_flatMap, List.mem_map]
              exact Or.inr (Or.inl ⟨j, List.mem_finRange j, χ, hχ_mem, rfl⟩)
            obtain ⟨a, hχ_sat⟩ := (hst (.existsVar j χ) hex_mem).mpr ⟨a', hχ_sat'⟩
            exact ⟨a, (ih φ hF.2 hd' _ w _ w' (fun ψ hψ => (hχ_iff' _ w hχ_sat ψ hψ).symm)).mpr ha'⟩
      | .existsExt φ, hF, hd, w, w', hst => by
          simp only [hdeg] at hd
          have hd' : hdeg φ ≤ d := Nat.le_of_succ_le_succ hd
          constructor
          · rintro ⟨a, ha⟩
            obtain ⟨χ, hχ_mem, hχ_sat, hχ_iff⟩ :=
              exists_stateDescription prevExt (Fin.snoc ms a) w
            have hex_mem : HybridFormula.existsExt χ ∈ step := by
              simp only [step, List.mem_append, if_pos hF.1, List.mem_map]
              exact Or.inr (Or.inr ⟨χ, hχ_mem, rfl⟩)
            obtain ⟨a', hχ_sat'⟩ := (hst (.existsExt χ) hex_mem).mp ⟨a, hχ_sat⟩
            exact ⟨a', (ih φ hF.2 hd' _ w _ w' (hχ_iff _ w' hχ_sat')).mp ha⟩
          · rintro ⟨a', ha'⟩
            obtain ⟨χ, hχ_mem, hχ_sat', hχ_iff'⟩ :=
              exists_stateDescription prevExt (Fin.snoc ms' a') w'
            have hex_mem : HybridFormula.existsExt χ ∈ step := by
              simp only [step, List.mem_append, if_pos hF.1, List.mem_map]
              exact Or.inr (Or.inr ⟨χ, hχ_mem, rfl⟩)
            obtain ⟨a, hχ_sat⟩ := (hst (.existsExt χ) hex_mem).mpr ⟨a', hχ_sat'⟩
            exact ⟨a, (ih φ hF.2 hd' _ w _ w' (fun ψ hψ => (hχ_iff' _ w hχ_sat ψ hψ).symm)).mpr ha'⟩
    exact goS φ₀ hF₀ hdegS m m' (fun ψ hψ => hbase ψ (mem_wrapJump_self hψ))

/-- Hybrid `F`-equivalence up to degree `d` on `k` world variables. -/
private def hTypeEq {P N M M' : Type} [(hybridLang P N).Structure M]
    [(hybridLang P N).Structure M'] (F : HybridFeatures) (d k : ℕ)
    (ms : Fin k → M) (m : M) (ms' : Fin k → M') (m' : M') : Prop :=
  ∀ φ : HybridFormula P N k, UsesFeatures F φ → hdeg φ ≤ d →
    (HybridSat ms m φ ↔ HybridSat ms' m' φ)

private lemma hTypeEq_mono {P N M M' : Type} [(hybridLang P N).Structure M]
    [(hybridLang P N).Structure M'] {F : HybridFeatures} {d₁ d₂ k : ℕ} (hle : d₁ ≤ d₂)
    {ms : Fin k → M} {m : M} {ms' : Fin k → M'} {m' : M'}
    (h : hTypeEq (P := P) (N := N) F d₂ k ms m ms' m') : hTypeEq (P := P) (N := N) F d₁ k ms m ms' m' :=
  fun φ hF hd => h φ hF (hd.trans hle)

private lemma hTypeEq_forth {P N M M' : Type} [Fintype P] [Fintype N]
    [(hybridLang P N).Structure M] [(hybridLang P N).Structure M']
    {F : HybridFeatures} {d k : ℕ} {ms : Fin k → M} {m : M} {ms' : Fin k → M'} {m' : M'}
    (h : hTypeEq (P := P) (N := N) F (d + 1) k ms m ms' m') (n : M) (hr : accRel (P := P) (N := N) m n) :
    ∃ n' : M', accRel (P := P) (N := N) m' n' ∧ hTypeEq (P := P) (N := N) F d k ms n ms' n' := by
  obtain ⟨χ, hχ_mem, hχ_sat, hχ_iff⟩ := exists_stateDescription (basisFormulas (P := P) (N := N) F d k) ms n
  have hχ_p := stateDescriptions_props (basisFormulas (P := P) (N := N) F d k) (basisFormulas_props (P := P) (N := N) F d k) χ hχ_mem
  have hdiam : HybridSat ms' m' (.diam χ) :=
    (h (.diam χ) hχ_p.1 (Nat.succ_le_succ hχ_p.2)).mp ⟨n, hr, hχ_sat⟩
  obtain ⟨n', hr', hχ_sat'⟩ := hdiam
  refine ⟨n', hr', fun φ hF hd =>
    agree_all_of_agree_basis φ hF hd ms n ms' n' (hχ_iff ms' n' hχ_sat')⟩

private lemma hTypeEq_back {P N M M' : Type} [Fintype P] [Fintype N]
    [(hybridLang P N).Structure M] [(hybridLang P N).Structure M']
    {F : HybridFeatures} {d k : ℕ} {ms : Fin k → M} {m : M} {ms' : Fin k → M'} {m' : M'}
    (h : hTypeEq (P := P) (N := N) F (d + 1) k ms m ms' m') (n' : M') (hr' : accRel (P := P) (N := N) m' n') :
    ∃ n : M, accRel (P := P) (N := N) m n ∧ hTypeEq (P := P) (N := N) F d k ms n ms' n' := by
  obtain ⟨χ, hχ_mem, hχ_sat', hχ_iff'⟩ := exists_stateDescription (basisFormulas (P := P) (N := N) F d k) ms' n'
  have hχ_p := stateDescriptions_props (basisFormulas (P := P) (N := N) F d k) (basisFormulas_props (P := P) (N := N) F d k) χ hχ_mem
  have hdiam : HybridSat ms m (.diam χ) :=
    (h (.diam χ) hχ_p.1 (Nat.succ_le_succ hχ_p.2)).mpr ⟨n', hr', hχ_sat'⟩
  obtain ⟨n, hr, hχ_sat⟩ := hdiam
  refine ⟨n, hr, fun φ hF hd =>
    agree_all_of_agree_basis φ hF hd ms n ms' n' (fun ψ hψ => (hχ_iff' ms n hχ_sat ψ hψ).symm)⟩

private lemma hTypeEq_ext {P N M M' : Type}
    [(hybridLang P N).Structure M] [(hybridLang P N).Structure M']
    {F : HybridFeatures} (hBE : F.hasBind = true ∨ F.hasExists = true)
    {d k : ℕ} {ms : Fin k → M} {m : M} {ms' : Fin k → M'} {m' : M'}
    (h : hTypeEq (P := P) (N := N) F (d + 1) k ms m ms' m') :
    hTypeEq (P := P) (N := N) F d (k + 1) (Fin.snoc ms m) m (Fin.snoc ms' m') m' := by
  intro φ hF hd
  rcases hBE with hb | he
  · exact h (.bindExt φ) ⟨hb, hF⟩ (Nat.succ_le_succ hd)
  · have heq1 : HybridSat (Fin.snoc ms m) m φ ↔
        HybridSat ms m (.existsExt (hAnd (.wvar (Fin.last k)) φ)) := by
      simp only [HybridSat, hybridSat_hAnd, Fin.snoc_last]
      constructor
      · intro hsat; exact ⟨m, rfl, hsat⟩
      · rintro ⟨a, rfl, hsat⟩; exact hsat
    have heq2 : HybridSat (Fin.snoc ms' m') m' φ ↔
        HybridSat ms' m' (.existsExt (hAnd (.wvar (Fin.last k)) φ)) := by
      simp only [HybridSat, hybridSat_hAnd, Fin.snoc_last]
      constructor
      · intro hsat; exact ⟨m', rfl, hsat⟩
      · rintro ⟨a', rfl, hsat⟩; exact hsat
    rw [heq1, heq2]
    exact h _ ⟨he, usesFeatures_hAnd trivial hF⟩
      (Nat.succ_le_succ (max_le (Nat.zero_le d) hd))

private lemma hTypeEq_bind {P N M M' : Type}
    [(hybridLang P N).Structure M] [(hybridLang P N).Structure M']
    {F : HybridFeatures} (hb : F.hasBind = true)
    {d k : ℕ} {ms : Fin k → M} {m : M} {ms' : Fin k → M'} {m' : M'}
    (h : hTypeEq (P := P) (N := N) F (d + 1) k ms m ms' m') (j : Fin k) :
    hTypeEq (P := P) (N := N) F d k (Function.update ms j m) m (Function.update ms' j m') m' :=
  fun φ hF hd => h (.bind j φ) ⟨hb, hF⟩ (Nat.succ_le_succ hd)

private lemma hTypeEq_atv {P N M M' : Type}
    [(hybridLang P N).Structure M] [(hybridLang P N).Structure M']
    {F : HybridFeatures} (hj : F.hasJump = true)
    {d k : ℕ} {ms : Fin k → M} {m : M} {ms' : Fin k → M'} {m' : M'}
    (h : hTypeEq (P := P) (N := N) F d k ms m ms' m') (j : Fin k) :
    hTypeEq (P := P) (N := N) F d k ms (ms j) ms' (ms' j) :=
  fun φ hF hd => h (.jumpVar j φ) ⟨hj, hF⟩ hd

private lemma hTypeEq_atn {P N M M' : Type}
    [(hybridLang P N).Structure M] [(hybridLang P N).Structure M']
    {F : HybridFeatures} (hj : F.hasJump = true) (hn : F.hasNom = true)
    {d k : ℕ} {ms : Fin k → M} {m : M} {ms' : Fin k → M'} {m' : M'}
    (h : hTypeEq (P := P) (N := N) F d k ms m ms' m') (s : N) :
    hTypeEq (P := P) (N := N) F d k ms (nomVal (P := P) (N := N) s) ms' (nomVal (P := P) (N := N) s) :=
  fun φ hF hd => h (.jumpNom s φ) ⟨hj, hn, hF⟩ hd

private lemma hTypeEq_ex_forth {P N M M' : Type} [Fintype P] [Fintype N]
    [(hybridLang P N).Structure M] [(hybridLang P N).Structure M']
    {F : HybridFeatures} (he : F.hasExists = true)
    {d k : ℕ} {ms : Fin k → M} {m : M} {ms' : Fin k → M'} {m' : M'}
    (h : hTypeEq (P := P) (N := N) F (d + 1) k ms m ms' m') (j : Fin k) (a : M) :
    ∃ a' : M', hTypeEq (P := P) (N := N) F d k (Function.update ms j a) m (Function.update ms' j a') m' := by
  obtain ⟨χ, hχ_mem, hχ_sat, hχ_iff⟩ :=
    exists_stateDescription (basisFormulas (P := P) (N := N) F d k) (Function.update ms j a) m
  have hχ_p := stateDescriptions_props (basisFormulas (P := P) (N := N) F d k) (basisFormulas_props (P := P) (N := N) F d k) χ hχ_mem
  have hex : HybridSat ms' m' (.existsVar j χ) :=
    (h (.existsVar j χ) ⟨he, hχ_p.1⟩ (Nat.succ_le_succ hχ_p.2)).mp ⟨a, hχ_sat⟩
  obtain ⟨a', hχ_sat'⟩ := hex
  exact ⟨a', fun φ hF hd =>
    agree_all_of_agree_basis φ hF hd _ m _ m' (hχ_iff _ m' hχ_sat')⟩

private lemma hTypeEq_ex_back {P N M M' : Type} [Fintype P] [Fintype N]
    [(hybridLang P N).Structure M] [(hybridLang P N).Structure M']
    {F : HybridFeatures} (he : F.hasExists = true)
    {d k : ℕ} {ms : Fin k → M} {m : M} {ms' : Fin k → M'} {m' : M'}
    (h : hTypeEq (P := P) (N := N) F (d + 1) k ms m ms' m') (j : Fin k) (a' : M') :
    ∃ a : M, hTypeEq (P := P) (N := N) F d k (Function.update ms j a) m (Function.update ms' j a') m' := by
  obtain ⟨χ, hχ_mem, hχ_sat', hχ_iff'⟩ :=
    exists_stateDescription (basisFormulas (P := P) (N := N) F d k) (Function.update ms' j a') m'
  have hχ_p := stateDescriptions_props (basisFormulas (P := P) (N := N) F d k) (basisFormulas_props (P := P) (N := N) F d k) χ hχ_mem
  have hex : HybridSat ms m (.existsVar j χ) :=
    (h (.existsVar j χ) ⟨he, hχ_p.1⟩ (Nat.succ_le_succ hχ_p.2)).mpr ⟨a', hχ_sat'⟩
  obtain ⟨a, hχ_sat⟩ := hex
  exact ⟨a, fun φ hF hd =>
    agree_all_of_agree_basis φ hF hd _ m _ m' (fun ψ hψ => (hχ_iff' _ m hχ_sat ψ hψ).symm)⟩

/-! ### Part 4: Lindström-type compactness theorem (`Theorem 1` of arXiv:2312.14661) -/

/-- Expanded first-order language encoding two disjoint universes `U₁, U₂`, two copies of
`P, N, R`, and a family of `(2k+2)`-ary bisimulation predicates `I_ℓ^k` (`ℓ, k ∈ ℕ`). -/
private def extLang (P N : Type) : FirstOrder.Language.{0, 0} where
  Functions
    | 0 => N ⊕ N
    | _ + 1 => PEmpty
  Relations
    | 0 => PEmpty
    | 1 => (Unit ⊕ Unit) ⊕ (P ⊕ P)
    | 2 => (Unit ⊕ Unit) ⊕ ℕ
    | n + 3 => if n % 2 = 1 then ℕ else PEmpty

private def uPred {P N : Type} (side : Bool) : (extLang P N).Relations 1 :=
  Sum.inl (if side then Sum.inr () else Sum.inl ())

private def pPred {P N : Type} (side : Bool) (p : P) : (extLang P N).Relations 1 :=
  Sum.inr (if side then Sum.inr p else Sum.inl p)

private def rPred {P N : Type} (side : Bool) : (extLang P N).Relations 2 :=
  Sum.inl (if side then Sum.inr () else Sum.inl ())

private def nomConst {P N : Type} (side : Bool) (s : N) : (extLang P N).Functions 0 :=
  if side then Sum.inr s else Sum.inl s

private def iPred {P N : Type} (k ℓ : ℕ) : (extLang P N).Relations (2 * (k + 1)) :=
  match k with
  | 0 => Sum.inr ℓ
  | k' + 1 =>
    have hmod : (2 * k' + 1) % 2 = 1 := by omega
    have h1 : ℕ = if (2 * k' + 1) % 2 = 1 then ℕ else PEmpty := by simp [hmod]
    have h2 : (if (2 * k' + 1) % 2 = 1 then ℕ else PEmpty) =
        (extLang P N).Relations (2 * (k' + 1 + 1)) := by
      have heq : 2 * (k' + 1 + 1) = (2 * k' + 1) + 3 := by omega
      rw [heq]; rfl
    cast h2 (cast h1 ℓ)

private lemma iPred_zero {P N : Type} (ℓ : ℕ) :
    iPred (P := P) (N := N) 0 ℓ = Sum.inr ℓ := rfl

private def mapTermSide {P N : Type} {α : Type*} (side : Bool) :
    (hybridLang P N).Term α → (extLang P N).Term α
  | .var a => .var a
  | @FirstOrder.Language.Term.func _ _ 0 s _ => FirstOrder.Language.Term.func (L := extLang P N) (l := 0) (nomConst side s) Fin.elim0
  | @FirstOrder.Language.Term.func _ _ (_ + 1) f _ => PEmpty.elim f

private def relativize {P N : Type} {α : Type*} (side : Bool) :
    ∀ {n : ℕ}, (hybridLang P N).BoundedFormula α n → (extLang P N).BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (mapTermSide side t₁) (mapTermSide side t₂)
  | _, @FirstOrder.Language.BoundedFormula.rel _ _ _ 0 r _ => PEmpty.elim r
  | _, @FirstOrder.Language.BoundedFormula.rel _ _ _ 1 p ts =>
      FirstOrder.Language.BoundedFormula.rel (pPred side p) (fun i => mapTermSide side (ts i))
  | _, @FirstOrder.Language.BoundedFormula.rel _ _ _ 2 () ts =>
      FirstOrder.Language.BoundedFormula.rel (rPred side) (fun i => mapTermSide side (ts i))
  | _, @FirstOrder.Language.BoundedFormula.rel _ _ _ (_ + 3) r _ => PEmpty.elim r
  | _, .imp f₁ f₂ => .imp (relativize side f₁) (relativize side f₂)
  | n, .all f =>
      .all ((FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (uPred side)
        (FirstOrder.Language.Term.var (Sum.inr (Fin.last n)))).imp (relativize side f))

/-- Substructure of an `extLang`-model on `{ x // uPred side x }`, given nominal closure. -/
private abbrev sideStruct {P N M : Type} [(extLang P N).Structure M] (side : Bool)
    (hnom : ∀ s : N, FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M) (uPred side)
      ![FirstOrder.Language.Structure.funMap (L := extLang P N) (M := M) (n := 0) (nomConst side s) Fin.elim0]) :
    (hybridLang P N).Structure { x : M // FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M) (uPred side) ![x] } where
  funMap := fun {n} f _ =>
    match n, f with
    | 0, s =>
        ⟨FirstOrder.Language.Structure.funMap (L := extLang P N) (M := M) (n := 0) (nomConst side s) Fin.elim0, hnom s⟩
    | _ + 1, f => PEmpty.elim f
  RelMap := fun {n} r xs =>
    match n, r with
    | 1, p => FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M) (pPred side p) (fun i => (xs i).1)
    | 2, () => FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M) (rPred side) (fun i => (xs i).1)
    | 0, r => PEmpty.elim r
    | _ + 3, r => PEmpty.elim r

private lemma realize_mapTermSide {P N M : Type} {α : Type*} [(extLang P N).Structure M]
    (side : Bool)
    (hnom : ∀ s : N, FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M) (uPred side)
      ![FirstOrder.Language.Structure.funMap (L := extLang P N) (M := M) (n := 0) (nomConst side s) Fin.elim0])
    (t : (hybridLang P N).Term α)
    (v : α → { x : M // FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M) (uPred side) ![x] }) :
    (mapTermSide side t).realize (fun a => (v a).1) =
      (@FirstOrder.Language.Term.realize (hybridLang P N) _ (sideStruct side hnom) _ v t).1 := by
  induction t with
  | var a => rfl
  | @func l f ts _ =>
    cases l with
    | zero =>
      change FirstOrder.Language.Structure.funMap (L := extLang P N) (n := 0) (nomConst side f)
        (fun i : Fin 0 => FirstOrder.Language.Term.realize (L := extLang P N) (fun a => (v a).1) (Fin.elim0 i)) =
        FirstOrder.Language.Structure.funMap (L := extLang P N) (n := 0) (nomConst side f) Fin.elim0
      have h1 : (fun i : Fin 0 => FirstOrder.Language.Term.realize (L := extLang P N) (fun a => (v a).1) (Fin.elim0 i)) = Fin.elim0 :=
        funext (fun i => Fin.elim0 i)
      rw [h1]
    | succ _ => exact PEmpty.elim f

private lemma realize_relativize {P N M : Type} {α : Type*} [(extLang P N).Structure M]
    (side : Bool)
    (hnom : ∀ s : N, FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M) (uPred side)
      ![FirstOrder.Language.Structure.funMap (L := extLang P N) (M := M) (n := 0) (nomConst side s) Fin.elim0]) :
    ∀ {n : ℕ} (φ : (hybridLang P N).BoundedFormula α n)
      (v : α → { x : M // FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M) (uPred side) ![x] })
      (xs : Fin n → { x : M // FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M) (uPred side) ![x] }),
      (relativize side φ).Realize (fun a => (v a).1) (fun i => (xs i).1) ↔
        @FirstOrder.Language.BoundedFormula.Realize (hybridLang P N) _ (sideStruct side hnom) _ _ φ v xs := by
  let _ : (hybridLang P N).Structure { x : M // FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M) (uPred side) ![x] } :=
    sideStruct side hnom
  intro n φ
  induction φ with
  | falsum => intro _ _; rfl
  | equal t₁ t₂ =>
    intro v xs
    simp only [relativize, FirstOrder.Language.BoundedFormula.Realize]
    have he1 : Sum.elim (fun a => (v a).1) (fun i => (xs i).1) = fun x => (Sum.elim v xs x).1 := by
      funext x; cases x <;> rfl
    rw [he1, realize_mapTermSide side hnom t₁, realize_mapTermSide side hnom t₂]
    exact Subtype.ext_iff.symm
  | @rel l n' r ts =>
    intro v xs
    have he1 : Sum.elim (fun a => (v a).1) (fun i => (xs i).1) = fun x => (Sum.elim v xs x).1 := by
      funext x; cases x <;> rfl
    match n', r with
    | 0, r => exact PEmpty.elim r
    | 1, p =>
      simp only [relativize, FirstOrder.Language.BoundedFormula.Realize, he1,
        realize_mapTermSide side hnom]
      rfl
    | 2, () =>
      simp only [relativize, FirstOrder.Language.BoundedFormula.Realize, he1,
        realize_mapTermSide side hnom]
      rfl
    | _ + 3, r => exact PEmpty.elim r
  | imp f₁ f₂ ih1 ih2 =>
    intro v xs
    simp only [relativize, FirstOrder.Language.BoundedFormula.Realize, ih1, ih2]
  | all f ih =>
    intro v xs
    simp only [relativize, FirstOrder.Language.BoundedFormula.Realize,
      realize_bf1, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
    constructor
    · intro h a
      have ha := h a.1 a.2
      have hsn : Fin.snoc (fun i => (xs i).1) a.1 =
          fun i => (Fin.snoc (α := fun _ => { x : M // FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M) (uPred side) ![x] }) xs a i).1 := by
        funext i; refine Fin.lastCases ?_ ?_ i <;> simp
      rw [hsn] at ha
      exact (ih v (Fin.snoc xs a)).mp ha
    · intro h a ha
      have hsn : Fin.snoc (fun i => (xs i).1) a =
          fun i => (Fin.snoc (α := fun _ => { x : M // FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M) (uPred side) ![x] }) xs ⟨a, ha⟩ i).1 := by
        funext i; refine Fin.lastCases ?_ ?_ i <;> simp
      rw [hsn]
      exact (ih v (Fin.snoc xs ⟨a, ha⟩)).mpr (h ⟨a, ha⟩)

/-- Helper: apply `m` universal quantifiers to a `BoundedFormula Empty m` to get a `Sentence`. -/
private def closeAll {L : FirstOrder.Language} : ∀ {m : ℕ}, L.BoundedFormula Empty m → L.Sentence
  | 0, f => f
  | _ + 1, f => closeAll f.all

private lemma realize_closeAll {L : FirstOrder.Language} {M : Type*} [L.Structure M] :
    ∀ {m : ℕ} (f : L.BoundedFormula Empty m),
      (closeAll f).Realize M ↔ ∀ xs : Fin m → M, f.Realize Empty.elim xs
  | 0, f => by
      simp only [closeAll, FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize]
      have hE : (default : Empty → M) = Empty.elim := funext (fun e => Empty.elim e)
      have h0 : (default : Fin 0 → M) = Fin.elim0 := funext (fun i => Fin.elim0 i)
      rw [hE, h0]
      constructor
      · intro h xs; rwa [show xs = Fin.elim0 from funext (fun i => Fin.elim0 i)]
      · intro h; exact h Fin.elim0
  | m + 1, f => by
      rw [closeAll, realize_closeAll]
      simp only [FirstOrder.Language.BoundedFormula.realize_all]
      constructor
      · intro h xs
        have h1 := h (Fin.init xs) (xs (Fin.last m))
        rwa [Fin.snoc_init_self] at h1
      · intro h xs a
        exact h (Fin.snoc xs a)

/-- Helper: build the `2*(k+1)`-tuple of bound variables for `I_ℓ^k(ms, m, ns, n)`. -/
private def tupleTerms {L : FirstOrder.Language} {n : ℕ} {k : ℕ}
    (ms : Fin k → L.Term (Empty ⊕ Fin n)) (m : L.Term (Empty ⊕ Fin n))
    (ns : Fin k → L.Term (Empty ⊕ Fin n)) (m' : L.Term (Empty ⊕ Fin n)) :
    Fin (2 * (k + 1)) → L.Term (Empty ⊕ Fin n) :=
  fun idx =>
    if h1 : idx.val < k then ms ⟨idx.val, h1⟩
    else if h_eq : idx.val = k then m
    else if h2 : idx.val < 2 * k + 1 then ns ⟨idx.val - (k + 1), by omega⟩
    else m'

private def jAtom {P N : Type} {n : ℕ} (k ℓ : ℕ)
    (ms : Fin k → (extLang P N).Term (Empty ⊕ Fin n)) (m : (extLang P N).Term (Empty ⊕ Fin n))
    (ns : Fin k → (extLang P N).Term (Empty ⊕ Fin n)) (m' : (extLang P N).Term (Empty ⊕ Fin n)) :
    (extLang P N).BoundedFormula Empty n :=
  FirstOrder.Language.Relations.boundedFormula (L := extLang P N) (iPred k ℓ) (tupleTerms ms m ns m')

private lemma realize_jAtom {P N M : Type} [(extLang P N).Structure M] {n k ℓ : ℕ}
    (ms : Fin k → (extLang P N).Term (Empty ⊕ Fin n)) (m : (extLang P N).Term (Empty ⊕ Fin n))
    (ns : Fin k → (extLang P N).Term (Empty ⊕ Fin n)) (m' : (extLang P N).Term (Empty ⊕ Fin n))
    (v : Empty → M) (xs : Fin n → M) :
    (jAtom k ℓ ms m ns m').Realize v xs ↔
      FirstOrder.Language.Structure.RelMap (L := extLang P N) (iPred k ℓ)
        (fun i => (tupleTerms ms m ns m' i).realize (Sum.elim v xs)) := Iff.rfl

/-- Bound variable `i : Fin n` as an `extLang` term. -/
private def bvar {L : FirstOrder.Language} {n : ℕ} (i : Fin n) : L.Term (Empty ⊕ Fin n) :=
  FirstOrder.Language.Term.var (Sum.inr i)

/-- Standard variable tuple `ms, m, ns, n` from `2*(k+1)` bound variables. -/
private def stdMs {L : FirstOrder.Language} {k : ℕ} (j : Fin k) : L.Term (Empty ⊕ Fin (2 * (k + 1))) :=
  bvar ⟨j.val, by omega⟩

private def stdM {L : FirstOrder.Language} {k : ℕ} : L.Term (Empty ⊕ Fin (2 * (k + 1))) :=
  bvar ⟨k, by omega⟩

private def stdNs {L : FirstOrder.Language} {k : ℕ} (j : Fin k) : L.Term (Empty ⊕ Fin (2 * (k + 1))) :=
  bvar ⟨k + 1 + j.val, by omega⟩

private def stdM' {L : FirstOrder.Language} {k : ℕ} : L.Term (Empty ⊕ Fin (2 * (k + 1))) :=
  bvar ⟨2 * k + 1, by omega⟩

/-- Closed sentence `∃ x y, U₁(x) ∧ U₂(y) ∧ I_0^0(x, y) ∧ φ^{U₁}(x) ∧ ¬φ^{U₂}(y)`. -/
private def initSentence {P N : Type} (φ : (hybridLang P N).Formula (Fin 1)) :
    (extLang P N).Sentence :=
  let φ1 : (extLang P N).BoundedFormula Empty 2 :=
    (relativize false φ).relabel (fun _ => Sum.inr (0 : Fin 2))
  let φ2 : (extLang P N).BoundedFormula Empty 2 :=
    (relativize true φ).relabel (fun _ => Sum.inr (1 : Fin 2))
  let body : (extLang P N).BoundedFormula Empty 2 :=
    FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (uPred false) (bvar 0) ⊓
    FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (uPred true) (bvar 1) ⊓
    jAtom 0 0 Fin.elim0 (bvar 0) Fin.elim0 (bvar 1) ⊓
    φ1 ⊓ φ2.not
  body.ex.ex

/-- Full first-order theory for Lindström's compactness step (`Theorem 1`), indexed so we can
read off the maximum level `ℓ` appearing in any sentence! -/
private inductive LindstromAx (P N : Type) (F : HybridFeatures) : Type
  | init
  | nomU (side : Bool) (s : N)
  | wellTyped (k ℓ : ℕ)
  | propAx (k ℓ : ℕ) (p : P)
  | wvarAx (k ℓ : ℕ) (j : Fin k)
  | forthAx (k ℓ : ℕ)
  | backAx (k ℓ : ℕ)
  | nomAx (k ℓ : ℕ) (s : N) (h : F.hasNom = true)
  | extAx (k ℓ : ℕ) (h : F.hasBind = true ∨ F.hasExists = true)
  | bindAx (k ℓ : ℕ) (j : Fin k) (h : F.hasBind = true)
  | atvAx (k ℓ : ℕ) (j : Fin k) (h : F.hasJump = true)
  | atnAx (k ℓ : ℕ) (s : N) (h1 : F.hasJump = true) (h2 : F.hasNom = true)
  | exForthAx (k ℓ : ℕ) (j : Fin k) (h : F.hasExists = true)
  | exBackAx (k ℓ : ℕ) (j : Fin k) (h : F.hasExists = true)

private def axLevel {P N : Type} {F : HybridFeatures} : LindstromAx P N F → ℕ
  | .init => 0
  | .nomU _ _ => 0
  | .wellTyped _ ℓ => ℓ
  | .propAx _ ℓ _ => ℓ
  | .wvarAx _ ℓ _ => ℓ
  | .forthAx _ ℓ => ℓ + 1
  | .backAx _ ℓ => ℓ + 1
  | .nomAx _ ℓ _ _ => ℓ
  | .extAx _ ℓ _ => ℓ + 1
  | .bindAx _ ℓ _ _ => ℓ + 1
  | .atvAx _ ℓ _ _ => ℓ
  | .atnAx _ ℓ _ _ _ => ℓ
  | .exForthAx _ ℓ _ _ => ℓ + 1
  | .exBackAx _ ℓ _ _ => ℓ + 1

private def axSentence {P N : Type} {F : HybridFeatures}
    (φ : (hybridLang P N).Formula (Fin 1)) : LindstromAx P N F → (extLang P N).Sentence
  | .init => initSentence φ
  | .nomU side s =>
      FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (uPred side)
        (FirstOrder.Language.Term.func (L := extLang P N) (l := 0) (nomConst side s) Fin.elim0)
  | .wellTyped k ℓ =>
      let conjU1 : (extLang P N).BoundedFormula Empty (2 * (k + 1)) :=
        ((List.finRange k).map (fun j =>
          FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (uPred false) (stdMs j))).foldr
          (· ⊓ ·) (FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (uPred false) stdM)
      let conjU2 : (extLang P N).BoundedFormula Empty (2 * (k + 1)) :=
        ((List.finRange k).map (fun j =>
          FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (uPred true) (stdNs j))).foldr
          (· ⊓ ·) (FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (uPred true) stdM')
      closeAll ((jAtom k ℓ stdMs stdM stdNs stdM').imp (conjU1 ⊓ conjU2))
  | .propAx k ℓ p =>
      closeAll ((jAtom k ℓ stdMs stdM stdNs stdM').imp
        ((FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (pPred false p) stdM).iff
         (FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (pPred true p) stdM')))
  | .wvarAx k ℓ j =>
      closeAll ((jAtom k ℓ stdMs stdM stdNs stdM').imp
        (((stdMs j).bdEqual stdM).iff ((stdNs j).bdEqual stdM')))
  | .forthAx k ℓ =>
      let n1 := 2 * (k + 1) + 1
      let ms1 : Fin k → _ := fun j => liftTerm1 (stdMs j)
      let m1 : _ := liftTerm1 (stdM (k := k))
      let ns1 : Fin k → _ := fun j => liftTerm1 (stdNs j)
      let m1' : _ := liftTerm1 (stdM' (k := k))
      let z1 : _ := bvar (Fin.last (2 * (k + 1)))
      let ms2 : Fin k → _ := fun j => liftTerm1 (ms1 j)
      let ns2 : Fin k → _ := fun j => liftTerm1 (ns1 j)
      let m2' : _ := liftTerm1 m1'
      let z1_2 : _ := liftTerm1 z1
      let z2 : _ := bvar (Fin.last n1)
      let concl : (extLang P N).BoundedFormula Empty n1 :=
        (FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (uPred true) z2 ⊓
         FirstOrder.Language.Relations.boundedFormula₂ (L := extLang P N) (rPred true) m2' z2 ⊓
         jAtom k (ℓ + 1) ms2 z1_2 ns2 z2).ex
      closeAll (m := n1)
        ((jAtom k ℓ ms1 m1 ns1 m1' ⊓
          FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (uPred false) z1 ⊓
          FirstOrder.Language.Relations.boundedFormula₂ (L := extLang P N) (rPred false) m1 z1).imp concl)
  | .backAx k ℓ =>
      let n1 := 2 * (k + 1) + 1
      let ms1 : Fin k → _ := fun j => liftTerm1 (stdMs j)
      let m1 : _ := liftTerm1 (stdM (k := k))
      let ns1 : Fin k → _ := fun j => liftTerm1 (stdNs j)
      let m1' : _ := liftTerm1 (stdM' (k := k))
      let z2 : _ := bvar (Fin.last (2 * (k + 1)))
      let ms2 : Fin k → _ := fun j => liftTerm1 (ms1 j)
      let m2 : _ := liftTerm1 m1
      let ns2 : Fin k → _ := fun j => liftTerm1 (ns1 j)
      let z2_2 : _ := liftTerm1 z2
      let z1 : _ := bvar (Fin.last n1)
      let concl : (extLang P N).BoundedFormula Empty n1 :=
        (FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (uPred false) z1 ⊓
         FirstOrder.Language.Relations.boundedFormula₂ (L := extLang P N) (rPred false) m2 z1 ⊓
         jAtom k (ℓ + 1) ms2 z1 ns2 z2_2).ex
      closeAll (m := n1)
        ((jAtom k ℓ ms1 m1 ns1 m1' ⊓
          FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (uPred true) z2 ⊓
          FirstOrder.Language.Relations.boundedFormula₂ (L := extLang P N) (rPred true) m1' z2).imp concl)
  | .nomAx k ℓ s _ =>
      closeAll ((jAtom k ℓ stdMs stdM stdNs stdM').imp
        ((stdM.bdEqual (FirstOrder.Language.Term.func (L := extLang P N) (l := 0) (nomConst false s) Fin.elim0)).iff
         (stdM'.bdEqual (FirstOrder.Language.Term.func (L := extLang P N) (l := 0) (nomConst true s) Fin.elim0))))
  | .extAx k ℓ _ =>
      closeAll ((jAtom k ℓ stdMs stdM stdNs stdM').imp
        (jAtom (k + 1) (ℓ + 1) (Fin.snoc stdMs stdM) stdM (Fin.snoc stdNs stdM') stdM'))
  | .bindAx k ℓ j _ =>
      closeAll ((jAtom k ℓ stdMs stdM stdNs stdM').imp
        (jAtom k (ℓ + 1) (Function.update stdMs j stdM) stdM
          (Function.update stdNs j stdM') stdM'))
  | .atvAx k ℓ j _ =>
      closeAll ((jAtom k ℓ stdMs stdM stdNs stdM').imp
        (jAtom k ℓ stdMs (stdMs j) stdNs (stdNs j)))
  | .atnAx k ℓ s _ _ =>
      closeAll ((jAtom k ℓ stdMs stdM stdNs stdM').imp
        (jAtom k ℓ stdMs
          (FirstOrder.Language.Term.func (L := extLang P N) (l := 0) (nomConst false s) Fin.elim0)
          stdNs
          (FirstOrder.Language.Term.func (L := extLang P N) (l := 0) (nomConst true s) Fin.elim0)))
  | .exForthAx k ℓ j _ =>
      let n1 := 2 * (k + 1) + 1
      let ms1 : Fin k → _ := fun i => liftTerm1 (stdMs i)
      let m1 : _ := liftTerm1 (stdM (k := k))
      let ns1 : Fin k → _ := fun i => liftTerm1 (stdNs i)
      let m1' : _ := liftTerm1 (stdM' (k := k))
      let a1 : _ := bvar (Fin.last (2 * (k + 1)))
      let ms2 : Fin k → _ := fun i => liftTerm1 (ms1 i)
      let m2 : _ := liftTerm1 m1
      let ns2 : Fin k → _ := fun i => liftTerm1 (ns1 i)
      let m2' : _ := liftTerm1 m1'
      let a1_2 : _ := liftTerm1 a1
      let a2 : _ := bvar (Fin.last n1)
      let concl : (extLang P N).BoundedFormula Empty n1 :=
        (FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (uPred true) a2 ⊓
         jAtom k (ℓ + 1) (Function.update ms2 j a1_2) m2 (Function.update ns2 j a2) m2').ex
      closeAll (m := n1)
        ((jAtom k ℓ ms1 m1 ns1 m1' ⊓
          FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (uPred false) a1).imp concl)
  | .exBackAx k ℓ j _ =>
      let n1 := 2 * (k + 1) + 1
      let ms1 : Fin k → _ := fun i => liftTerm1 (stdMs i)
      let m1 : _ := liftTerm1 (stdM (k := k))
      let ns1 : Fin k → _ := fun i => liftTerm1 (stdNs i)
      let m1' : _ := liftTerm1 (stdM' (k := k))
      let a2 : _ := bvar (Fin.last (2 * (k + 1)))
      let ms2 : Fin k → _ := fun i => liftTerm1 (ms1 i)
      let m2 : _ := liftTerm1 m1
      let ns2 : Fin k → _ := fun i => liftTerm1 (ns1 i)
      let m2' : _ := liftTerm1 m1'
      let a2_2 : _ := liftTerm1 a2
      let a1 : _ := bvar (Fin.last n1)
      let concl : (extLang P N).BoundedFormula Empty n1 :=
        (FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (uPred false) a1 ⊓
         jAtom k (ℓ + 1) (Function.update ms2 j a1) m2 (Function.update ns2 j a2_2) m2').ex
      closeAll (m := n1)
        ((jAtom k ℓ ms1 m1 ns1 m1' ⊓
          FirstOrder.Language.Relations.boundedFormula₁ (L := extLang P N) (uPred true) a2).imp concl)

/-- Build the finite-level model `M₁ ⊕ M₂` for level bound `L`. -/
private abbrev sumModel {P N M₁ M₂ : Type}
    [(hybridLang P N).Structure M₁] [(hybridLang P N).Structure M₂]
    (F : HybridFeatures) (L : ℕ) : (extLang P N).Structure (M₁ ⊕ M₂) where
  funMap := fun {n} f _ =>
    match n, f with
    | 0, Sum.inl s => Sum.inl (nomVal (P := P) (N := N) s)
    | 0, Sum.inr s => Sum.inr (nomVal (P := P) (N := N) s)
    | _ + 1, f => PEmpty.elim f
  RelMap := fun {n} r xs =>
    match n, r with
    | 0, r => PEmpty.elim r
    | 1, Sum.inl (Sum.inl ()) => match xs 0 with | Sum.inl _ => True | Sum.inr _ => False
    | 1, Sum.inl (Sum.inr ()) => match xs 0 with | Sum.inl _ => False | Sum.inr _ => True
    | 1, Sum.inr (Sum.inl p) => match xs 0 with | Sum.inl x => propVal (P := P) (N := N) p x | Sum.inr _ => False
    | 1, Sum.inr (Sum.inr p) => match xs 0 with | Sum.inl _ => False | Sum.inr y => propVal (P := P) (N := N) p y
    | 2, Sum.inl (Sum.inl ()) =>
        match xs 0, xs 1 with | Sum.inl x, Sum.inl y => accRel (P := P) (N := N) x y | _, _ => False
    | 2, Sum.inl (Sum.inr ()) =>
        match xs 0, xs 1 with | Sum.inr x, Sum.inr y => accRel (P := P) (N := N) x y | _, _ => False
    | 2, Sum.inr ℓ =>
        match xs 0, xs 1 with
        | Sum.inl x, Sum.inr y => ℓ ≤ L ∧ hTypeEq (P := P) (N := N) F (L - ℓ) 0 Fin.elim0 x Fin.elim0 y
        | _, _ => False
    | n + 3, r =>
        if hmod : n % 2 = 1 then
          let k : ℕ := n / 2 + 1
          let ℓ : ℕ := cast (by simp [extLang, hmod]) r
          ∃ (ms : Fin k → M₁) (m : M₁) (ns : Fin k → M₂) (m' : M₂),
            (∀ i : Fin (n + 3),
              xs i =
                if h1 : i.val < k then Sum.inl (ms ⟨i.val, h1⟩)
                else if h_eq : i.val = k then Sum.inl m
                else if h2 : i.val < 2 * k + 1 then Sum.inr (ns ⟨i.val - (k + 1), by omega⟩)
                else Sum.inr m') ∧
            ℓ ≤ L ∧ hTypeEq (P := P) (N := N) F (L - ℓ) k ms m ns m'
        else PEmpty.elim (cast (by simp [extLang, hmod]) r)

private lemma relMap_cast {L : FirstOrder.Language} {M : Type*} [L.Structure M]
    {m n : ℕ} (h : m = n) (r : L.Relations m) (ys : Fin n → M) :
    FirstOrder.Language.Structure.RelMap (cast (congrArg L.Relations h) r) ys =
      FirstOrder.Language.Structure.RelMap r (ys ∘ Fin.cast h) := by
  subst h; rfl

private lemma hTypeEq_cast {P N M₁ M₂ : Type} [(hybridLang P N).Structure M₁]
    [(hybridLang P N).Structure M₂] {F : HybridFeatures} {d k₁ k₂ : ℕ} (h : k₁ = k₂)
    (a : Fin k₂ → M₁) (x : M₁) (b : Fin k₂ → M₂) (y : M₂) :
    hTypeEq (P := P) (N := N) F d k₁ (a ∘ Fin.cast h) x (b ∘ Fin.cast h) y ↔
      hTypeEq (P := P) (N := N) F d k₂ a x b y := by
  subst h; rfl

private lemma sumModel_jAtom_iff {P N M₁ M₂ : Type}
    [(hybridLang P N).Structure M₁] [(hybridLang P N).Structure M₂]
    (F : HybridFeatures) (L : ℕ) {n k ℓ : ℕ}
    (ms : Fin k → (extLang P N).Term (Empty ⊕ Fin n)) (m : (extLang P N).Term (Empty ⊕ Fin n))
    (ns : Fin k → (extLang P N).Term (Empty ⊕ Fin n)) (m' : (extLang P N).Term (Empty ⊕ Fin n))
    (xs : Fin n → M₁ ⊕ M₂) :
    @FirstOrder.Language.BoundedFormula.Realize (extLang P N) (M₁ ⊕ M₂) (sumModel F L)
      Empty n (jAtom k ℓ ms m ns m') Empty.elim xs ↔
    ∃ (a : Fin k → M₁) (x : M₁) (b : Fin k → M₂) (y : M₂),
      (∀ j, @FirstOrder.Language.Term.realize (extLang P N) (M₁ ⊕ M₂) (sumModel F L) _
        (Sum.elim Empty.elim xs) (ms j) = Sum.inl (a j)) ∧
      @FirstOrder.Language.Term.realize (extLang P N) (M₁ ⊕ M₂) (sumModel F L) _
        (Sum.elim Empty.elim xs) m = Sum.inl x ∧
      (∀ j, @FirstOrder.Language.Term.realize (extLang P N) (M₁ ⊕ M₂) (sumModel F L) _
        (Sum.elim Empty.elim xs) (ns j) = Sum.inr (b j)) ∧
      @FirstOrder.Language.Term.realize (extLang P N) (M₁ ⊕ M₂) (sumModel F L) _
        (Sum.elim Empty.elim xs) m' = Sum.inr y ∧
      ℓ ≤ L ∧ hTypeEq (P := P) (N := N) F (L - ℓ) k a x b y := by
  let _ : (extLang P N).Structure (M₁ ⊕ M₂) := sumModel F L
  cases k with
  | zero =>
    simp only [jAtom, iPred_zero]
    have h0 : (tupleTerms ms m ns m' 0).realize (Sum.elim Empty.elim xs) =
        m.realize (Sum.elim Empty.elim xs) := by simp [tupleTerms]
    have h1 : (tupleTerms ms m ns m' 1).realize (Sum.elim Empty.elim xs) =
        m'.realize (Sum.elim Empty.elim xs) := by simp [tupleTerms]
    change (match (tupleTerms ms m ns m' 0).realize (Sum.elim Empty.elim xs),
        (tupleTerms ms m ns m' 1).realize (Sum.elim Empty.elim xs) with
      | Sum.inl x, Sum.inr y => ℓ ≤ L ∧ hTypeEq (P := P) (N := N) F (L - ℓ) 0 Fin.elim0 x Fin.elim0 y
      | _, _ => False) ↔ _
    rw [h0, h1]
    cases hm : m.realize (Sum.elim Empty.elim xs) <;> cases hm' : m'.realize (Sum.elim Empty.elim xs)
    · simp
    · constructor
      · rintro ⟨hℓ, ht⟩
        exact ⟨Fin.elim0, _, Fin.elim0, _, fun j => Fin.elim0 j, rfl, fun j => Fin.elim0 j, rfl, hℓ, ht⟩
      · rintro ⟨a, x, b, y, _, hx, _, hy, hℓ, ht⟩
        have hx' := Sum.inl.inj hx; have hy' := Sum.inr.inj hy; subst hx'; subst hy'
        rw [show a = Fin.elim0 from funext (fun j => Fin.elim0 j),
            show b = Fin.elim0 from funext (fun j => Fin.elim0 j)] at ht
        exact ⟨hℓ, ht⟩
    · simp
    · simp
  | succ k' =>
    have heq_ar : 2 * (k' + 1 + 1) = (2 * k' + 1) + 3 := by omega
    have hmod : (2 * k' + 1) % 2 = 1 := by omega
    have hdiv : (2 * k' + 1) / 2 + 1 = k' + 1 := by omega
    rw [realize_jAtom]
    -- Use helper to relate RelMap (iPred (k'+1) ℓ) with the `n + 3` branch!
    have hrel : ∀ (ys : Fin (2 * (k' + 1 + 1)) → M₁ ⊕ M₂),
        FirstOrder.Language.Structure.RelMap (L := extLang P N) (iPred (k' + 1) ℓ) ys ↔
        ∃ (a : Fin (k' + 1) → M₁) (x : M₁) (b : Fin (k' + 1) → M₂) (y : M₂),
          (∀ i : Fin (2 * (k' + 1 + 1)),
            ys i =
              if h1 : i.val < k' + 1 then Sum.inl (a ⟨i.val, h1⟩)
              else if h_eq : i.val = k' + 1 then Sum.inl x
              else if h2 : i.val < 2 * (k' + 1) + 1 then Sum.inr (b ⟨i.val - (k' + 2), by omega⟩)
              else Sum.inr y) ∧
          ℓ ≤ L ∧ hTypeEq (P := P) (N := N) F (L - ℓ) (k' + 1) a x b y := by
      intro ys
      have hcast_eq :
          FirstOrder.Language.Structure.RelMap (L := extLang P N) (iPred (k' + 1) ℓ) ys =
          FirstOrder.Language.Structure.RelMap (L := extLang P N) (n := (2 * k' + 1) + 3)
            (cast (by simp [extLang, hmod]) ℓ) (ys ∘ Fin.cast heq_ar.symm) := by
        have hrel_cast := relMap_cast (L := extLang P N) (M := M₁ ⊕ M₂) heq_ar.symm
          (cast (by simp [extLang, hmod] : ℕ = (extLang P N).Relations ((2 * k' + 1) + 3)) ℓ) ys
        convert hrel_cast using 2
        unfold iPred
        dsimp only
        rw [cast_cast, cast_cast]
      rw [hcast_eq]
      change (if h : (2 * k' + 1) % 2 = 1 then _ else _) ↔ _
      rw [dif_pos hmod]
      have hcast_ell : cast (by simp [extLang, hmod] : (extLang P N).Relations ((2 * k' + 1) + 3) = ℕ)
          (cast (by simp [extLang, hmod] : ℕ = (extLang P N).Relations ((2 * k' + 1) + 3)) ℓ) = ℓ := by
        rw [cast_cast]; rfl
      dsimp only
      rw [hcast_ell]
      constructor
      · rintro ⟨a, x, b, y, hys, hℓ, ht⟩
        refine ⟨a ∘ Fin.cast hdiv.symm, x, b ∘ Fin.cast hdiv.symm, y, ?_, hℓ, ?_⟩
        · intro i
          have hi := hys (Fin.cast heq_ar i)
          simpa [hdiv] using hi
        · exact (hTypeEq_cast hdiv.symm a x b y).mpr ht
      · rintro ⟨a, x, b, y, hys, hℓ, ht⟩
        refine ⟨a ∘ Fin.cast hdiv, x, b ∘ Fin.cast hdiv, y, ?_, hℓ, ?_⟩
        · intro i
          have hi := hys (Fin.cast heq_ar.symm i)
          simpa [hdiv] using hi
        · exact (hTypeEq_cast hdiv a x b y).mpr ht
    rw [hrel]
    constructor
    · rintro ⟨a, x, b, y, hys, hℓ, ht⟩
      refine ⟨a, x, b, y, ?_, ?_, ?_, ?_, hℓ, ht⟩
      · intro j
        have hi := hys ⟨j.val, by omega⟩
        have hlt : j.val < k' + 1 := j.isLt
        simpa [tupleTerms, hlt] using hi
      · have hi := hys ⟨k' + 1, by omega⟩
        simpa [tupleTerms] using hi
      · intro j
        have hi := hys ⟨k' + 2 + j.val, by omega⟩
        have h1 : ¬ (k' + 2 + j.val < k' + 1) := by omega
        have h2 : ¬ (k' + 2 + j.val = k' + 1) := by omega
        have h3 : k' + 2 + j.val < 2 * (k' + 1) + 1 := by omega
        have hsub : k' + 2 + j.val - (k' + 2) = j.val := by omega
        simpa [tupleTerms, h1, h2, h3, hsub] using hi
      · have hi := hys ⟨2 * (k' + 1) + 1, by omega⟩
        have h1 : ¬ (2 * (k' + 1) + 1 < k' + 1) := by omega
        have h2 : ¬ (2 * (k' + 1) + 1 = k' + 1) := by omega
        have h2' : ¬ (2 * (k' + 1) = k') := by omega
        have h3 : ¬ (2 * (k' + 1) + 1 < 2 * (k' + 1) + 1) := by omega
        simpa [tupleTerms, h1, h2, h2', h3] using hi
    · rintro ⟨a, x, b, y, ha, hx, hb, hy, hℓ, ht⟩
      refine ⟨a, x, b, y, ?_, hℓ, ht⟩
      intro i
      unfold tupleTerms
      split_ifs with h1 h2 h3
      · exact ha ⟨i.val, h1⟩
      · exact hx
      · exact hb ⟨i.val - (k' + 2), by omega⟩
      · exact hy

private lemma realize_foldr_inf_base {L : FirstOrder.Language} {M : Type*} [L.Structure M]
    {α : Type*} {n : ℕ} (base : L.BoundedFormula α n) (l : List (L.BoundedFormula α n))
    (v : α → M) (xs : Fin n → M) :
    (l.foldr (· ⊓ ·) base).Realize v xs ↔
      (∀ φ ∈ l, φ.Realize v xs) ∧ base.Realize v xs := by
  induction l with
  | nil => simp
  | cons φ t ih => simp [ih, and_assoc]

private lemma lindstrom_theorem {P N : Type} [Fintype P] [Fintype N]
    {F : HybridFeatures} {φ : (hybridLang P N).Formula (Fin 1)}
    {M₁ M₂ : Type} [(hybridLang P N).Structure M₁] [(hybridLang P N).Structure M₂]
    (m₁ : M₁) (m₂ : M₂)
    (hφ1 : φ.Realize ![m₁]) (hφ2 : ¬ φ.Realize ![m₂])
    (heq : ∀ ψ : HybridFormula P N 0, UsesFeatures F ψ →
      (HybridSat Fin.elim0 m₁ ψ ↔ HybridSat Fin.elim0 m₂ ψ)) :
    ∃ (N₁ N₂ : Type) (_ : (hybridLang P N).Structure N₁) (_ : (hybridLang P N).Structure N₂)
      (n₁ : N₁) (n₂ : N₂),
      FOmegaBisimilar (P := P) (N := N) F n₁ n₂ ∧ φ.Realize ![n₁] ∧ ¬ φ.Realize ![n₂] := by
  let T : (extLang P N).Theory := Set.range (axSentence (F := F) φ)
  have hfin : T.IsFinitelySatisfiable := by
    intro T0 hT0
    -- Every sentence in T0 comes from some `ax : LindstromAx P N F`; take max `axLevel`!
    classical
    have hex_ax : ∀ s ∈ T0, ∃ a : LindstromAx P N F, axSentence φ a = s := fun s hs => hT0 hs
    let L : ℕ := T0.attach.sup (fun s => axLevel (hex_ax s.1 s.2).choose)
    let _ : (extLang P N).Structure (M₁ ⊕ M₂) := sumModel F L
    have _ : Nonempty (M₁ ⊕ M₂) := ⟨Sum.inl m₁⟩
    have hnom1 : ∀ s : N, FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M₁ ⊕ M₂) (uPred false)
        ![FirstOrder.Language.Structure.funMap (L := extLang P N) (M := M₁ ⊕ M₂) (n := 0) (nomConst false s) Fin.elim0] :=
      fun _ => show True from trivial
    have hnom2 : ∀ s : N, FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M₁ ⊕ M₂) (uPred true)
        ![FirstOrder.Language.Structure.funMap (L := extLang P N) (M := M₁ ⊕ M₂) (n := 0) (nomConst true s) Fin.elim0] :=
      fun _ => show True from trivial
    -- Equivalence between sideStruct of sumModel and M₁ / M₂
    have hequiv1 : ∀ (x : M₁),
        (relativize false φ).Realize (M := M₁ ⊕ M₂) ![Sum.inl x] Fin.elim0 ↔ φ.Realize ![x] := by
      intro x
      let _ : (hybridLang P N).Structure { z : M₁ ⊕ M₂ // FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M₁ ⊕ M₂) (uPred false) ![z] } :=
        sideStruct false hnom1
      let px : { z : M₁ ⊕ M₂ // FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M₁ ⊕ M₂) (uPred false) ![z] } :=
        ⟨Sum.inl x, trivial⟩
      have h1 := realize_relativize (M := M₁ ⊕ M₂) false hnom1 φ ![px] Fin.elim0
      have harg : (fun a : Fin 1 => ((![px] : Fin 1 → _) a).1) = ![Sum.inl x] := by
        funext i; fin_cases i; rfl
      have harg2 : (fun i : Fin 0 => ((Fin.elim0 : Fin 0 → { z : M₁ ⊕ M₂ // FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M₁ ⊕ M₂) (uPred false) ![z] }) i).1) = Fin.elim0 :=
        funext (fun i => Fin.elim0 i)
      rw [harg, harg2] at h1
      rw [h1]
      let e1 : M₁ ≃[hybridLang P N] { z : M₁ ⊕ M₂ // FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M₁ ⊕ M₂) (uPred false) ![z] } :=
        { toFun := fun a => ⟨Sum.inl a, trivial⟩
          invFun := fun z => match z with | ⟨Sum.inl a, _⟩ => a | ⟨Sum.inr _, h⟩ => False.elim h
          left_inv := fun _ => rfl
          right_inv := fun z => by rcases z with ⟨a | b, h⟩; rfl; exact False.elim h
          map_fun' := fun {l} f xs => by
            cases l with
            | zero =>
              apply Subtype.ext
              change Sum.inl (FirstOrder.Language.Structure.funMap (L := hybridLang P N) (n := 0) f xs) =
                Sum.inl (FirstOrder.Language.Structure.funMap (L := hybridLang P N) (n := 0) f Fin.elim0)
              exact congrArg Sum.inl (congrArg _ (funext (fun i => Fin.elim0 i)))
            | succ _ => exact PEmpty.elim f
          map_rel' := fun {l} r xs => by
            match l, r with
            | 0, r => exact PEmpty.elim r
            | 1, p =>
              change FirstOrder.Language.Structure.RelMap (L := hybridLang P N) (n := 1) p ![xs 0] ↔ _
              exact iff_of_eq (congrArg _ (funext (fun i => by fin_cases i; rfl)))
            | 2, () =>
              change accRel (xs 0) (xs 1) ↔ _
              rw [accRel]
              exact iff_of_eq (congrArg _ (funext (fun i => by fin_cases i <;> rfl)))
            | _ + 3, r => exact PEmpty.elim r }
      have h2 := FirstOrder.Language.StrongHomClass.realize_formula e1 φ (v := ![x])
      have hcomp : (e1 ∘ ![x]) = ![px] := by
        funext i; fin_cases i; rfl
      rw [hcomp] at h2
      exact h2
    have hequiv2 : ∀ (y : M₂),
        (relativize true φ).Realize (M := M₁ ⊕ M₂) ![Sum.inr y] Fin.elim0 ↔ φ.Realize ![y] := by
      intro y
      let _ : (hybridLang P N).Structure { z : M₁ ⊕ M₂ // FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M₁ ⊕ M₂) (uPred true) ![z] } :=
        sideStruct true hnom2
      let py : { z : M₁ ⊕ M₂ // FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M₁ ⊕ M₂) (uPred true) ![z] } :=
        ⟨Sum.inr y, trivial⟩
      have h1 := realize_relativize (M := M₁ ⊕ M₂) true hnom2 φ ![py] Fin.elim0
      have harg : (fun a : Fin 1 => ((![py] : Fin 1 → _) a).1) = ![Sum.inr y] := by
        funext i; fin_cases i; rfl
      have harg2 : (fun i : Fin 0 => ((Fin.elim0 : Fin 0 → { z : M₁ ⊕ M₂ // FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M₁ ⊕ M₂) (uPred true) ![z] }) i).1) = Fin.elim0 :=
        funext (fun i => Fin.elim0 i)
      rw [harg, harg2] at h1
      rw [h1]
      let e2 : M₂ ≃[hybridLang P N] { z : M₁ ⊕ M₂ // FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M₁ ⊕ M₂) (uPred true) ![z] } :=
        { toFun := fun b => ⟨Sum.inr b, trivial⟩
          invFun := fun z => match z with | ⟨Sum.inr b, _⟩ => b | ⟨Sum.inl _, h⟩ => False.elim h
          left_inv := fun _ => rfl
          right_inv := fun z => by rcases z with ⟨a | b, h⟩; exact False.elim h; rfl
          map_fun' := fun {l} f xs => by
            cases l with
            | zero =>
              apply Subtype.ext
              change Sum.inr (FirstOrder.Language.Structure.funMap (L := hybridLang P N) (n := 0) f xs) =
                Sum.inr (FirstOrder.Language.Structure.funMap (L := hybridLang P N) (n := 0) f Fin.elim0)
              exact congrArg Sum.inr (congrArg _ (funext (fun i => Fin.elim0 i)))
            | succ _ => exact PEmpty.elim f
          map_rel' := fun {l} r xs => by
            match l, r with
            | 0, r => exact PEmpty.elim r
            | 1, p =>
              change FirstOrder.Language.Structure.RelMap (L := hybridLang P N) (n := 1) p ![xs 0] ↔ _
              exact iff_of_eq (congrArg _ (funext (fun i => by fin_cases i; rfl)))
            | 2, () =>
              change accRel (xs 0) (xs 1) ↔ _
              rw [accRel]
              exact iff_of_eq (congrArg _ (funext (fun i => by fin_cases i <;> rfl)))
            | _ + 3, r => exact PEmpty.elim r }
      have h2 := FirstOrder.Language.StrongHomClass.realize_formula e2 φ (v := ![y])
      have hcomp : (e2 ∘ ![y]) = ![py] := by
        funext i; fin_cases i; rfl
      rw [hcomp] at h2
      exact h2
    have hmod : (M₁ ⊕ M₂) ⊨ (T0 : (extLang P N).Theory) := by
      refine ⟨fun s hs => ?_⟩
      have hleL : axLevel (hex_ax s hs).choose ≤ L :=
        Finset.le_sup (f := fun x : {x // x ∈ T0} => axLevel (hex_ax x.1 x.2).choose)
          (Finset.mem_attach T0 ⟨s, hs⟩)
      rw [← (hex_ax s hs).choose_spec]
      generalize (hex_ax s hs).choose = ax at hleL ⊢
      cases ax with
      | init =>
        simp only [axSentence, initSentence, FirstOrder.Language.Sentence.Realize,
          FirstOrder.Language.Formula.Realize,
          FirstOrder.Language.BoundedFormula.realize_ex, FirstOrder.Language.BoundedFormula.realize_inf,
          FirstOrder.Language.BoundedFormula.realize_not, realize_bf1,
          FirstOrder.Language.BoundedFormula.realize_relabel, bvar, FirstOrder.Language.Term.realize_var]
        refine ⟨Sum.inl m₁, Sum.inr m₂, ?_⟩
        refine ⟨⟨⟨⟨trivial, trivial⟩, ?_⟩, ?_⟩, ?_⟩
        · rw [show (default : Empty → M₁ ⊕ M₂) = Empty.elim from funext (fun e => e.elim),
            sumModel_jAtom_iff]
          exact ⟨Fin.elim0, m₁, Fin.elim0, m₂, fun j => Fin.elim0 j, rfl,
            fun j => Fin.elim0 j, rfl, Nat.zero_le L, fun ψ hF _ => heq ψ hF⟩
        · have harg : (Sum.elim (default : Empty → M₁ ⊕ M₂) (Fin.snoc (α := fun _ => M₁ ⊕ M₂) (Fin.snoc (α := fun _ => M₁ ⊕ M₂) (default : Fin 0 → M₁ ⊕ M₂) (Sum.inl m₁)) (Sum.inr m₂) ∘ Fin.castAdd 0) ∘
              fun _ : Fin 1 => Sum.inr (0 : Fin 2)) = ![Sum.inl m₁] := by
            funext i; fin_cases i; simp [Fin.snoc]
          have harg0 : (Fin.snoc (α := fun _ => M₁ ⊕ M₂) (Fin.snoc (α := fun _ => M₁ ⊕ M₂) (default : Fin 0 → M₁ ⊕ M₂) (Sum.inl m₁)) (Sum.inr m₂) ∘ Fin.natAdd 2) = Fin.elim0 :=
            funext (fun i => Fin.elim0 i)
          rw [harg, harg0]
          exact (hequiv1 m₁).mpr hφ1
        · have harg : (Sum.elim (default : Empty → M₁ ⊕ M₂) (Fin.snoc (α := fun _ => M₁ ⊕ M₂) (Fin.snoc (α := fun _ => M₁ ⊕ M₂) (default : Fin 0 → M₁ ⊕ M₂) (Sum.inl m₁)) (Sum.inr m₂) ∘ Fin.castAdd 0) ∘
              fun _ : Fin 1 => Sum.inr (1 : Fin 2)) = ![Sum.inr m₂] := by
            funext i; fin_cases i; simp [Fin.snoc]
          have harg0 : (Fin.snoc (α := fun _ => M₁ ⊕ M₂) (Fin.snoc (α := fun _ => M₁ ⊕ M₂) (default : Fin 0 → M₁ ⊕ M₂) (Sum.inl m₁)) (Sum.inr m₂) ∘ Fin.natAdd 2) = Fin.elim0 :=
            funext (fun i => Fin.elim0 i)
          rw [harg, harg0]
          exact fun h => hφ2 ((hequiv2 m₂).mp h)
      | nomU side s =>
        cases side <;> exact trivial
      | wellTyped k ℓ =>
        rw [axSentence, realize_closeAll]
        intro xs
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, FirstOrder.Language.BoundedFormula.realize_inf,
          realize_foldr_inf_base, List.mem_map, realize_bf1,
          sumModel_jAtom_iff]
        rintro ⟨a, x, b, y, ha, hx, hb, hy, _, _⟩
        constructor
        · refine ⟨?_, ?_⟩
          · rintro _ ⟨j, _, rfl⟩
            simp only [realize_bf1, ha j]; trivial
          · rw [hx]; trivial
        · refine ⟨?_, ?_⟩
          · rintro _ ⟨j, _, rfl⟩
            simp only [realize_bf1, hb j]; trivial
          · rw [hy]; trivial
      | propAx k ℓ p =>
        rw [axSentence, realize_closeAll]
        intro xs
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, FirstOrder.Language.BoundedFormula.realize_iff,
          realize_bf1, sumModel_jAtom_iff]
        rintro ⟨a, x, b, y, _, hx, _, hy, _, ht⟩
        rw [hx, hy]
        exact ht (.prop p) trivial (Nat.zero_le _)
      | wvarAx k ℓ j =>
        rw [axSentence, realize_closeAll]
        intro xs
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, FirstOrder.Language.BoundedFormula.realize_iff,
          FirstOrder.Language.BoundedFormula.realize_bdEqual, sumModel_jAtom_iff]
        rintro ⟨a, x, b, y, ha, hx, hb, hy, _, ht⟩
        rw [ha j, hx, hb j, hy]
        have h := ht (.wvar j) trivial (Nat.zero_le _)
        simp only [HybridSat] at h
        constructor <;> intro heq'
        · exact congrArg Sum.inr (h.mp (Sum.inl.inj heq').symm).symm
        · exact congrArg Sum.inl (h.mpr (Sum.inr.inj heq').symm).symm
      | forthAx k ℓ =>
        simp only [axLevel] at hleL
        rw [axSentence, realize_closeAll]
        intro xs
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, FirstOrder.Language.BoundedFormula.realize_inf,
          realize_bf1, realize_bf2,
          FirstOrder.Language.BoundedFormula.realize_ex, sumModel_jAtom_iff]
        rintro ⟨⟨⟨a, x, b, y, ha, hx, hb, hy, _, ht⟩, hu1⟩, hr1⟩
        cases hz1 : (bvar (L := extLang P N) (Fin.last (2 * (k + 1)))).realize (Sum.elim Empty.elim xs) with
        | inr _ => rw [hz1] at hu1; exact False.elim hu1
        | inl n1 =>
          rw [hx, hz1] at hr1
          have hstep : L - ℓ = (L - (ℓ + 1)) + 1 := by omega
          rw [hstep] at ht
          obtain ⟨n2, hr2, ht'⟩ := hTypeEq_forth ht n1 hr1
          refine ⟨Sum.inr n2, ⟨⟨?_, ?_⟩, ?_⟩⟩
          · simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]; trivial
          · rw [realize_liftTerm1, hy]
            simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
            exact hr2
          · refine ⟨a, n1, b, n2, ?_, ?_, ?_, ?_, hleL, ht'⟩
            · intro j; rw [realize_liftTerm1]; exact ha j
            · rw [realize_liftTerm1]; exact hz1
            · intro j; rw [realize_liftTerm1]; exact hb j
            · simp [bvar]
      | backAx k ℓ =>
        simp only [axLevel] at hleL
        rw [axSentence, realize_closeAll]
        intro xs
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, FirstOrder.Language.BoundedFormula.realize_inf,
          realize_bf1, realize_bf2,
          FirstOrder.Language.BoundedFormula.realize_ex, sumModel_jAtom_iff]
        rintro ⟨⟨⟨a, x, b, y, ha, hx, hb, hy, _, ht⟩, hu2⟩, hr2⟩
        cases hz2 : (bvar (L := extLang P N) (Fin.last (2 * (k + 1)))).realize (Sum.elim Empty.elim xs) with
        | inl _ => rw [hz2] at hu2; exact False.elim hu2
        | inr n2 =>
          rw [hy, hz2] at hr2
          have hstep : L - ℓ = (L - (ℓ + 1)) + 1 := by omega
          rw [hstep] at ht
          obtain ⟨n1, hr1, ht'⟩ := hTypeEq_back ht n2 hr2
          refine ⟨Sum.inl n1, ⟨⟨?_, ?_⟩, ?_⟩⟩
          · simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]; trivial
          · rw [realize_liftTerm1, hx]
            simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
            exact hr1
          · refine ⟨a, n1, b, n2, ?_, ?_, ?_, ?_, hleL, ht'⟩
            · intro j; rw [realize_liftTerm1]; exact ha j
            · simp [bvar]
            · intro j; rw [realize_liftTerm1]; exact hb j
            · rw [realize_liftTerm1]; exact hz2
      | nomAx k ℓ s hnom =>
        rw [axSentence, realize_closeAll]
        intro xs
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, FirstOrder.Language.BoundedFormula.realize_iff,
          FirstOrder.Language.BoundedFormula.realize_bdEqual, sumModel_jAtom_iff]
        rintro ⟨a, x, b, y, _, hx, _, hy, _, ht⟩
        rw [hx, hy]
        have h := ht (.nom s) hnom (Nat.zero_le _)
        simp only [HybridSat] at h
        change (Sum.inl x = Sum.inl (nomVal (P := P) (N := N) s) ↔ Sum.inr y = Sum.inr (nomVal (P := P) (N := N) s))
        simp [h]
      | extAx k ℓ hBE =>
        simp only [axLevel] at hleL
        rw [axSentence, realize_closeAll]
        intro xs
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, sumModel_jAtom_iff]
        rintro ⟨a, x, b, y, ha, hx, hb, hy, _, ht⟩
        have hstep : L - ℓ = (L - (ℓ + 1)) + 1 := by omega
        rw [hstep] at ht
        refine ⟨Fin.snoc a x, x, Fin.snoc b y, y, ?_, hx, ?_, hy, hleL, hTypeEq_ext hBE ht⟩
        · intro j; refine Fin.lastCases ?_ ?_ j <;> simp [ha, hx]
        · intro j; refine Fin.lastCases ?_ ?_ j <;> simp [hb, hy]
      | bindAx k ℓ j hb =>
        simp only [axLevel] at hleL
        rw [axSentence, realize_closeAll]
        intro xs
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, sumModel_jAtom_iff]
        rintro ⟨a, x, b, y, ha, hx, hb', hy, _, ht⟩
        have hstep : L - ℓ = (L - (ℓ + 1)) + 1 := by omega
        rw [hstep] at ht
        refine ⟨Function.update a j x, x, Function.update b j y, y, ?_, hx, ?_, hy, hleL,
          hTypeEq_bind hb ht j⟩
        · intro i; by_cases h : i = j <;> simp [h, ha, hx]
        · intro i; by_cases h : i = j <;> simp [h, hb', hy]
      | atvAx k ℓ j hj =>
        rw [axSentence, realize_closeAll]
        intro xs
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, sumModel_jAtom_iff]
        rintro ⟨a, x, b, y, ha, _, hb, _, hℓ, ht⟩
        exact ⟨a, a j, b, b j, ha, ha j, hb, hb j, hℓ, hTypeEq_atv hj ht j⟩
      | atnAx k ℓ s hj hn =>
        rw [axSentence, realize_closeAll]
        intro xs
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, sumModel_jAtom_iff]
        rintro ⟨a, x, b, y, ha, _, hb, _, hℓ, ht⟩
        refine ⟨a, nomVal (P := P) (N := N) s, b, nomVal (P := P) (N := N) s, ha, rfl, hb, rfl, hℓ, hTypeEq_atn hj hn ht s⟩
      | exForthAx k ℓ j he =>
        simp only [axLevel] at hleL
        rw [axSentence, realize_closeAll]
        intro xs
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, FirstOrder.Language.BoundedFormula.realize_inf,
          realize_bf1, FirstOrder.Language.BoundedFormula.realize_ex, sumModel_jAtom_iff]
        rintro ⟨⟨a, x, b, y, ha, hx, hb, hy, _, ht⟩, hu1⟩
        cases ha1 : (bvar (L := extLang P N) (Fin.last (2 * (k + 1)))).realize (Sum.elim Empty.elim xs) with
        | inr _ => rw [ha1] at hu1; exact False.elim hu1
        | inl c1 =>
          have hstep : L - ℓ = (L - (ℓ + 1)) + 1 := by omega
          rw [hstep] at ht
          obtain ⟨c2, ht'⟩ := hTypeEq_ex_forth he ht j c1
          refine ⟨Sum.inr c2, ?_, ?_⟩
          · simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]; trivial
          · refine ⟨Function.update a j c1, x, Function.update b j c2, y, ?_, ?_, ?_, ?_, hleL, ht'⟩
            · intro i; by_cases h : i = j <;> simp [h, realize_liftTerm1, ha, ha1]
            · rw [realize_liftTerm1]; exact hx
            · intro i; by_cases h : i = j <;> simp [h, realize_liftTerm1, hb, bvar]
            · rw [realize_liftTerm1]; exact hy
      | exBackAx k ℓ j he =>
        simp only [axLevel] at hleL
        rw [axSentence, realize_closeAll]
        intro xs
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, FirstOrder.Language.BoundedFormula.realize_inf,
          realize_bf1, FirstOrder.Language.BoundedFormula.realize_ex, sumModel_jAtom_iff]
        rintro ⟨⟨a, x, b, y, ha, hx, hb, hy, _, ht⟩, hu2⟩
        cases ha2 : (bvar (L := extLang P N) (Fin.last (2 * (k + 1)))).realize (Sum.elim Empty.elim xs) with
        | inl _ => rw [ha2] at hu2; exact False.elim hu2
        | inr c2 =>
          have hstep : L - ℓ = (L - (ℓ + 1)) + 1 := by omega
          rw [hstep] at ht
          obtain ⟨c1, ht'⟩ := hTypeEq_ex_back he ht j c2
          refine ⟨Sum.inl c1, ?_, ?_⟩
          · simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]; trivial
          · refine ⟨Function.update a j c1, x, Function.update b j c2, y, ?_, ?_, ?_, ?_, hleL, ht'⟩
            · intro i; by_cases h : i = j <;> simp [h, realize_liftTerm1, ha, bvar]
            · rw [realize_liftTerm1]; exact hx
            · intro i; by_cases h : i = j <;> simp [h, realize_liftTerm1, hb, ha2]
            · rw [realize_liftTerm1]; exact hy
    exact FirstOrder.Language.Theory.Model.isSatisfiable (M₁ ⊕ M₂)
  -- Apply First-Order Compactness!
  obtain ⟨M4⟩ := FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr hfin
  have hax : ∀ a : LindstromAx P N F, (axSentence φ a).Realize M4 := fun a =>
    FirstOrder.Language.Theory.realize_sentence_of_mem T ⟨a, rfl⟩
  have hnom1 : ∀ s : N, FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (uPred false)
      ![FirstOrder.Language.Structure.funMap (L := extLang P N) (M := M4) (n := 0) (nomConst false s) Fin.elim0] := by
    intro s
    have h := hax (.nomU false s)
    simp only [axSentence, FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize,
      realize_bf1] at h
    convert h using 2
    change _ = FirstOrder.Language.Structure.funMap (L := extLang P N) (M := M4) (n := 0) (nomConst false s)
      (fun j : Fin 0 => FirstOrder.Language.Term.realize (L := extLang P N) (Sum.elim default default) (Fin.elim0 j))
    congr 1; funext j; exact Fin.elim0 j
  have hnom2 : ∀ s : N, FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (uPred true)
      ![FirstOrder.Language.Structure.funMap (L := extLang P N) (M := M4) (n := 0) (nomConst true s) Fin.elim0] := by
    intro s
    have h := hax (.nomU true s)
    simp only [axSentence, FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize,
      realize_bf1] at h
    convert h using 2
    change _ = FirstOrder.Language.Structure.funMap (L := extLang P N) (M := M4) (n := 0) (nomConst true s)
      (fun j : Fin 0 => FirstOrder.Language.Term.realize (L := extLang P N) (Sum.elim default default) (Fin.elim0 j))
    congr 1; funext j; exact Fin.elim0 j
  let N₁ := { x : M4 // FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (uPred false) ![x] }
  let N₂ := { y : M4 // FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (uPred true) ![y] }
  let _ : (hybridLang P N).Structure N₁ := sideStruct false hnom1
  let _ : (hybridLang P N).Structure N₂ := sideStruct true hnom2
  -- Extract witness `(n₁, n₂)` from `init`
  have hinit := hax .init
  simp only [axSentence, initSentence, FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize,
    FirstOrder.Language.BoundedFormula.realize_ex, FirstOrder.Language.BoundedFormula.realize_inf,
    FirstOrder.Language.BoundedFormula.realize_not, realize_bf1,
    FirstOrder.Language.BoundedFormula.realize_relabel, bvar, FirstOrder.Language.Term.realize_var,
    Sum.elim_inr] at hinit
  rcases hinit with ⟨x0, y0, ⟨⟨⟨⟨hx0, hy0⟩, hI0⟩, hφx0⟩, hφy0⟩⟩
  have h0val : Fin.snoc (α := fun _ => M4) (Fin.snoc (α := fun _ => M4) (default : Fin 0 → M4) x0) y0 (0 : Fin 2) = x0 := by
    simp [Fin.snoc]
  have h1val : Fin.snoc (α := fun _ => M4) (Fin.snoc (α := fun _ => M4) (default : Fin 0 → M4) x0) y0 (1 : Fin 2) = y0 := by
    simp [Fin.snoc]
  rw [h0val] at hx0
  rw [h1val] at hy0
  let n₁ : N₁ := ⟨x0, hx0⟩
  let n₂ : N₂ := ⟨y0, hy0⟩
  -- Define `B k ms m ns n` as `∃ ℓ, I_ℓ^k(ms, m, ns, n)` in `M4`
  let evalTuple : ∀ {k : ℕ}, (Fin k → N₁) → N₁ → (Fin k → N₂) → N₂ → Fin (2 * (k + 1)) → M4 :=
    fun {k} ms m ns n idx =>
      if h1 : idx.val < k then (ms ⟨idx.val, h1⟩).1
      else if h_eq : idx.val = k then m.1
      else if h2 : idx.val < 2 * k + 1 then (ns ⟨idx.val - (k + 1), by omega⟩).1
      else n.1
  let B : ∀ k : ℕ, (Fin k → N₁) → N₁ → (Fin k → N₂) → N₂ → Prop :=
    fun k ms m ns n =>
      ∃ ℓ : ℕ, FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (iPred k ℓ)
        (evalTuple ms m ns n)
  have hprop1 : ∀ (p : P) (x : N₁), propVal (P := P) (N := N) p x ↔
      FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (pPred false p) ![x.1] := by
    intro p x
    change FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (pPred false p)
        (fun i : Fin 1 => (![x] i).1) ↔ _
    exact iff_of_eq (congrArg (FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (pPred false p))
      (funext fun i : Fin 1 => by fin_cases i; rfl))
  have hprop2 : ∀ (p : P) (y : N₂), propVal (P := P) (N := N) p y ↔
      FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (pPred true p) ![y.1] := by
    intro p y
    change FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (pPred true p)
        (fun i : Fin 1 => (![y] i).1) ↔ _
    exact iff_of_eq (congrArg (FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (pPred true p))
      (funext fun i : Fin 1 => by fin_cases i; rfl))
  have hacc1 : ∀ (x y : N₁), accRel (P := P) (N := N) x y ↔
      FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (rPred false) ![x.1, y.1] := by
    intro x y
    change FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (rPred false)
        (fun i : Fin 2 => (![x, y] i).1) ↔ _
    exact iff_of_eq (congrArg (FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (rPred false))
      (funext fun i : Fin 2 => by fin_cases i <;> rfl))
  have hacc2 : ∀ (x y : N₂), accRel (P := P) (N := N) x y ↔
      FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (rPred true) ![x.1, y.1] := by
    intro x y
    change FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (rPred true)
        (fun i : Fin 2 => (![x, y] i).1) ↔ _
    exact iff_of_eq (congrArg (FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (rPred true))
      (funext fun i : Fin 2 => by fin_cases i <;> rfl))
  have heval1 : ∀ {k : ℕ} (ms : Fin k → N₁) (m : N₁) (ns : Fin k → N₂) (n : N₂)
      (idx : Fin (2 * (k + 1))) (h1 : idx.val < k),
      evalTuple ms m ns n idx = (ms ⟨idx.val, h1⟩).1 := by
    intro k ms m ns n idx h1; dsimp only [evalTuple]; rw [dif_pos h1]
  have heval2 : ∀ {k : ℕ} (ms : Fin k → N₁) (m : N₁) (ns : Fin k → N₂) (n : N₂)
      (idx : Fin (2 * (k + 1))) (h1 : ¬ idx.val < k) (h2 : idx.val = k),
      evalTuple ms m ns n idx = m.1 := by
    intro k ms m ns n idx h1 h2; dsimp only [evalTuple]; rw [dif_neg h1, dif_pos h2]
  have heval3 : ∀ {k : ℕ} (ms : Fin k → N₁) (m : N₁) (ns : Fin k → N₂) (n : N₂)
      (idx : Fin (2 * (k + 1))) (h1 : ¬ idx.val < k) (h2 : idx.val ≠ k) (h3 : idx.val < 2 * k + 1),
      evalTuple ms m ns n idx = (ns ⟨idx.val - (k + 1), by omega⟩).1 := by
    intro k ms m ns n idx h1 h2 h3; dsimp only [evalTuple]; rw [dif_neg h1, dif_neg h2, dif_pos h3]
  have heval4 : ∀ {k : ℕ} (ms : Fin k → N₁) (m : N₁) (ns : Fin k → N₂) (n : N₂)
      (idx : Fin (2 * (k + 1))) (h1 : ¬ idx.val < k) (h2 : idx.val ≠ k) (h3 : ¬ idx.val < 2 * k + 1),
      evalTuple ms m ns n idx = n.1 := by
    intro k ms m ns n idx h1 h2 h3; dsimp only [evalTuple]; rw [dif_neg h1, dif_neg h2, dif_neg h3]
  have hstdMs : ∀ {k : ℕ} (ms : Fin k → N₁) (m : N₁) (ns : Fin k → N₂) (n : N₂) (j : Fin k),
      (stdMs (L := extLang P N) j).realize (Sum.elim Empty.elim (evalTuple ms m ns n)) = (ms j).1 := by
    intro k ms m ns n j
    exact heval1 ms m ns n ⟨j.val, by omega⟩ j.isLt
  have hstdM : ∀ {k : ℕ} (ms : Fin k → N₁) (m : N₁) (ns : Fin k → N₂) (n : N₂),
      (stdM (L := extLang P N) (k := k)).realize (Sum.elim Empty.elim (evalTuple ms m ns n)) = m.1 := by
    intro k ms m ns n
    exact heval2 ms m ns n ⟨k, by omega⟩ (by dsimp; omega) rfl
  have hstdNs : ∀ {k : ℕ} (ms : Fin k → N₁) (m : N₁) (ns : Fin k → N₂) (n : N₂) (j : Fin k),
      (stdNs (L := extLang P N) j).realize (Sum.elim Empty.elim (evalTuple ms m ns n)) = (ns j).1 := by
    intro k ms m ns n j
    change evalTuple ms m ns n ⟨k + 1 + j.val, by omega⟩ = (ns j).1
    rw [heval3 ms m ns n ⟨k + 1 + j.val, by omega⟩ (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)]
    congr 2; ext; dsimp; omega
  have hstdM' : ∀ {k : ℕ} (ms : Fin k → N₁) (m : N₁) (ns : Fin k → N₂) (n : N₂),
      (stdM' (L := extLang P N) (k := k)).realize (Sum.elim Empty.elim (evalTuple ms m ns n)) = n.1 := by
    intro k ms m ns n
    exact heval4 ms m ns n ⟨2 * k + 1, by omega⟩ (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
  have hB_jAtom : ∀ {k ℓ : ℕ} (ms : Fin k → N₁) (m : N₁) (ns : Fin k → N₂) (n : N₂),
      (jAtom (P := P) (N := N) k ℓ stdMs stdM stdNs stdM').Realize (M := M4) Empty.elim (evalTuple ms m ns n) ↔
      FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (iPred k ℓ) (evalTuple ms m ns n) := by
    intro k ℓ ms m ns n
    simp only [realize_jAtom]
    refine iff_of_eq (congrArg _ (funext (fun idx => ?_)))
    unfold tupleTerms
    split_ifs with h1 h2 h3
    · rw [hstdMs, heval1 ms m ns n idx h1]
    · rw [hstdM, heval2 ms m ns n idx h1 h2]
    · rw [hstdNs, heval3 ms m ns n idx h1 h2 h3]
    · rw [hstdM', heval4 ms m ns n idx h1 h2 h3]
  have hJ_lift : ∀ {k ℓ : ℕ} (ms : Fin k → N₁) (m : N₁) (ns : Fin k → N₂) (n : N₂) (z : M4),
      FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (iPred k ℓ) (evalTuple ms m ns n) →
      (jAtom (P := P) (N := N) k ℓ (fun i => liftTerm1 (stdMs i)) (liftTerm1 stdM)
        (fun i => liftTerm1 (stdNs i)) (liftTerm1 stdM')).Realize (M := M4) Empty.elim
        (Fin.snoc (evalTuple ms m ns n) z) := by
    intro k ℓ ms m ns n z hℓ
    rw [← hB_jAtom] at hℓ
    simp only [realize_jAtom] at hℓ ⊢
    refine Eq.mp (congrArg (FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (iPred k ℓ))
      (funext fun idx => ?_)) hℓ
    unfold tupleTerms
    split_ifs <;> simp only [realize_liftTerm1]
  have hbisim : IsFOmegaBisim (P := P) (N := N) F B :=
    { prop := by
        rintro k ms m ns n ⟨ℓ, hℓ⟩ p
        have h := (realize_closeAll _).mp (hax (.propAx k ℓ p)) (evalTuple ms m ns n)
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, FirstOrder.Language.BoundedFormula.realize_iff,
          realize_bf1, hB_jAtom] at h
        have h' := h hℓ
        rw [hstdM, hstdM'] at h'
        rw [hprop1, hprop2]
        exact h'
      wvar := by
        rintro k ms m ns n ⟨ℓ, hℓ⟩ j
        have h := (realize_closeAll _).mp (hax (.wvarAx k ℓ j)) (evalTuple ms m ns n)
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, FirstOrder.Language.BoundedFormula.realize_iff,
          FirstOrder.Language.BoundedFormula.realize_bdEqual, hB_jAtom] at h
        have h' := h hℓ
        rw [hstdMs, hstdM, hstdNs, hstdM'] at h'
        rw [Subtype.ext_iff, Subtype.ext_iff]
        exact h'
      forth := by
        rintro k ms m ns n ⟨ℓ, hℓ⟩ a ha
        have h := (realize_closeAll _).mp (hax (.forthAx k ℓ)) (Fin.snoc (evalTuple ms m ns n) a.1)
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, FirstOrder.Language.BoundedFormula.realize_inf,
          realize_bf1, realize_bf2,
          FirstOrder.Language.BoundedFormula.realize_ex] at h
        obtain ⟨b0, ⟨⟨hbU, hbR⟩, hbJ⟩⟩ := h ⟨⟨hJ_lift ms m ns n a.1 hℓ, by
          simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
          exact a.2⟩, by
          rw [realize_liftTerm1, hstdM]
          simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
          exact (hacc1 m a).mp ha⟩
        simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last] at hbU
        refine ⟨⟨b0, hbU⟩, ?_, ℓ + 1, ?_⟩
        · rw [realize_liftTerm1, realize_liftTerm1, hstdM'] at hbR
          simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last] at hbR
          exact (hacc2 n ⟨b0, hbU⟩).mpr hbR
        · simp only [realize_jAtom] at hbJ
          refine Eq.mp (congrArg (FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (iPred k (ℓ + 1)))
            (funext fun idx => ?_)) hbJ
          unfold tupleTerms
          split_ifs with h1 h2 h3
          · rw [realize_liftTerm1, realize_liftTerm1, hstdMs, heval1 _ _ _ _ _ h1]
          · rw [realize_liftTerm1, heval2 _ _ _ _ _ h1 h2]
            simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
          · rw [realize_liftTerm1, realize_liftTerm1, hstdNs, heval3 _ _ _ _ _ h1 h2 h3]
          · rw [heval4 _ _ _ _ _ h1 h2 h3]
            simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
      back := by
        rintro k ms m ns n ⟨ℓ, hℓ⟩ b hb
        have h := (realize_closeAll _).mp (hax (.backAx k ℓ)) (Fin.snoc (evalTuple ms m ns n) b.1)
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, FirstOrder.Language.BoundedFormula.realize_inf,
          realize_bf1, realize_bf2,
          FirstOrder.Language.BoundedFormula.realize_ex] at h
        obtain ⟨a0, ⟨⟨haU, haR⟩, haJ⟩⟩ := h ⟨⟨hJ_lift ms m ns n b.1 hℓ, by
          simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
          exact b.2⟩, by
          rw [realize_liftTerm1, hstdM']
          simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
          exact (hacc2 n b).mp hb⟩
        simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last] at haU
        refine ⟨⟨a0, haU⟩, ?_, ℓ + 1, ?_⟩
        · rw [realize_liftTerm1, realize_liftTerm1, hstdM] at haR
          simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last] at haR
          exact (hacc1 m ⟨a0, haU⟩).mpr haR
        · simp only [realize_jAtom] at haJ
          refine Eq.mp (congrArg (FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (iPred k (ℓ + 1)))
            (funext fun idx => ?_)) haJ
          unfold tupleTerms
          split_ifs with h1 h2 h3
          · rw [realize_liftTerm1, realize_liftTerm1, hstdMs, heval1 _ _ _ _ _ h1]
          · rw [heval2 _ _ _ _ _ h1 h2]
            simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
          · rw [realize_liftTerm1, realize_liftTerm1, hstdNs, heval3 _ _ _ _ _ h1 h2 h3]
          · rw [realize_liftTerm1, heval4 _ _ _ _ _ h1 h2 h3]
            simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
      nom := by
        rintro hnom k ms m ns n ⟨ℓ, hℓ⟩ s
        have h := (realize_closeAll _).mp (hax (.nomAx k ℓ s hnom)) (evalTuple ms m ns n)
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, FirstOrder.Language.BoundedFormula.realize_iff,
          FirstOrder.Language.BoundedFormula.realize_bdEqual, hB_jAtom] at h
        have h' := h hℓ
        rw [hstdM, hstdM'] at h'
        have hc1 : (FirstOrder.Language.Term.func (L := extLang P N) (l := 0) (nomConst false s) Fin.elim0).realize
            (Sum.elim Empty.elim (evalTuple ms m ns n)) = (nomVal (P := P) (N := N) (M := N₁) s).1 :=
          congrArg (FirstOrder.Language.Structure.funMap (L := extLang P N) (M := M4) (n := 0) (nomConst false s))
            (funext fun i => Fin.elim0 i)
        have hc2 : (FirstOrder.Language.Term.func (L := extLang P N) (l := 0) (nomConst true s) Fin.elim0).realize
            (Sum.elim Empty.elim (evalTuple ms m ns n)) = (nomVal (P := P) (N := N) (M := N₂) s).1 :=
          congrArg (FirstOrder.Language.Structure.funMap (L := extLang P N) (M := M4) (n := 0) (nomConst true s))
            (funext fun i => Fin.elim0 i)
        rw [hc1, hc2] at h'
        rw [Subtype.ext_iff, Subtype.ext_iff]
        exact h'
      ext := by
        rintro hBE k ms m ns n ⟨ℓ, hℓ⟩
        have h := (realize_closeAll _).mp (hax (.extAx k ℓ hBE)) (evalTuple ms m ns n)
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, hB_jAtom] at h
        have h' := h hℓ
        refine ⟨ℓ + 1, ?_⟩
        simp only [realize_jAtom] at h'
        refine Eq.mp (congrArg (FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (iPred (k + 1) (ℓ + 1)))
          (funext fun idx => ?_)) h'
        unfold tupleTerms
        split_ifs with h1 h2 h3
        · rw [heval1 _ _ _ _ _ h1]
          by_cases hlt : idx.val < k
          · have hidx : (⟨idx.val, h1⟩ : Fin (k + 1)) = Fin.castSucc ⟨idx.val, hlt⟩ := rfl
            rw [hidx, Fin.snoc_castSucc, Fin.snoc_castSucc, hstdMs]
          · have hidx : (⟨idx.val, h1⟩ : Fin (k + 1)) = Fin.last k := Fin.ext (by dsimp; omega)
            rw [hidx, Fin.snoc_last, Fin.snoc_last, hstdM]
        · rw [hstdM, heval2 _ _ _ _ _ h1 h2]
        · rw [heval3 _ _ _ _ _ h1 h2 h3]
          by_cases hlt : idx.val - (k + 1 + 1) < k
          · have hidx : (⟨idx.val - (k + 1 + 1), by omega⟩ : Fin (k + 1)) =
                Fin.castSucc ⟨idx.val - (k + 1 + 1), hlt⟩ := rfl
            rw [hidx, Fin.snoc_castSucc, Fin.snoc_castSucc, hstdNs]
          · have hidx : (⟨idx.val - (k + 1 + 1), by omega⟩ : Fin (k + 1)) = Fin.last k := Fin.ext (by dsimp; omega)
            rw [hidx, Fin.snoc_last, Fin.snoc_last, hstdM']
        · rw [hstdM', heval4 _ _ _ _ _ h1 h2 h3]
      bind := by
        rintro hb k ms m ns n ⟨ℓ, hℓ⟩ j
        have h := (realize_closeAll _).mp (hax (.bindAx k ℓ j hb)) (evalTuple ms m ns n)
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, hB_jAtom] at h
        have h' := h hℓ
        refine ⟨ℓ + 1, ?_⟩
        simp only [realize_jAtom] at h'
        refine Eq.mp (congrArg (FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (iPred k (ℓ + 1)))
          (funext fun idx => ?_)) h'
        unfold tupleTerms
        split_ifs with h1 h2 h3
        · rw [heval1 _ _ _ _ _ h1]
          by_cases heq' : (⟨idx.val, h1⟩ : Fin k) = j
          · rw [heq', Function.update_self, Function.update_self, hstdM]
          · rw [Function.update_of_ne heq', Function.update_of_ne heq', hstdMs]
        · rw [hstdM, heval2 _ _ _ _ _ h1 h2]
        · rw [heval3 _ _ _ _ _ h1 h2 h3]
          by_cases heq' : (⟨idx.val - (k + 1), by omega⟩ : Fin k) = j
          · rw [heq', Function.update_self, Function.update_self, hstdM']
          · rw [Function.update_of_ne heq', Function.update_of_ne heq', hstdNs]
        · rw [hstdM', heval4 _ _ _ _ _ h1 h2 h3]
      atv := by
        rintro hj k ms m ns n ⟨ℓ, hℓ⟩ j
        have h := (realize_closeAll _).mp (hax (.atvAx k ℓ j hj)) (evalTuple ms m ns n)
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, hB_jAtom] at h
        have h' := h hℓ
        refine ⟨ℓ, ?_⟩
        simp only [realize_jAtom] at h'
        refine Eq.mp (congrArg (FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (iPred k ℓ))
          (funext fun idx => ?_)) h'
        unfold tupleTerms
        split_ifs with h1 h2 h3
        · rw [hstdMs, heval1 _ _ _ _ _ h1]
        · rw [hstdMs, heval2 _ _ _ _ _ h1 h2]
        · rw [hstdNs, heval3 _ _ _ _ _ h1 h2 h3]
        · rw [hstdNs, heval4 _ _ _ _ _ h1 h2 h3]
      atn := by
        rintro hj hn k ms m ns n ⟨ℓ, hℓ⟩ s
        have h := (realize_closeAll _).mp (hax (.atnAx k ℓ s hj hn)) (evalTuple ms m ns n)
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, hB_jAtom] at h
        have h' := h hℓ
        refine ⟨ℓ, ?_⟩
        simp only [realize_jAtom] at h'
        refine Eq.mp (congrArg (FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (iPred k ℓ))
          (funext fun idx => ?_)) h'
        unfold tupleTerms
        split_ifs with h1 h2 h3
        · rw [hstdMs, heval1 _ _ _ _ _ h1]
        · rw [heval2 _ _ _ _ _ h1 h2]
          exact congrArg (FirstOrder.Language.Structure.funMap (L := extLang P N) (M := M4) (n := 0) (nomConst false s))
            (funext fun i => Fin.elim0 i)
        · rw [hstdNs, heval3 _ _ _ _ _ h1 h2 h3]
        · rw [heval4 _ _ _ _ _ h1 h2 h3]
          exact congrArg (FirstOrder.Language.Structure.funMap (L := extLang P N) (M := M4) (n := 0) (nomConst true s))
            (funext fun i => Fin.elim0 i)
      ex_forth := by
        rintro he k ms m ns n ⟨ℓ, hℓ⟩ j a
        have h := (realize_closeAll _).mp (hax (.exForthAx k ℓ j he)) (Fin.snoc (evalTuple ms m ns n) a.1)
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, FirstOrder.Language.BoundedFormula.realize_inf,
          realize_bf1, FirstOrder.Language.BoundedFormula.realize_ex] at h
        obtain ⟨b0, hbU, hbJ⟩ := h ⟨hJ_lift ms m ns n a.1 hℓ, by
          simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
          exact a.2⟩
        simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last] at hbU
        refine ⟨⟨b0, hbU⟩, ℓ + 1, ?_⟩
        simp only [realize_jAtom] at hbJ
        refine Eq.mp (congrArg (FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (iPred k (ℓ + 1)))
          (funext fun idx => ?_)) hbJ
        unfold tupleTerms
        split_ifs with h1 h2 h3
        · rw [heval1 _ _ _ _ _ h1]
          by_cases heq' : (⟨idx.val, h1⟩ : Fin k) = j
          · rw [heq', Function.update_self, Function.update_self, realize_liftTerm1]
            simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
          · rw [Function.update_of_ne heq', Function.update_of_ne heq', realize_liftTerm1, realize_liftTerm1, hstdMs]
        · rw [realize_liftTerm1, realize_liftTerm1, hstdM, heval2 _ _ _ _ _ h1 h2]
        · rw [heval3 _ _ _ _ _ h1 h2 h3]
          by_cases heq' : (⟨idx.val - (k + 1), by omega⟩ : Fin k) = j
          · rw [heq', Function.update_self, Function.update_self]
            simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
          · rw [Function.update_of_ne heq', Function.update_of_ne heq', realize_liftTerm1, realize_liftTerm1, hstdNs]
        · rw [realize_liftTerm1, realize_liftTerm1, hstdM', heval4 _ _ _ _ _ h1 h2 h3]
      ex_back := by
        rintro he k ms m ns n ⟨ℓ, hℓ⟩ j b
        have h := (realize_closeAll _).mp (hax (.exBackAx k ℓ j he)) (Fin.snoc (evalTuple ms m ns n) b.1)
        simp only [FirstOrder.Language.BoundedFormula.realize_imp, FirstOrder.Language.BoundedFormula.realize_inf,
          realize_bf1, FirstOrder.Language.BoundedFormula.realize_ex] at h
        obtain ⟨a0, haU, haJ⟩ := h ⟨hJ_lift ms m ns n b.1 hℓ, by
          simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
          exact b.2⟩
        simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last] at haU
        refine ⟨⟨a0, haU⟩, ℓ + 1, ?_⟩
        simp only [realize_jAtom] at haJ
        refine Eq.mp (congrArg (FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (iPred k (ℓ + 1)))
          (funext fun idx => ?_)) haJ
        unfold tupleTerms
        split_ifs with h1 h2 h3
        · rw [heval1 _ _ _ _ _ h1]
          by_cases heq' : (⟨idx.val, h1⟩ : Fin k) = j
          · rw [heq', Function.update_self, Function.update_self]
            simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
          · rw [Function.update_of_ne heq', Function.update_of_ne heq', realize_liftTerm1, realize_liftTerm1, hstdMs]
        · rw [realize_liftTerm1, realize_liftTerm1, hstdM, heval2 _ _ _ _ _ h1 h2]
        · rw [heval3 _ _ _ _ _ h1 h2 h3]
          by_cases heq' : (⟨idx.val - (k + 1), by omega⟩ : Fin k) = j
          · rw [heq', Function.update_self, Function.update_self, realize_liftTerm1]
            simp only [bvar, FirstOrder.Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
          · rw [Function.update_of_ne heq', Function.update_of_ne heq', realize_liftTerm1, realize_liftTerm1, hstdNs]
        · rw [realize_liftTerm1, realize_liftTerm1, hstdM', heval4 _ _ _ _ _ h1 h2 h3] }
  -- Verify `B 0 Fin.elim0 n₁ Fin.elim0 n₂`, `φ.Realize ![n₁]`, and `¬ φ.Realize ![n₂]`
  refine ⟨N₁, N₂, inferInstance, inferInstance, n₁, n₂, ⟨B, hbisim, 0, ?_⟩, ?_, ?_⟩
  · simp only [realize_jAtom] at hI0
    refine Eq.mp (congrArg (FirstOrder.Language.Structure.RelMap (L := extLang P N) (M := M4) (iPred 0 0))
      (funext fun idx => ?_)) hI0
    fin_cases idx
    · simp only [tupleTerms, evalTuple, FirstOrder.Language.Term.realize_var, Sum.elim_inr,
        Fin.isValue, lt_self_iff_false, ↓reduceDIte, n₁]
      exact h0val
    · simp only [tupleTerms, evalTuple, FirstOrder.Language.Term.realize_var, Sum.elim_inr,
        Fin.isValue, Nat.not_lt_zero, one_ne_zero, mul_zero, zero_add,
        lt_self_iff_false, ↓reduceDIte, n₂]
      exact h1val
  · have harg : (Sum.elim (default : Empty → M4) (Fin.snoc (Fin.snoc (default : Fin 0 → M4) x0) y0 ∘ Fin.castAdd 0) ∘
        fun _ : Fin 1 => Sum.inr (0 : Fin 2)) = fun a : Fin 1 => ((![n₁] : Fin 1 → N₁) a).1 := by
      funext i; fin_cases i; rfl
    have h0 : (Fin.snoc (Fin.snoc (default : Fin 0 → M4) x0) y0 ∘ Fin.natAdd 2) =
        fun i : Fin 0 => ((Fin.elim0 : Fin 0 → N₁) i).1 := funext (fun i => Fin.elim0 i)
    rw [harg, h0] at hφx0
    exact (realize_relativize false hnom1 φ ![n₁] Fin.elim0).mp hφx0
  · have harg : (Sum.elim (default : Empty → M4) (Fin.snoc (Fin.snoc (default : Fin 0 → M4) x0) y0 ∘ Fin.castAdd 0) ∘
        fun _ : Fin 1 => Sum.inr (1 : Fin 2)) = fun a : Fin 1 => ((![n₂] : Fin 1 → N₂) a).1 := by
      funext i; fin_cases i; rfl
    have h0 : (Fin.snoc (Fin.snoc (default : Fin 0 → M4) x0) y0 ∘ Fin.natAdd 2) =
        fun i : Fin 0 => ((Fin.elim0 : Fin 0 → N₂) i).1 := funext (fun i => Fin.elim0 i)
    rw [harg, h0] at hφy0
    exact fun h => hφy0 ((realize_relativize true hnom2 φ ![n₂] Fin.elim0).mpr h)

/-! ### Part 5: Main Characterization Theorem (`Theorem 2` of arXiv:2312.14661) -/

/-- Pointed language adding a single constant `none` for the distinguished world to `hybridLang P N`. -/
private def pointedLang (P N : Type) : FirstOrder.Language.{0, 0} where
  Functions
    | 0 => Option N
    | _ + 1 => PEmpty
  Relations
    | 1 => P
    | 2 => Unit
    | _ => PEmpty

private abbrev pointedStruct {P N M : Type} [(hybridLang P N).Structure M] (m : M) :
    (pointedLang P N).Structure M where
  funMap := fun {n} f _ =>
    match n, f with
    | 0, none => m
    | 0, some s => nomVal (P := P) (N := N) s
    | _ + 1, f => PEmpty.elim f
  RelMap := fun {n} r xs =>
    match n, r with
    | 1, p => propVal (P := P) (N := N) p (xs 0)
    | 2, () => accRel (P := P) (N := N) (xs 0) (xs 1)
    | 0, r => PEmpty.elim r
    | _ + 3, r => PEmpty.elim r

private abbrev unpointStruct {P N M : Type} [(pointedLang P N).Structure M] :
    (hybridLang P N).Structure M where
  funMap := fun {n} f _ =>
    match n, f with
    | 0, s => FirstOrder.Language.Structure.funMap (L := pointedLang P N) (n := 0) (some s) Fin.elim0
    | _ + 1, f => PEmpty.elim f
  RelMap := fun {n} r xs =>
    match n, r with
    | 1, p => FirstOrder.Language.Structure.RelMap (L := pointedLang P N) (n := 1) p xs
    | 2, () => FirstOrder.Language.Structure.RelMap (L := pointedLang P N) (n := 2) () xs
    | 0, r => PEmpty.elim r
    | _ + 3, r => PEmpty.elim r

private def ptWorld {P N M : Type} [(pointedLang P N).Structure M] : M :=
  FirstOrder.Language.Structure.funMap (L := pointedLang P N) (n := 0) none Fin.elim0

private def mapTermPointed {P N : Type} {n : ℕ} :
    (hybridLang P N).Term (Fin 1 ⊕ Fin n) → (pointedLang P N).Term (Empty ⊕ Fin n)
  | .var (Sum.inl _) => FirstOrder.Language.Term.func (L := pointedLang P N) (l := 0) none Fin.elim0
  | .var (Sum.inr i) => .var (Sum.inr i)
  | @FirstOrder.Language.Term.func _ _ 0 s _ =>
      FirstOrder.Language.Term.func (L := pointedLang P N) (l := 0) (some s) Fin.elim0
  | @FirstOrder.Language.Term.func _ _ (_ + 1) f _ => PEmpty.elim f

private def toPointedBounded {P N : Type} :
    ∀ {n : ℕ}, (hybridLang P N).BoundedFormula (Fin 1) n → (pointedLang P N).BoundedFormula Empty n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (mapTermPointed t₁) (mapTermPointed t₂)
  | _, @FirstOrder.Language.BoundedFormula.rel _ _ _ 0 r _ => PEmpty.elim r
  | _, @FirstOrder.Language.BoundedFormula.rel _ _ _ 1 p ts =>
      FirstOrder.Language.BoundedFormula.rel (L := pointedLang P N) (l := 1) p (fun i => mapTermPointed (ts i))
  | _, @FirstOrder.Language.BoundedFormula.rel _ _ _ 2 () ts =>
      FirstOrder.Language.BoundedFormula.rel (L := pointedLang P N) (l := 2) () (fun i => mapTermPointed (ts i))
  | _, @FirstOrder.Language.BoundedFormula.rel _ _ _ (_ + 3) r _ => PEmpty.elim r
  | _, .imp f₁ f₂ => .imp (toPointedBounded f₁) (toPointedBounded f₂)
  | _, .all f => .all (toPointedBounded f)

private def toPointedSentence {P N : Type} (φ : (hybridLang P N).Formula (Fin 1)) :
    (pointedLang P N).Sentence :=
  toPointedBounded φ

private lemma realize_mapTermPointed {P N M : Type} [(pointedLang P N).Structure M] {n : ℕ}
    (t : (hybridLang P N).Term (Fin 1 ⊕ Fin n)) (xs : Fin n → M) :
    (mapTermPointed t).realize (Sum.elim Empty.elim xs) =
      @FirstOrder.Language.Term.realize (hybridLang P N) M unpointStruct _
        (Sum.elim ![ptWorld (P := P) (N := N)] xs) t := by
  induction t with
  | var x =>
    rcases x with i | j
    · fin_cases i
      change FirstOrder.Language.Structure.funMap (L := pointedLang P N) (n := 0) none
          (fun k : Fin 0 => FirstOrder.Language.Term.realize (L := pointedLang P N) (Sum.elim Empty.elim xs) (Fin.elim0 k)) =
        FirstOrder.Language.Structure.funMap (L := pointedLang P N) (n := 0) none Fin.elim0
      have h0 : (fun k : Fin 0 => FirstOrder.Language.Term.realize (L := pointedLang P N) (Sum.elim Empty.elim xs) (Fin.elim0 k)) =
          Fin.elim0 := funext (fun k => Fin.elim0 k)
      rw [h0]
    · rfl
  | @func l f ts _ =>
    cases l with
    | zero =>
      change FirstOrder.Language.Structure.funMap (L := pointedLang P N) (n := 0) (some f)
          (fun k : Fin 0 => FirstOrder.Language.Term.realize (L := pointedLang P N) (Sum.elim Empty.elim xs) (Fin.elim0 k)) =
        FirstOrder.Language.Structure.funMap (L := pointedLang P N) (n := 0) (some f) Fin.elim0
      have h0 : (fun k : Fin 0 => FirstOrder.Language.Term.realize (L := pointedLang P N) (Sum.elim Empty.elim xs) (Fin.elim0 k)) =
          Fin.elim0 := funext (fun k => Fin.elim0 k)
      rw [h0]
    | succ _ => exact PEmpty.elim f

private lemma realize_toPointedBounded {P N M : Type} [(pointedLang P N).Structure M] :
    ∀ {n : ℕ} (φ : (hybridLang P N).BoundedFormula (Fin 1) n) (xs : Fin n → M),
      (toPointedBounded φ).Realize Empty.elim xs ↔
        @FirstOrder.Language.BoundedFormula.Realize (hybridLang P N) M unpointStruct _ _
          φ ![ptWorld (P := P) (N := N)] xs := by
  intro n φ
  induction φ with
  | falsum => intro _; rfl
  | equal t₁ t₂ =>
    intro xs
    simp only [toPointedBounded, FirstOrder.Language.BoundedFormula.Realize, realize_mapTermPointed]
  | @rel l n' r ts =>
    intro xs
    match n', r with
    | 0, r => exact PEmpty.elim r
    | 1, p =>
      simp only [toPointedBounded, FirstOrder.Language.BoundedFormula.Realize, realize_mapTermPointed]
      rfl
    | 2, () =>
      simp only [toPointedBounded, FirstOrder.Language.BoundedFormula.Realize, realize_mapTermPointed]
      rfl
    | _ + 3, r => exact PEmpty.elim r
  | imp f₁ f₂ ih1 ih2 =>
    intro xs
    simp only [toPointedBounded, FirstOrder.Language.BoundedFormula.Realize, ih1, ih2]
  | all f ih =>
    intro xs
    simp only [toPointedBounded, FirstOrder.Language.BoundedFormula.Realize]
    exact forall_congr' (fun a => ih (Fin.snoc xs a))

private lemma realize_toPointedSentence_unpoint {P N M : Type} [(pointedLang P N).Structure M]
    (φ : (hybridLang P N).Formula (Fin 1)) :
    (toPointedSentence φ).Realize M ↔
      @FirstOrder.Language.Formula.Realize (hybridLang P N) M unpointStruct _ φ ![ptWorld (P := P) (N := N)] := by
  simp only [toPointedSentence, FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize]
  have hE : (default : Empty → M) = Empty.elim := funext (fun e => Empty.elim e)
  have h0 : (default : Fin 0 → M) = Fin.elim0 := funext (fun i => Fin.elim0 i)
  rw [hE, h0]
  exact realize_toPointedBounded φ Fin.elim0

private lemma realize_toPointedSentence {P N M : Type} [(hybridLang P N).Structure M]
    (m : M) (φ : (hybridLang P N).Formula (Fin 1)) :
    @FirstOrder.Language.Sentence.Realize (pointedLang P N) M (pointedStruct m) (toPointedSentence φ) ↔
      φ.Realize ![m] := by
  let _ : (pointedLang P N).Structure M := pointedStruct m
  have h1 := realize_toPointedSentence_unpoint (P := P) (N := N) (M := M) φ
  have hstruct : @unpointStruct P N M (pointedStruct m) = ‹(hybridLang P N).Structure M› := by
    ext l f xs
    · cases l with
      | zero =>
        change nomVal (P := P) (N := N) f = _
        have : xs = Fin.elim0 := funext (fun i => Fin.elim0 i)
        rw [this]; rfl
      | succ _ => exact PEmpty.elim f
    · match l, f with
      | 0, r => exact PEmpty.elim r
      | 1, p =>
        change FirstOrder.Language.Structure.RelMap (L := hybridLang P N) (n := 1) p ![xs 0] ↔ _
        have : ![xs 0] = xs := by funext i; fin_cases i; rfl
        rw [this]
      | 2, () =>
        change FirstOrder.Language.Structure.RelMap (L := hybridLang P N) (n := 2) () ![xs 0, xs 1] ↔ _
        have : ![xs 0, xs 1] = xs := by funext i; fin_cases i <;> rfl
        rw [this]
      | _ + 3, r => exact PEmpty.elim r
  rw [hstruct] at h1
  exact h1

theorem main_proof :
    ∀ (P N : Type) [Fintype P] [Fintype N] (F : HybridFeatures)
      (φ : (hybridLang P N).Formula (Fin 1)),
      (∃ ψ : HybridFormula P N 0, UsesFeatures F ψ ∧
        ∀ (M : Type) [(hybridLang P N).Structure M] (m : M),
          φ.Realize ![m] ↔ HybridSat Fin.elim0 m ψ) ↔
      IsFOmegaBisimInvariant F φ := by
  intro P N _ _ F φ
  constructor
  · rintro ⟨ψ, hF, hequiv⟩ M M' _ _ m m' ⟨B, hB, h0⟩
    rw [hequiv M m, hequiv M' m']
    exact hybridSat_iff_of_bisim hB ψ hF h0
  · intro hinv
    -- Step 1: For every pointed model `(M, m)` satisfying `φ(m)`, compactness yields a single
    -- hybrid `F`-sentence `ψ` satisfied at `(M, m)` that entails `φ` in all pointed models!
    have hlocal : ∀ (M : Type) [(hybridLang P N).Structure M] (m : M),
        φ.Realize ![m] →
        ∃ ψ : HybridFormula P N 0, UsesFeatures F ψ ∧
          HybridSat Fin.elim0 m ψ ∧
          ∀ (M' : Type) [(hybridLang P N).Structure M'] (m' : M'),
            HybridSat Fin.elim0 m' ψ → φ.Realize ![m'] := by
      intro M _ m hφm
      let T : (pointedLang P N).Theory :=
        { s | ∃ ψ : HybridFormula P N 0, UsesFeatures F ψ ∧ HybridSat Fin.elim0 m ψ ∧
              s = toPointedSentence (stdTrans ψ) } ∪
        { (toPointedSentence φ).not }
      have hunsat : ¬ T.IsSatisfiable := by
        rintro ⟨M'⟩
        let _ : (hybridLang P N).Structure M' := unpointStruct
        let m' : M' := ptWorld (P := P) (N := N)
        have hsat_φ : ¬ φ.Realize ![m'] := by
          have h := FirstOrder.Language.Theory.realize_sentence_of_mem T
            (Set.mem_union_right _ (Set.mem_singleton _)) (M := M')
          rw [FirstOrder.Language.Sentence.realize_not] at h
          exact fun h1 => h ((realize_toPointedSentence_unpoint φ).mpr h1)
        have heq_m : ∀ ψ : HybridFormula P N 0, UsesFeatures F ψ →
            (HybridSat Fin.elim0 m ψ ↔ HybridSat Fin.elim0 m' ψ) := by
          intro ψ hF
          constructor
          · intro hs
            have h := FirstOrder.Language.Theory.realize_sentence_of_mem T
              (Set.mem_union_left _ ⟨ψ, hF, hs, rfl⟩) (M := M')
            exact (realize_stdTrans ψ m').mp ((realize_toPointedSentence_unpoint (stdTrans ψ)).mp h)
          · intro hs'
            by_contra hns
            have h := FirstOrder.Language.Theory.realize_sentence_of_mem T
              (Set.mem_union_left _ ⟨.neg ψ, hF, hns, rfl⟩) (M := M')
            exact ((realize_stdTrans (.neg ψ) m').mp
              ((realize_toPointedSentence_unpoint (stdTrans (.neg ψ))).mp h)) hs'
        obtain ⟨N₁, N₂, _, _, n₁, n₂, hbis, h1, h2⟩ :=
          lindstrom_theorem m m' hφm hsat_φ heq_m
        exact h2 ((hinv N₁ N₂ n₁ n₂ hbis).mp h1)
      have hnotfin : ¬ T.IsFinitelySatisfiable :=
        fun hf => hunsat (FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr hf)
      unfold FirstOrder.Language.Theory.IsFinitelySatisfiable at hnotfin
      push Not at hnotfin
      obtain ⟨T0, hT0_sub, hT0_unsat⟩ := hnotfin
      classical
      let S0 := T0.filter (fun s => ∃ ψ : HybridFormula P N 0, UsesFeatures F ψ ∧
        HybridSat Fin.elim0 m ψ ∧ s = toPointedSentence (stdTrans ψ))
      have hS0 : ∀ s ∈ S0, ∃ ψ : HybridFormula P N 0, UsesFeatures F ψ ∧
          HybridSat Fin.elim0 m ψ ∧ s = toPointedSentence (stdTrans ψ) :=
        fun s hs => (Finset.mem_filter.mp hs).2
      let l : List (HybridFormula P N 0) := S0.attach.toList.map (fun x => (hS0 x.1 x.2).choose)
      refine ⟨hBigAnd l, usesFeatures_hBigAnd (fun ψ hψ => ?_),
        (hybridSat_hBigAnd _ _ _).mpr (fun ψ hψ => ?_), ?_⟩
      · simp only [l, List.mem_map] at hψ
        rcases hψ with ⟨x, _, rfl⟩
        exact (hS0 x.1 x.2).choose_spec.1
      · simp only [l, List.mem_map] at hψ
        rcases hψ with ⟨x, _, rfl⟩
        exact (hS0 x.1 x.2).choose_spec.2.1
      · intro M' _ m' hsat
        by_contra hnotφ
        apply hT0_unsat
        let _ : (pointedLang P N).Structure M' := pointedStruct m'
        have _ : Nonempty M' := ⟨m'⟩
        have hmod : M' ⊨ (T0 : (pointedLang P N).Theory) := by
          refine ⟨fun s hs => ?_⟩
          rcases hT0_sub hs with hleft | hright
          · have hsS0 : s ∈ S0 := Finset.mem_filter.mpr ⟨hs, hleft⟩
            have hψ_mem : (hS0 s hsS0).choose ∈ l :=
              List.mem_map.mpr ⟨⟨s, hsS0⟩, Finset.mem_toList.mpr (Finset.mem_attach _ _), rfl⟩
            have hψ_sat := (hybridSat_hBigAnd _ _ _).mp hsat _ hψ_mem
            rw [(hS0 s hsS0).choose_spec.2.2]
            exact (realize_toPointedSentence m' _).mpr ((realize_stdTrans _ m').mpr hψ_sat)
          · rw [Set.mem_singleton_iff.mp hright, FirstOrder.Language.Sentence.realize_not]
            exact fun h => hnotφ ((realize_toPointedSentence m' φ).mp h)
        exact FirstOrder.Language.Theory.Model.isSatisfiable M'
    -- Step 2: Second compactness step covering all models of `φ` by finitely many local sentences!
    let Good : Set (HybridFormula P N 0) :=
      { ψ | UsesFeatures F ψ ∧ ∀ (M' : Type) [(hybridLang P N).Structure M'] (m' : M'),
        HybridSat Fin.elim0 m' ψ → φ.Realize ![m'] }
    let T2 : (pointedLang P N).Theory :=
      { toPointedSentence φ } ∪ { s | ∃ ψ ∈ Good, s = (toPointedSentence (stdTrans ψ)).not }
    have hunsat2 : ¬ T2.IsSatisfiable := by
      rintro ⟨M'⟩
      let _ : (hybridLang P N).Structure M' := unpointStruct
      let m' : M' := ptWorld (P := P) (N := N)
      have hφm' : φ.Realize ![m'] := by
        have h := FirstOrder.Language.Theory.realize_sentence_of_mem T2
          (Set.mem_union_left _ (Set.mem_singleton _)) (M := M')
        exact (realize_toPointedSentence_unpoint φ).mp h
      obtain ⟨ψ, hF, hsat, hent⟩ := hlocal M' m' hφm'
      have hneg := FirstOrder.Language.Theory.realize_sentence_of_mem T2
        (Set.mem_union_right _ ⟨ψ, ⟨hF, hent⟩, rfl⟩) (M := M')
      rw [FirstOrder.Language.Sentence.realize_not] at hneg
      exact hneg ((realize_toPointedSentence_unpoint (stdTrans ψ)).mpr ((realize_stdTrans ψ m').mpr hsat))
    have hnotfin2 : ¬ T2.IsFinitelySatisfiable :=
      fun hf => hunsat2 (FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr hf)
    unfold FirstOrder.Language.Theory.IsFinitelySatisfiable at hnotfin2
    push Not at hnotfin2
    obtain ⟨T0, hT0_sub, hT0_unsat⟩ := hnotfin2
    classical
    let S0 := T0.filter (fun s => ∃ ψ ∈ Good, s = (toPointedSentence (stdTrans ψ)).not)
    have hS0 : ∀ s ∈ S0, ∃ ψ ∈ Good, s = (toPointedSentence (stdTrans ψ)).not :=
      fun s hs => (Finset.mem_filter.mp hs).2
    let l : List (HybridFormula P N 0) := S0.attach.toList.map (fun x => (hS0 x.1 x.2).choose)
    refine ⟨hBigOr l, usesFeatures_hBigOr (fun ψ hψ => ?_), fun M _ m => ?_⟩
    · simp only [l, List.mem_map] at hψ
      rcases hψ with ⟨x, _, rfl⟩
      exact (hS0 x.1 x.2).choose_spec.1.1
    · constructor
      · intro hφm
        by_contra hnotor
        apply hT0_unsat
        let _ : (pointedLang P N).Structure M := pointedStruct m
        have _ : Nonempty M := ⟨m⟩
        have hmod : M ⊨ (T0 : (pointedLang P N).Theory) := by
          refine ⟨fun s hs => ?_⟩
          rcases hT0_sub hs with hleft | hright
          · rw [Set.mem_singleton_iff.mp hleft]
            exact (realize_toPointedSentence m φ).mpr hφm
          · have hsS0 : s ∈ S0 := Finset.mem_filter.mpr ⟨hs, hright⟩
            have hψ_mem : (hS0 s hsS0).choose ∈ l :=
              List.mem_map.mpr ⟨⟨s, hsS0⟩, Finset.mem_toList.mpr (Finset.mem_attach _ _), rfl⟩
            rw [(hS0 s hsS0).choose_spec.2, FirstOrder.Language.Sentence.realize_not]
            intro hsat
            exact hnotor ((hybridSat_hBigOr _ _ _).mpr ⟨_, hψ_mem,
              (realize_stdTrans _ m).mp ((realize_toPointedSentence m _).mp hsat)⟩)
        exact FirstOrder.Language.Theory.Model.isSatisfiable M
      · intro hor
        obtain ⟨ψ, hψ_mem, hψ_sat⟩ := (hybridSat_hBigOr _ _ _).mp hor
        simp only [l, List.mem_map] at hψ_mem
        rcases hψ_mem with ⟨x, _, rfl⟩
        exact (hS0 x.1 x.2).choose_spec.1.2 M m hψ_sat

end OMA.P_arxiv_2312_14661

theorem OMA.solution : type_of% @OMA.S_arxiv_2312_14661.main :=
  OMA.P_arxiv_2312_14661.main_proof
