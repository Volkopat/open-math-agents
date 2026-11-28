import OMAStatements.S_oeis_a264273
import Mathlib.Tactic

/-!
# Proof of OEIS A264273

We prove that the number `a n` of permutations of `Fin 3 × Fin (n + 1)` moving each cell
by `(0, 0)`, `±(1, 0)`, or `±(1, 2)` satisfies `a n = 256 * 5 ^ (n - 3)` for `n > 2` and
has generating series `X * (9 + 3 * X + 16 * X ^ 2) / (1 - 5 * X)`.

1. **Column-parity split**: every allowed move preserves column parity, so `Cell n` splits
   into two independent boards of widths `n / 2 + 1` and `(n + 1) / 2` with adjacent-column
   moves `±(1, 0)` and `±(1, 1)`, yielding `a n = F (n / 2 + 1) * F ((n + 1) / 2)`.
2. **Column-by-column transfer matrix**: partial configurations on `Fin 3 × Fin m` into
   `Fin 3 × Fin (m + 1)` are classified by a 4-bit right-boundary state `(out0, in0, out1, in1)`.
   Peeling off the rightmost column gives an exact bijection
   `Valid (m + 1) ns ≃ Σ s, Valid m s × Step s ns`.
   At `m = 2`, the 16-state count vector is an exact eigenvector of the transfer matrix with
   eigenvalue `5`, giving `F 1 = 3` and `F m = 16 * 5 ^ (m - 2)` for all `m ≥ 2`.
3. **Generating series**: substituting the closed form into the coefficient identity for
   `P * (1 - 5 * X)` finishes the proof.
-/

namespace A264273

open OMA.S_oeis_a264273

abbrev Cell1 (m : ℕ) := Fin 3 × Fin m

def allowed1 {m : ℕ} (u v : Cell1 m) : Prop :=
  u = v ∨
    (v.1.val = u.1.val + 1 ∧ (v.2.val = u.2.val ∨ v.2.val = u.2.val + 1)) ∨
    (u.1.val = v.1.val + 1 ∧ (u.2.val = v.2.val ∨ u.2.val = v.2.val + 1))

noncomputable def F (m : ℕ) : ℕ :=
  Nat.card {p : Equiv.Perm (Cell1 m) // ∀ u, allowed1 u (p u)}

private lemma beq_eq_dec (a b : Fin 3 × Fin 3) :
    (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

/-! ### Part 1: Even/odd column parity split -/

def splitCol (n : ℕ) : Fin (n + 1) ≃ Fin (n / 2 + 1) ⊕ Fin ((n + 1) / 2) where
  toFun c :=
    if h : c.val % 2 = 0 then
      Sum.inl ⟨c.val / 2, by omega⟩
    else
      Sum.inr ⟨c.val / 2, by omega⟩
  invFun
    | Sum.inl k => ⟨2 * k.val, by omega⟩
    | Sum.inr k => ⟨2 * k.val + 1, by omega⟩
  left_inv c := by
    ext
    by_cases h : c.val % 2 = 0 <;> simp [h] <;> omega
  right_inv x := by
    rcases x with k | k
    · simp only [Nat.mul_mod_right, ↓reduceDIte, Sum.inl.injEq]
      ext
      simp
    · simp only [Nat.mul_add_mod_self_left, Nat.one_mod, one_ne_zero, ↓reduceDIte, Sum.inr.injEq]
      ext
      simp
      omega

def splitCell (n : ℕ) : Cell n ≃ Cell1 (n / 2 + 1) ⊕ Cell1 ((n + 1) / 2) :=
  (Equiv.prodCongr (Equiv.refl (Fin 3)) (splitCol n)).trans (Equiv.prodSumDistrib _ _ _)

private lemma splitCell_symm_inl (n : ℕ) (u : Cell1 (n / 2 + 1)) :
    (splitCell n).symm (Sum.inl u) = (u.1, ⟨2 * u.2.val, by omega⟩) := rfl

private lemma splitCell_symm_inr (n : ℕ) (u : Cell1 ((n + 1) / 2)) :
    (splitCell n).symm (Sum.inr u) = (u.1, ⟨2 * u.2.val + 1, by omega⟩) := rfl

private lemma allowed_inl_inl {n : ℕ} (u v : Cell1 (n / 2 + 1)) :
    allowed ((splitCell n).symm (Sum.inl u)) ((splitCell n).symm (Sum.inl v)) ↔ allowed1 u v := by
  rcases u with ⟨r1, c1⟩
  rcases v with ⟨r2, c2⟩
  simp only [splitCell_symm_inl, allowed, allowed1, Prod.mk.injEq, Fin.ext_iff]
  omega

private lemma allowed_inr_inr {n : ℕ} (u v : Cell1 ((n + 1) / 2)) :
    allowed ((splitCell n).symm (Sum.inr u)) ((splitCell n).symm (Sum.inr v)) ↔ allowed1 u v := by
  rcases u with ⟨r1, c1⟩
  rcases v with ⟨r2, c2⟩
  simp only [splitCell_symm_inr, allowed, allowed1, Prod.mk.injEq, Fin.ext_iff]
  omega

private lemma not_allowed_inl_inr {n : ℕ} (u : Cell1 (n / 2 + 1)) (v : Cell1 ((n + 1) / 2)) :
    ¬ allowed ((splitCell n).symm (Sum.inl u)) ((splitCell n).symm (Sum.inr v)) := by
  rcases u with ⟨r1, c1⟩
  rcases v with ⟨r2, c2⟩
  simp only [splitCell_symm_inl, splitCell_symm_inr, allowed, Prod.mk.injEq, Fin.ext_iff]
  omega

private lemma not_allowed_inr_inl {n : ℕ} (u : Cell1 ((n + 1) / 2)) (v : Cell1 (n / 2 + 1)) :
    ¬ allowed ((splitCell n).symm (Sum.inr u)) ((splitCell n).symm (Sum.inl v)) := by
  rcases u with ⟨r1, c1⟩
  rcases v with ⟨r2, c2⟩
  simp only [splitCell_symm_inl, splitCell_symm_inr, allowed, Prod.mk.injEq, Fin.ext_iff]
  omega

private lemma conj_inl {n : ℕ} {p : Equiv.Perm (Cell n)} (hp : ∀ u, allowed u (p u))
    (u : Cell1 (n / 2 + 1)) :
    ∃ v, ((splitCell n).symm.trans (p.trans (splitCell n))) (Sum.inl u) = Sum.inl v := by
  cases h : ((splitCell n).symm.trans (p.trans (splitCell n))) (Sum.inl u) with
  | inl v => exact ⟨v, rfl⟩
  | inr v =>
    have h1 := hp ((splitCell n).symm (Sum.inl u))
    have h2 : p ((splitCell n).symm (Sum.inl u)) = (splitCell n).symm (Sum.inr v) := by
      have := congrArg (splitCell n).symm h
      simpa using this
    rw [h2] at h1
    exact absurd h1 (not_allowed_inl_inr u v)

private lemma conj_inr {n : ℕ} {p : Equiv.Perm (Cell n)} (hp : ∀ u, allowed u (p u))
    (u : Cell1 ((n + 1) / 2)) :
    ∃ v, ((splitCell n).symm.trans (p.trans (splitCell n))) (Sum.inr u) = Sum.inr v := by
  cases h : ((splitCell n).symm.trans (p.trans (splitCell n))) (Sum.inr u) with
  | inr v => exact ⟨v, rfl⟩
  | inl v =>
    have h1 := hp ((splitCell n).symm (Sum.inr u))
    have h2 : p ((splitCell n).symm (Sum.inr u)) = (splitCell n).symm (Sum.inl v) := by
      have := congrArg (splitCell n).symm h
      simpa using this
    rw [h2] at h1
    exact absurd h1 (not_allowed_inr_inl u v)

private lemma conj_symm_inl {n : ℕ} {p : Equiv.Perm (Cell n)} (hp : ∀ u, allowed u (p u))
    (u : Cell1 (n / 2 + 1)) :
    ∃ v, ((splitCell n).symm.trans (p.trans (splitCell n))).symm (Sum.inl u) = Sum.inl v := by
  set q := (splitCell n).symm.trans (p.trans (splitCell n))
  cases h : q.symm (Sum.inl u) with
  | inl v => exact ⟨v, rfl⟩
  | inr v =>
    obtain ⟨w, hw⟩ := conj_inr hp v
    have h1 := congrArg q h
    rw [Equiv.apply_symm_apply] at h1
    rw [hw] at h1
    exact absurd h1 (by simp)

private lemma conj_symm_inr {n : ℕ} {p : Equiv.Perm (Cell n)} (hp : ∀ u, allowed u (p u))
    (u : Cell1 ((n + 1) / 2)) :
    ∃ v, ((splitCell n).symm.trans (p.trans (splitCell n))).symm (Sum.inr u) = Sum.inr v := by
  set q := (splitCell n).symm.trans (p.trans (splitCell n))
  cases h : q.symm (Sum.inr u) with
  | inr v => exact ⟨v, rfl⟩
  | inl v =>
    obtain ⟨w, hw⟩ := conj_inl hp v
    have h1 := congrArg q h
    rw [Equiv.apply_symm_apply] at h1
    rw [hw] at h1
    exact absurd h1 (by simp)

private noncomputable def splitPermEven {n : ℕ} (p : Equiv.Perm (Cell n))
    (hp : ∀ u, allowed u (p u)) : Equiv.Perm (Cell1 (n / 2 + 1)) where
  toFun u := (conj_inl hp u).choose
  invFun u := (conj_symm_inl hp u).choose
  left_inv u := by
    set q := (splitCell n).symm.trans (p.trans (splitCell n))
    have h1 := (conj_inl hp u).choose_spec
    have h2 := (conj_symm_inl hp (conj_inl hp u).choose).choose_spec
    have h3 : q.symm (q (Sum.inl u)) = Sum.inl u := q.symm_apply_apply _
    rw [h1, h2] at h3
    exact Sum.inl.inj h3
  right_inv u := by
    set q := (splitCell n).symm.trans (p.trans (splitCell n))
    have h1 := (conj_symm_inl hp u).choose_spec
    have h2 := (conj_inl hp (conj_symm_inl hp u).choose).choose_spec
    have h3 : q (q.symm (Sum.inl u)) = Sum.inl u := q.apply_symm_apply _
    rw [h1, h2] at h3
    exact Sum.inl.inj h3

private noncomputable def splitPermOdd {n : ℕ} (p : Equiv.Perm (Cell n))
    (hp : ∀ u, allowed u (p u)) : Equiv.Perm (Cell1 ((n + 1) / 2)) where
  toFun u := (conj_inr hp u).choose
  invFun u := (conj_symm_inr hp u).choose
  left_inv u := by
    set q := (splitCell n).symm.trans (p.trans (splitCell n))
    have h1 := (conj_inr hp u).choose_spec
    have h2 := (conj_symm_inr hp (conj_inr hp u).choose).choose_spec
    have h3 : q.symm (q (Sum.inr u)) = Sum.inr u := q.symm_apply_apply _
    rw [h1, h2] at h3
    exact Sum.inr.inj h3
  right_inv u := by
    set q := (splitCell n).symm.trans (p.trans (splitCell n))
    have h1 := (conj_symm_inr hp u).choose_spec
    have h2 := (conj_inr hp (conj_symm_inr hp u).choose).choose_spec
    have h3 : q (q.symm (Sum.inr u)) = Sum.inr u := q.apply_symm_apply _
    rw [h1, h2] at h3
    exact Sum.inr.inj h3

private lemma splitPermEven_spec {n : ℕ} {p : Equiv.Perm (Cell n)} (hp : ∀ u, allowed u (p u))
    (u : Cell1 (n / 2 + 1)) :
    p ((splitCell n).symm (Sum.inl u)) = (splitCell n).symm (Sum.inl (splitPermEven p hp u)) := by
  have h := congrArg (splitCell n).symm (conj_inl hp u).choose_spec
  simpa [splitPermEven] using h

private lemma splitPermOdd_spec {n : ℕ} {p : Equiv.Perm (Cell n)} (hp : ∀ u, allowed u (p u))
    (u : Cell1 ((n + 1) / 2)) :
    p ((splitCell n).symm (Sum.inr u)) = (splitCell n).symm (Sum.inr (splitPermOdd p hp u)) := by
  have h := congrArg (splitCell n).symm (conj_inr hp u).choose_spec
  simpa [splitPermOdd] using h

private noncomputable def splitPerm (n : ℕ) :
    {p : Equiv.Perm (Cell n) // ∀ u, allowed u (p u)} ≃
      {p : Equiv.Perm (Cell1 (n / 2 + 1)) // ∀ u, allowed1 u (p u)} ×
      {p : Equiv.Perm (Cell1 ((n + 1) / 2)) // ∀ u, allowed1 u (p u)} where
  toFun := fun ⟨p, hp⟩ =>
    (⟨splitPermEven p hp, fun u => by
        have h1 := hp ((splitCell n).symm (Sum.inl u))
        rw [splitPermEven_spec hp u] at h1
        exact (allowed_inl_inl u _).mp h1⟩,
     ⟨splitPermOdd p hp, fun u => by
        have h1 := hp ((splitCell n).symm (Sum.inr u))
        rw [splitPermOdd_spec hp u] at h1
        exact (allowed_inr_inr u _).mp h1⟩)
  invFun := fun ⟨⟨pE, hpE⟩, ⟨pO, hpO⟩⟩ =>
    ⟨(splitCell n).trans ((Equiv.sumCongr pE pO).trans (splitCell n).symm), fun u => by
      cases h : splitCell n u with
      | inl x =>
        have hu : u = (splitCell n).symm (Sum.inl x) := by rw [← h, Equiv.symm_apply_apply]
        rw [hu]
        simpa using (allowed_inl_inl x (pE x)).mpr (hpE x)
      | inr x =>
        have hu : u = (splitCell n).symm (Sum.inr x) := by rw [← h, Equiv.symm_apply_apply]
        rw [hu]
        simpa using (allowed_inr_inr x (pO x)).mpr (hpO x)⟩
  left_inv := fun ⟨p, hp⟩ => by
    apply Subtype.ext
    apply Equiv.ext
    intro u
    cases h : splitCell n u with
    | inl x =>
      have hu : u = (splitCell n).symm (Sum.inl x) := by rw [← h, Equiv.symm_apply_apply]
      rw [hu]
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inl]
      exact (splitPermEven_spec hp x).symm
    | inr x =>
      have hu : u = (splitCell n).symm (Sum.inr x) := by rw [← h, Equiv.symm_apply_apply]
      rw [hu]
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inr]
      exact (splitPermOdd_spec hp x).symm
  right_inv := fun ⟨⟨pE, hpE⟩, ⟨pO, hpO⟩⟩ => by
    refine Prod.ext (Subtype.ext (Equiv.ext fun u => ?_)) (Subtype.ext (Equiv.ext fun u => ?_))
    · have hspec := splitPermEven_spec
        (p := (splitCell n).trans ((Equiv.sumCongr pE pO).trans (splitCell n).symm))
        (fun w => by
          cases h : splitCell n w with
          | inl x =>
            have hw : w = (splitCell n).symm (Sum.inl x) := by rw [← h, Equiv.symm_apply_apply]
            rw [hw]; simpa using (allowed_inl_inl x (pE x)).mpr (hpE x)
          | inr x =>
            have hw : w = (splitCell n).symm (Sum.inr x) := by rw [← h, Equiv.symm_apply_apply]
            rw [hw]; simpa using (allowed_inr_inr x (pO x)).mpr (hpO x)) u
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inl] at hspec
      exact Sum.inl.inj ((splitCell n).symm.injective hspec).symm
    · have hspec := splitPermOdd_spec
        (p := (splitCell n).trans ((Equiv.sumCongr pE pO).trans (splitCell n).symm))
        (fun w => by
          cases h : splitCell n w with
          | inl x =>
            have hw : w = (splitCell n).symm (Sum.inl x) := by rw [← h, Equiv.symm_apply_apply]
            rw [hw]; simpa using (allowed_inl_inl x (pE x)).mpr (hpE x)
          | inr x =>
            have hw : w = (splitCell n).symm (Sum.inr x) := by rw [← h, Equiv.symm_apply_apply]
            rw [hw]; simpa using (allowed_inr_inr x (pO x)).mpr (hpO x)) u
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inr] at hspec
      exact Sum.inr.inj ((splitCell n).symm.injective hspec).symm

lemma a_eq_mul (n : ℕ) : a n = F (n / 2 + 1) * F ((n + 1) / 2) := by
  unfold a F
  rw [Nat.card_congr (splitPerm n), Nat.card_prod]

/-! ### Part 2: Column-by-column transfer matrix for `F m` -/

abbrev State := Bool × Bool × Bool × Bool

def ValidPred (m : ℕ) (s : State) (f : Cell1 m → Cell1 (m + 1)) : Prop :=
  Function.Injective f ∧
  (∀ u : Cell1 m, allowed1 (u.1, u.2.castSucc) (f u)) ∧
  (s.1 = true ↔ ∃ u : Cell1 m, f u = (1, Fin.last m)) ∧
  (s.2.2.1 = true ↔ ∃ u : Cell1 m, f u = (2, Fin.last m)) ∧
  (∀ v : Cell1 m, (∃ u : Cell1 m, f u = (v.1, v.2.castSucc)) ↔
    ¬ ((s.2.1 = true ∧ v.1 = 0 ∧ v.2.val + 1 = m) ∨
       (s.2.2.2 = true ∧ v.1 = 1 ∧ v.2.val + 1 = m))) ∧
  (s.2.1 = true → 0 < m) ∧
  (s.2.2.2 = true → 0 < m)

abbrev Valid (m : ℕ) (s : State) := {f : Cell1 m → Cell1 (m + 1) // ValidPred m s f}

noncomputable def cnt (m : ℕ) (s : State) : ℕ := Nat.card (Valid m s)

private lemma allowed1_not_zero_last {m : ℕ} (u : Cell1 m) :
    ¬ allowed1 (u.1, u.2.castSucc) (0, Fin.last m) := by
  simp only [allowed1, Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_last, Fin.val_zero]
  omega

private lemma allowed1_col_le {m : ℕ} {u v : Cell1 m} (h : allowed1 u v) :
    v.2.val ≤ u.2.val + 1 := by
  rcases u with ⟨r1, c1⟩
  rcases v with ⟨r2, c2⟩
  simp only [allowed1, Prod.mk.injEq, Fin.ext_iff] at h
  dsimp only
  omega

private lemma allowed1_castSucc {m : ℕ} (u v : Cell1 m) :
    allowed1 (u.1, u.2.castSucc) (v.1, v.2.castSucc) ↔ allowed1 u v := by
  rcases u with ⟨r1, c1⟩
  rcases v with ⟨r2, c2⟩
  simp only [allowed1, Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc]

lemma F_eq_cnt (m : ℕ) : F m = cnt m (false, false, false, false) := by
  unfold F cnt
  refine Nat.card_congr ?_
  refine
    { toFun := fun ⟨p, hp⟩ =>
        ⟨fun u => ((p u).1, (p u).2.castSucc),
         ⟨fun u1 u2 h => by
            rcases Prod.mk.inj h with ⟨h1, h2⟩
            exact p.injective (Prod.ext h1 (Fin.castSucc_inj.mp h2)),
          fun u => (allowed1_castSucc u (p u)).mpr (hp u),
          by
            simp only [Bool.false_eq_true, false_iff, not_exists]
            intro u h
            have h2 := congrArg (fun x : Cell1 (m + 1) => x.2.val) h
            simp only [Fin.val_castSucc, Fin.val_last] at h2
            omega,
          by
            simp only [Bool.false_eq_true, false_iff, not_exists]
            intro u h
            have h2 := congrArg (fun x : Cell1 (m + 1) => x.2.val) h
            simp only [Fin.val_castSucc, Fin.val_last] at h2
            omega,
          fun v => by
            simp only [Bool.false_eq_true, false_and, or_self, not_false_eq_true, iff_true]
            exact ⟨p.symm v, by simp⟩,
          by simp, by simp⟩⟩
      invFun := fun ⟨f, hinj, hall, hout0, hout1, hcov, _, _⟩ =>
        have hlt : ∀ u : Cell1 m, (f u).2.val < m := by
          intro u
          by_contra hge
          have heq : (f u).2 = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
          have hrow : (f u).1 = 0 ∨ (f u).1 = 1 ∨ (f u).1 = 2 := by
            have := (f u).1.isLt; omega
          rcases hrow with hr0 | hr1 | hr2
          · have hfu : f u = (0, Fin.last m) := Prod.ext hr0 heq
            exact allowed1_not_zero_last u (hfu ▸ hall u)
          · have hfu : f u = (1, Fin.last m) := Prod.ext hr1 heq
            exact Bool.false_ne_true (hout0.mpr ⟨u, hfu⟩)
          · have hfu : f u = (2, Fin.last m) := Prod.ext hr2 heq
            exact Bool.false_ne_true (hout1.mpr ⟨u, hfu⟩)
        let g : Cell1 m → Cell1 m := fun u => ((f u).1, ⟨(f u).2.val, hlt u⟩)
        have hginj : Function.Injective g := fun u1 u2 h => by
          rcases Prod.mk.inj h with ⟨h1, h2⟩
          exact hinj (Prod.ext h1 (Fin.ext (Fin.mk.inj h2)))
        have hgsurj : Function.Surjective g := fun v => by
          obtain ⟨u, hu⟩ := (hcov v).mpr (by simp)
          exact ⟨u, Prod.ext (by simp [g, hu]) (Fin.ext (by simp [g, hu]))⟩
        ⟨Equiv.ofBijective g ⟨hginj, hgsurj⟩, fun u => by
          have h1 := hall u
          have hf_eq : f u = ((g u).1, (g u).2.castSucc) := Prod.ext rfl (Fin.ext rfl)
          rw [hf_eq] at h1
          exact (allowed1_castSucc u (g u)).mp h1⟩
      left_inv := fun ⟨p, hp⟩ => by
        apply Subtype.ext; apply Equiv.ext; intro u; exact Prod.ext rfl (Fin.ext rfl)
      right_inv := fun ⟨f, _, _, _, _, _, _, _⟩ => by
        apply Subtype.ext; funext u; exact Prod.ext rfl (Fin.ext rfl) }

lemma cnt_zero (s : State) : cnt 0 s = if s = (false, false, false, false) then 1 else 0 := by
  by_cases h : s = (false, false, false, false)
  · subst h
    simp only [↓reduceIte, cnt]
    have : Unique (Valid 0 (false, false, false, false)) :=
      { default := ⟨(fun u => nomatch u.2),
          ⟨(fun u => nomatch u.2), (fun u => nomatch u.2),
           by simp, by simp, (fun v => nomatch v.2), by simp, by simp⟩⟩
        uniq := fun ⟨f, _⟩ => by apply Subtype.ext; funext u; exact nomatch u.2 }
    exact Nat.card_unique
  · simp only [h, ↓reduceIte, cnt]
    rcases s with ⟨out0, in0, out1, in1⟩
    have : IsEmpty (Valid 0 (out0, in0, out1, in1)) :=
      ⟨fun ⟨f, _, _, hout0, hout1, _, hin0, hin1⟩ => by
        cases out0
        · cases in0
          · cases out1
            · cases in1
              · exact h rfl
              · exact absurd (hin1 rfl) (by omega)
            · obtain ⟨u, _⟩ := hout1.mp rfl
              exact nomatch u.2
          · exact absurd (hin0 rfl) (by omega)
        · obtain ⟨u, _⟩ := hout0.mp rfl
          exact nomatch u.2⟩
    simp

/-! #### One-column step space -/

def target0 : Fin 3 → Fin 3 × Fin 3
  | 0 => (0, 1)
  | 1 => (1, 1)
  | 2 => (1, 2)

def target1 : Fin 5 → Fin 3 × Fin 3
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)
  | 3 => (2, 1)
  | 4 => (2, 2)

def target2 : Fin 3 → Fin 3 × Fin 3
  | 0 => (1, 0)
  | 1 => (1, 1)
  | 2 => (2, 1)

def targetOf (x : Fin 3 × Fin 5 × Fin 3) : Fin 3 → Fin 3 × Fin 3
  | 0 => target0 x.1
  | 1 => target1 x.2.1
  | 2 => target2 x.2.2

private lemma target0_ne_22 : ∀ i : Fin 3, target0 i ≠ (2, 2) := by decide
private lemma target1_ne_12 : ∀ i : Fin 5, target1 i ≠ (1, 2) := by decide
private lemma target2_ne_12 : ∀ i : Fin 3, target2 i ≠ (1, 2) := by decide
private lemma target2_ne_22 : ∀ i : Fin 3, target2 i ≠ (2, 2) := by decide

def stepValid (s ns : State) (x : Fin 3 × Fin 5 × Fin 3) : Bool :=
  let (out0, in0, out1, in1) := s
  let (nout0, nin0, nout1, nin1) := ns
  let d0 := target0 x.1
  let d1 := target1 x.2.1
  let d2 := target2 x.2.2
  (d0 != d1) && (d0 != d2) && (d1 != d2) &&
  (in0 == (d1 == (0, 0))) &&
  (in1 == (d2 == (1, 0))) &&
  (!out0 || (d0 != (1, 1) && d1 != (1, 1) && d2 != (1, 1))) &&
  (!out1 || (d0 != (2, 1) && d1 != (2, 1) && d2 != (2, 1))) &&
  (nout0 == (d0 == (1, 2))) &&
  (nout1 == (d1 == (2, 2))) &&
  (out1 || (d0 == (2, 1)) || (d1 == (2, 1)) || (d2 == (2, 1))) &&
  (nin0 == !((d0 == (0, 1)) || (d1 == (0, 1)) || (d2 == (0, 1)))) &&
  (nin1 == !(out0 || (d0 == (1, 1)) || (d1 == (1, 1)) || (d2 == (1, 1))))

abbrev Step (s ns : State) := {x : Fin 3 × Fin 5 × Fin 3 // stepValid s ns x = true}

def stepCard (s ns : State) : ℕ :=
  (Finset.univ.filter (fun x : Fin 3 × Fin 5 × Fin 3 => stepValid s ns x = true)).card

def absCell (m : ℕ) (d : Fin 3 × Fin 3) : Cell1 (m + 2) :=
  (d.1, ⟨m + d.2.val - 1, by omega⟩)

private lemma absCell_one (m : ℕ) (r : Fin 3) :
    absCell m (r, 1) = (r, (Fin.last m).castSucc) :=
  Prod.ext rfl (Fin.ext (by simp [absCell]))

private lemma absCell_two (m : ℕ) (r : Fin 3) :
    absCell m (r, 2) = (r, Fin.last (m + 1)) :=
  Prod.ext rfl (Fin.ext (by simp [absCell]))

def extract0 (m : ℕ) (v : Cell1 (m + 2)) : Fin 3 :=
  if v.1.val = 0 then 0 else if v.2.val = m then 1 else 2

def extract1 (m : ℕ) (v : Cell1 (m + 2)) : Fin 5 :=
  if v.1.val = 0 then (if v.2.val = m then 1 else 0)
  else if v.1.val = 1 then 2
  else (if v.2.val = m then 3 else 4)

def extract2 (m : ℕ) (v : Cell1 (m + 2)) : Fin 3 :=
  if v.1.val = 1 then (if v.2.val = m then 1 else 0) else 2

private lemma target0_allowed (m : ℕ) (i : Fin 3) :
    allowed1 (0, (Fin.last m).castSucc) (absCell m (target0 i)) := by
  fin_cases i <;> simp [target0, absCell, allowed1, Fin.ext_iff]

private lemma target1_allowed (m : ℕ) (i : Fin 5) (h : target1 i = (0, 0) → 0 < m) :
    allowed1 (1, (Fin.last m).castSucc) (absCell m (target1 i)) := by
  fin_cases i
  · have hm : 0 < m := h rfl
    simp only [target1, absCell, allowed1, Fin.val_zero, Fin.val_one, Fin.val_castSucc,
      Fin.val_last]
    right; right; exact ⟨by decide, Or.inr (by omega)⟩
  all_goals simp [target1, absCell, allowed1, Fin.ext_iff]

private lemma target2_allowed (m : ℕ) (i : Fin 3) (h : target2 i = (1, 0) → 0 < m) :
    allowed1 (2, (Fin.last m).castSucc) (absCell m (target2 i)) := by
  fin_cases i
  · have hm : 0 < m := h rfl
    simp only [target2, absCell, allowed1, Fin.val_zero, Fin.val_one, Fin.val_two,
      Fin.val_castSucc, Fin.val_last]
    right; right; exact ⟨by decide, Or.inr (by omega)⟩
  all_goals simp [target2, absCell, allowed1, Fin.ext_iff]

private lemma absCell_inj {m : ℕ} {d1 d2 : Fin 3 × Fin 3}
    (h1 : d1.2.val = 0 → 0 < m) (h2 : d2.2.val = 0 → 0 < m)
    (heq : absCell m d1 = absCell m d2) : d1 = d2 := by
  rcases Prod.mk.inj heq with ⟨hr, hc'⟩
  have hc : m + d1.2.val - 1 = m + d2.2.val - 1 := congrArg Fin.val hc'
  refine Prod.ext hr (Fin.ext ?_)
  by_cases h10 : d1.2.val = 0 <;> by_cases h20 : d2.2.val = 0 <;> omega

private lemma target_col0_iff (x : Fin 3 × Fin 5 × Fin 3) :
    ((target0 x.1).2.val = 0 → False) ∧
    ((target1 x.2.1).2.val = 0 → target1 x.2.1 = (0, 0)) ∧
    ((target2 x.2.2).2.val = 0 → target2 x.2.2 = (1, 0)) := by
  rcases x with ⟨i0, i1, i2⟩
  refine ⟨?_, ?_, ?_⟩
  · fin_cases i0 <;> simp [target0]
  · fin_cases i1 <;> simp [target1]
  · fin_cases i2 <;> simp [target2]

private lemma absCell_extract0 {m : ℕ} {v : Cell1 (m + 2)}
    (hv : allowed1 (0, (Fin.last m).castSucc) v) :
    absCell m (target0 (extract0 m v)) = v := by
  rcases v with ⟨⟨r, hr⟩, ⟨c, hc⟩⟩
  simp only [allowed1, Prod.mk.injEq, Fin.ext_iff, Fin.val_zero, Fin.val_castSucc,
    Fin.val_last] at hv
  interval_cases r
  · refine Prod.ext (by simp [extract0, target0, absCell]) (Fin.ext ?_)
    simp only [extract0, target0, absCell, ↓reduceIte, Fin.val_one]
    omega
  · by_cases hcm : c = m
    · refine Prod.ext (by simp [extract0, target0, absCell, hcm]) (Fin.ext ?_)
      simp only [extract0, target0, absCell, hcm, one_ne_zero, ↓reduceIte, Fin.val_one]
      omega
    · refine Prod.ext (by simp [extract0, target0, absCell, hcm]) (Fin.ext ?_)
      simp only [extract0, target0, absCell, hcm, one_ne_zero, ↓reduceIte, Fin.val_two]
      omega
  · omega

private lemma absCell_extract1 {m : ℕ} {v : Cell1 (m + 2)}
    (hv : allowed1 (1, (Fin.last m).castSucc) v) :
    absCell m (target1 (extract1 m v)) = v ∧ (target1 (extract1 m v) = (0, 0) → 0 < m) := by
  rcases v with ⟨⟨r, hr⟩, ⟨c, hc⟩⟩
  simp only [allowed1, Prod.mk.injEq, Fin.ext_iff, Fin.val_one, Fin.val_castSucc,
    Fin.val_last] at hv
  interval_cases r
  · by_cases hcm : c = m
    · refine ⟨Prod.ext (by simp [extract1, target1, absCell, hcm]) (Fin.ext ?_),
        by simp [extract1, target1, hcm]⟩
      simp only [extract1, target1, absCell, hcm, ↓reduceIte, Fin.val_one]
      omega
    · refine ⟨Prod.ext (by simp [extract1, target1, absCell, hcm]) (Fin.ext ?_),
        fun _ => by omega⟩
      simp only [extract1, target1, absCell, hcm, ↓reduceIte, Fin.val_zero]
      omega
  · refine ⟨Prod.ext (by simp [extract1, target1, absCell]) (Fin.ext ?_),
      by simp [extract1, target1]⟩
    simp only [extract1, target1, absCell, one_ne_zero, ↓reduceIte, Fin.val_one]
    omega
  · by_cases hcm : c = m
    · refine ⟨Prod.ext (by simp [extract1, target1, absCell, hcm]) (Fin.ext ?_),
        by simp [extract1, target1, hcm]⟩
      simp only [extract1, target1, absCell, hcm, OfNat.ofNat_ne_zero, Nat.reduceEqDiff,
        ↓reduceIte, Fin.val_one]
      omega
    · refine ⟨Prod.ext (by simp [extract1, target1, absCell, hcm]) (Fin.ext ?_),
        by simp [extract1, target1, hcm]⟩
      simp only [extract1, target1, absCell, hcm, OfNat.ofNat_ne_zero, Nat.reduceEqDiff,
        ↓reduceIte, Fin.val_two]
      omega

private lemma absCell_extract2 {m : ℕ} {v : Cell1 (m + 2)}
    (hv : allowed1 (2, (Fin.last m).castSucc) v) :
    absCell m (target2 (extract2 m v)) = v ∧ (target2 (extract2 m v) = (1, 0) → 0 < m) := by
  rcases v with ⟨⟨r, hr⟩, ⟨c, hc⟩⟩
  simp only [allowed1, Prod.mk.injEq, Fin.ext_iff, Fin.val_two, Fin.val_castSucc,
    Fin.val_last] at hv
  interval_cases r
  · omega
  · by_cases hcm : c = m
    · refine ⟨Prod.ext (by simp [extract2, target2, absCell, hcm]) (Fin.ext ?_),
        by simp [extract2, target2, hcm]⟩
      simp only [extract2, target2, absCell, hcm, ↓reduceIte, Fin.val_one]
      omega
    · refine ⟨Prod.ext (by simp [extract2, target2, absCell, hcm]) (Fin.ext ?_),
        fun _ => by omega⟩
      simp only [extract2, target2, absCell, hcm, ↓reduceIte, Fin.val_zero]
      omega
  · refine ⟨Prod.ext (by simp [extract2, target2, absCell]) (Fin.ext ?_),
      by simp [extract2, target2]⟩
    simp only [extract2, target2, absCell, Nat.reduceEqDiff, ↓reduceIte, Fin.val_one]
    omega

private lemma extract0_absCell (m : ℕ) (i : Fin 3) :
    extract0 m (absCell m (target0 i)) = i := by
  fin_cases i <;> simp [extract0, absCell, target0]

private lemma extract1_absCell (m : ℕ) (i : Fin 5) (h : target1 i = (0, 0) → 0 < m) :
    extract1 m (absCell m (target1 i)) = i := by
  fin_cases i
  · have hm : 0 < m := h rfl
    have hne : m - 1 ≠ m := by omega
    simp [extract1, absCell, target1, hne]
  · simp [extract1, absCell, target1]
  · simp [extract1, absCell, target1]
  · simp [extract1, absCell, target1]
  · simp [extract1, absCell, target1]

private lemma extract2_absCell (m : ℕ) (i : Fin 3) (h : target2 i = (1, 0) → 0 < m) :
    extract2 m (absCell m (target2 i)) = i := by
  fin_cases i
  · have hm : 0 < m := h rfl
    have hne : m - 1 ≠ m := by omega
    simp [extract2, absCell, target2, hne]
  · simp [extract2, absCell, target2]
  · simp [extract2, absCell, target2]

/-! #### Pure combination and restriction functions -/

def combineFun (m : ℕ) (f : Cell1 m → Cell1 (m + 1)) (x : Fin 3 × Fin 5 × Fin 3) :
    Cell1 (m + 1) → Cell1 (m + 2) := fun u =>
  if h : u.2.val < m then
    let w := f (u.1, ⟨u.2.val, h⟩)
    (w.1, w.2.castSucc)
  else
    absCell m (targetOf x u.1)

private lemma combineFun_old (m : ℕ) (f : Cell1 m → Cell1 (m + 1)) (x : Fin 3 × Fin 5 × Fin 3)
    (u : Cell1 m) :
    combineFun m f x (u.1, u.2.castSucc) = ((f u).1, (f u).2.castSucc) := by
  simp [combineFun, u.2.isLt]

private lemma combineFun_last (m : ℕ) (f : Cell1 m → Cell1 (m + 1)) (x : Fin 3 × Fin 5 × Fin 3)
    (r : Fin 3) :
    combineFun m f x (r, Fin.last m) = absCell m (targetOf x r) := by
  simp [combineFun]

def restrictFun (m : ℕ) (g : Cell1 (m + 1) → Cell1 (m + 2))
    (hcol : ∀ u : Cell1 m, (g (u.1, u.2.castSucc)).2.val < m + 1) :
    Cell1 m → Cell1 (m + 1) := fun u =>
  ((g (u.1, u.2.castSucc)).1, ⟨(g (u.1, u.2.castSucc)).2.val, hcol u⟩)

private lemma g_col_lt {m : ℕ} {g : Cell1 (m + 1) → Cell1 (m + 2)}
    (hgall : ∀ u : Cell1 (m + 1), allowed1 (u.1, u.2.castSucc) (g u)) (u : Cell1 m) :
    (g (u.1, u.2.castSucc)).2.val < m + 1 := by
  have h := allowed1_col_le (hgall (u.1, u.2.castSucc))
  simp only [Fin.val_castSucc] at h
  omega

private lemma combine_valid {m : ℕ} {s ns : State} {f : Cell1 m → Cell1 (m + 1)}
    (hf : ValidPred m s f) {x : Fin 3 × Fin 5 × Fin 3} (hst : stepValid s ns x = true) :
    ValidPred (m + 1) ns (combineFun m f x) := by
  rcases s with ⟨out0, in0, out1, in1⟩
  rcases ns with ⟨nout0, nin0, nout1, nin1⟩
  rcases hf with ⟨hfinj, hfall, hfout0, hfout1, hfcov, hfin0, hfin1⟩
  rcases x with ⟨i0, i1, i2⟩
  simp only [stepValid, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    bne_iff_ne, beq_iff_eq] at hst
  rcases hst with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd01, hd02⟩, hd12⟩, h_in0⟩, h_in1⟩, h_out0⟩, h_out1⟩,
    h_nout0⟩, h_nout1⟩, h_hit2⟩, h_nin0⟩, h_nin1⟩
  have hcol0 := target_col0_iff (i0, i1, i2)
  have ht1_pos : target1 i1 = (0, 0) → 0 < m := fun h => hfin0 (h_in0.trans (by simp [h]))
  have ht2_pos : target2 i2 = (1, 0) → 0 < m := fun h => hfin1 (h_in1.trans (by simp [h]))
  set d : Fin 3 → Fin 3 × Fin 3 := targetOf (i0, i1, i2)
  have hd_pos : ∀ r : Fin 3, (d r).2.val = 0 → 0 < m := by
    intro r hr
    fin_cases r
    · exact False.elim (hcol0.1 hr)
    · exact ht1_pos (hcol0.2.1 hr)
    · exact ht2_pos (hcol0.2.2 hr)
  have hd_inj : ∀ r1 r2 : Fin 3, absCell m (d r1) = absCell m (d r2) → r1 = r2 := by
    intro r1 r2 heq
    have hd := absCell_inj (hd_pos r1) (hd_pos r2) heq
    fin_cases r1 <;> fin_cases r2 <;>
      first | rfl | exact absurd hd hd01 | exact absurd hd hd02 | exact absurd hd hd12 |
        exact absurd hd.symm hd01 | exact absurd hd.symm hd02 | exact absurd hd.symm hd12
  have hdisj : ∀ (u : Cell1 m) (r : Fin 3), ((f u).1, (f u).2.castSucc) ≠ absCell m (d r) := by
    intro u r heq
    rcases Prod.mk.inj heq with ⟨hr, hc'⟩
    have hc : (f u).2.val = m + (d r).2.val - 1 := by simpa [absCell] using congrArg Fin.val hc'
    have hlt : (f u).2.val < m + 1 := (f u).2.isLt
    have hcases : (d r).2.val = 0 ∨ (d r).2.val = 1 ∨ (d r).2.val = 2 := by
      fin_cases r
      · fin_cases i0 <;> simp [d, targetOf, target0]
      · fin_cases i1 <;> simp [d, targetOf, target1]
      · fin_cases i2 <;> simp [d, targetOf, target2]
    rcases hcases with h0 | h1 | h2
    · have hm : 0 < m := hd_pos r h0
      have hfm : (f u).2.val + 1 = m := by omega
      have hne : ¬ (∃ u' : Cell1 m, f u' = ((f u).1, (⟨(f u).2.val, by omega⟩ : Fin m).castSucc)) := by
        rw [hfcov ((f u).1, ⟨(f u).2.val, by omega⟩)]
        simp only [not_not]
        fin_cases r
        · exact False.elim (hcol0.1 h0)
        · left
          have h10 := hcol0.2.1 h0
          have hr0 : (d 1).1 = 0 := congrArg Prod.fst h10
          exact ⟨h_in0.trans (by simp [h10]), hr.trans hr0, hfm⟩
        · right
          have h20 := hcol0.2.2 h0
          have hr1 : (d 2).1 = 1 := congrArg Prod.fst h20
          exact ⟨h_in1.trans (by simp [h20]), hr.trans hr1, hfm⟩
      exact hne ⟨u, Prod.ext rfl (Fin.ext rfl)⟩
    · have hflast : (f u).2 = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
      have hrow : (f u).1 = 0 ∨ (f u).1 = 1 ∨ (f u).1 = 2 := by have := (f u).1.isLt; omega
      rcases hrow with hr0 | hr1 | hr2
      · have hfu : f u = (0, Fin.last m) := Prod.ext hr0 hflast
        exact allowed1_not_zero_last u (hfu ▸ hfall u)
      · have hout0_t : out0 = true := hfout0.mpr ⟨u, Prod.ext hr1 hflast⟩
        have hdr : d r = (1, 1) := Prod.ext (hr.symm.trans hr1) (Fin.ext h1)
        rcases h_out0 with hfalse | ⟨⟨h0', h1'⟩, h2'⟩
        · exact absurd hout0_t (by simp [hfalse])
        · fin_cases r
          · exact h0' hdr
          · exact h1' hdr
          · exact h2' hdr
      · have hout1_t : out1 = true := hfout1.mpr ⟨u, Prod.ext hr2 hflast⟩
        have hdr : d r = (2, 1) := Prod.ext (hr.symm.trans hr2) (Fin.ext h1)
        rcases h_out1 with hfalse | ⟨⟨h0', h1'⟩, h2'⟩
        · exact absurd hout1_t (by simp [hfalse])
        · fin_cases r
          · exact h0' hdr
          · exact h1' hdr
          · exact h2' hdr
    · omega
  refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => by omega, fun _ => by omega⟩
  · -- Injective
    intro u1 u2 heq
    by_cases h1 : u1.2.val < m <;> by_cases h2 : u2.2.val < m
    · simp only [combineFun, h1, h2, ↓reduceDIte] at heq
      rcases Prod.mk.inj heq with ⟨hr, hc⟩
      have hfeq : f (u1.1, ⟨u1.2.val, h1⟩) = f (u2.1, ⟨u2.2.val, h2⟩) :=
        Prod.ext hr (Fin.castSucc_inj.mp hc)
      rcases Prod.mk.inj (hfinj hfeq) with ⟨hur, huc⟩
      exact Prod.ext hur (Fin.ext (Fin.mk.inj huc))
    · simp only [combineFun, h1, h2, ↓reduceDIte] at heq
      exact absurd heq (hdisj (u1.1, ⟨u1.2.val, h1⟩) u2.1)
    · simp only [combineFun, h1, h2, ↓reduceDIte] at heq
      exact absurd heq.symm (hdisj (u2.1, ⟨u2.2.val, h2⟩) u1.1)
    · simp only [combineFun, h1, h2, ↓reduceDIte] at heq
      exact Prod.ext (hd_inj u1.1 u2.1 heq) (Fin.ext (by omega))
  · -- Allowed
    intro u
    rcases u with ⟨r, c⟩
    by_cases h : c.val < m
    · simp only [combineFun, h, ↓reduceDIte]
      have h1 := hfall (r, ⟨c.val, h⟩)
      have h2 := (allowed1_castSucc (r, (⟨c.val, h⟩ : Fin m).castSucc) (f (r, ⟨c.val, h⟩))).mpr h1
      have hce : (⟨c.val, h⟩ : Fin m).castSucc.castSucc = c.castSucc := Fin.ext rfl
      simpa [hce] using h2
    · have hcm : c = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
      subst hcm
      rw [combineFun_last]
      fin_cases r
      · exact target0_allowed m i0
      · exact target1_allowed m i1 ht1_pos
      · exact target2_allowed m i2 ht2_pos
  · -- nout0
    rw [h_nout0, beq_eq_dec]
    simp only [decide_eq_true_eq]
    constructor
    · intro hd0
      refine ⟨(0, Fin.last m), ?_⟩
      rw [combineFun_last, targetOf, hd0, absCell_two]
    · rintro ⟨⟨r, c⟩, hu⟩
      by_cases h : c.val < m
      · simp only [combineFun, h, ↓reduceDIte] at hu
        have hc := congrArg (fun y : Cell1 (m + 2) => y.2.val) hu
        simp only [Fin.val_castSucc, Fin.val_last] at hc
        have := (f (r, ⟨c.val, h⟩)).2.isLt
        omega
      · simp only [combineFun, h, ↓reduceDIte] at hu
        rcases Prod.mk.inj hu with ⟨hrow, hcol'⟩
        have hcol : (d r).2 = 2 := Fin.ext (by
          have hval : m + (d r).2.val - 1 = m + 1 := by
            simpa [absCell] using congrArg Fin.val hcol'
          omega)
        fin_cases r
        · exact Prod.ext hrow hcol
        · exact absurd (Prod.ext hrow hcol) (target1_ne_12 i1)
        · exact absurd (Prod.ext hrow hcol) (target2_ne_12 i2)
  · -- nout1
    rw [h_nout1, beq_eq_dec]
    simp only [decide_eq_true_eq]
    constructor
    · intro hd1
      refine ⟨(1, Fin.last m), ?_⟩
      rw [combineFun_last, targetOf, hd1, absCell_two]
    · rintro ⟨⟨r, c⟩, hu⟩
      by_cases h : c.val < m
      · simp only [combineFun, h, ↓reduceDIte] at hu
        have hc := congrArg (fun y : Cell1 (m + 2) => y.2.val) hu
        simp only [Fin.val_castSucc, Fin.val_last] at hc
        have := (f (r, ⟨c.val, h⟩)).2.isLt
        omega
      · simp only [combineFun, h, ↓reduceDIte] at hu
        rcases Prod.mk.inj hu with ⟨hrow, hcol'⟩
        have hcol : (d r).2 = 2 := Fin.ext (by
          have hval : m + (d r).2.val - 1 = m + 1 := by
            simpa [absCell] using congrArg Fin.val hcol'
          omega)
        fin_cases r
        · exact absurd (Prod.ext hrow hcol) (target0_ne_22 i0)
        · exact Prod.ext hrow hcol
        · exact absurd (Prod.ext hrow hcol) (target2_ne_22 i2)
  · -- Coverage
    intro v
    rcases v with ⟨r, c⟩
    by_cases hv : c.val < m
    · have hnot : ¬ ((nin0 = true ∧ r = 0 ∧ c.val + 1 = m + 1) ∨
          (nin1 = true ∧ r = 1 ∧ c.val + 1 = m + 1)) := by omega
      simp only [hnot, not_false_eq_true, iff_true]
      by_cases hex : ∃ u : Cell1 m, f u = (r, (⟨c.val, hv⟩ : Fin m).castSucc)
      · obtain ⟨u, hu⟩ := hex
        refine ⟨(u.1, u.2.castSucc), ?_⟩
        rw [combineFun_old, hu]
        exact Prod.ext rfl (Fin.ext rfl)
      · rw [hfcov (r, ⟨c.val, hv⟩)] at hex
        push Not at hex
        rcases hex with ⟨hin0t, hv0, hvm⟩ | ⟨hin1t, hv1, hvm⟩
        · dsimp only at hv0 hvm
          have hd1 : target1 i1 = (0, 0) := by
            have := h_in0.symm.trans hin0t
            simpa [beq_eq_dec] using this
          refine ⟨(1, Fin.last m), ?_⟩
          rw [combineFun_last, targetOf, hd1]
          refine Prod.ext (by simp [absCell, hv0]) (Fin.ext ?_)
          simp only [absCell, Fin.val_zero, Fin.val_castSucc]
          omega
        · dsimp only at hv1 hvm
          have hd2 : target2 i2 = (1, 0) := by
            have := h_in1.symm.trans hin1t
            simpa [beq_eq_dec] using this
          refine ⟨(2, Fin.last m), ?_⟩
          rw [combineFun_last, targetOf, hd2]
          refine Prod.ext (by simp [absCell, hv1]) (Fin.ext ?_)
          simp only [absCell, Fin.val_zero, Fin.val_castSucc]
          omega
    · have hcm : c = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
      subst hcm
      have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 := by fin_cases r <;> simp
      rcases hr_cases with rfl | rfl | rfl
      · have hhit0 : (∃ u : Cell1 (m + 1), combineFun m f (i0, i1, i2) u = (0, (Fin.last m).castSucc)) ↔
            (target0 i0 = (0, 1) ∨ target1 i1 = (0, 1) ∨ target2 i2 = (0, 1)) := by
          constructor
          · rintro ⟨⟨ru, cu⟩, hu⟩
            by_cases h : cu.val < m
            · simp only [combineFun, h, ↓reduceDIte] at hu
              rcases Prod.mk.inj hu with ⟨hr', hc'⟩
              have hfu : f (ru, ⟨cu.val, h⟩) = (0, Fin.last m) :=
                Prod.ext hr' (Fin.castSucc_inj.mp hc')
              exact False.elim (allowed1_not_zero_last _ (hfu ▸ hfall _))
            · simp only [combineFun, h, ↓reduceDIte] at hu
              have hdu : d ru = (0, 1) := absCell_inj (hd_pos ru) (by simp)
                (hu.trans (absCell_one m 0).symm)
              fin_cases ru
              · left; exact hdu
              · right; left; exact hdu
              · right; right; exact hdu
          · intro h
            rcases h with h0 | h1 | h2
            · exact ⟨(0, Fin.last m), by rw [combineFun_last, targetOf, h0, absCell_one]⟩
            · exact ⟨(1, Fin.last m), by rw [combineFun_last, targetOf, h1, absCell_one]⟩
            · exact ⟨(2, Fin.last m), by rw [combineFun_last, targetOf, h2, absCell_one]⟩
        rw [hhit0, h_nin0]
        by_cases h0 : target0 i0 = (0, 1) <;> by_cases h1 : target1 i1 = (0, 1) <;>
          by_cases h2 : target2 i2 = (0, 1) <;> simp [h0, h1, h2]
      · have hhit1 : (∃ u : Cell1 (m + 1), combineFun m f (i0, i1, i2) u = (1, (Fin.last m).castSucc)) ↔
            (out0 = true ∨ target0 i0 = (1, 1) ∨ target1 i1 = (1, 1) ∨ target2 i2 = (1, 1)) := by
          constructor
          · rintro ⟨⟨ru, cu⟩, hu⟩
            by_cases h : cu.val < m
            · simp only [combineFun, h, ↓reduceDIte] at hu
              rcases Prod.mk.inj hu with ⟨hr', hc'⟩
              exact Or.inl (hfout0.mpr ⟨(ru, ⟨cu.val, h⟩), Prod.ext hr' (Fin.castSucc_inj.mp hc')⟩)
            · simp only [combineFun, h, ↓reduceDIte] at hu
              have hdu : d ru = (1, 1) := absCell_inj (hd_pos ru) (by simp)
                (hu.trans (absCell_one m 1).symm)
              fin_cases ru
              · right; left; exact hdu
              · right; right; left; exact hdu
              · right; right; right; exact hdu
          · intro h
            rcases h with hout | h0 | h1 | h2
            · obtain ⟨u, hu⟩ := hfout0.mp hout
              exact ⟨(u.1, u.2.castSucc), by rw [combineFun_old, hu]⟩
            · exact ⟨(0, Fin.last m), by rw [combineFun_last, targetOf, h0, absCell_one]⟩
            · exact ⟨(1, Fin.last m), by rw [combineFun_last, targetOf, h1, absCell_one]⟩
            · exact ⟨(2, Fin.last m), by rw [combineFun_last, targetOf, h2, absCell_one]⟩
        rw [hhit1, h_nin1]
        cases out0 <;> by_cases h0 : target0 i0 = (1, 1) <;> by_cases h1 : target1 i1 = (1, 1) <;>
          by_cases h2 : target2 i2 = (1, 1) <;> simp [h0, h1, h2]
      · have hnot2 : ¬ ((nin0 = true ∧ (2 : Fin 3) = 0 ∧ (Fin.last m).val + 1 = m + 1) ∨
            (nin1 = true ∧ (2 : Fin 3) = 1 ∧ (Fin.last m).val + 1 = m + 1)) := by
          rintro (⟨_, h, _⟩ | ⟨_, h, _⟩) <;> exact absurd h (by decide)
        rw [iff_true_intro hnot2, iff_true]
        rcases h_hit2 with ((hout | h0) | h1) | h2
        · obtain ⟨u, hu⟩ := hfout1.mp hout
          exact ⟨(u.1, u.2.castSucc), by rw [combineFun_old, hu]⟩
        · exact ⟨(0, Fin.last m), by rw [combineFun_last, targetOf, h0, absCell_one]⟩
        · exact ⟨(1, Fin.last m), by rw [combineFun_last, targetOf, h1, absCell_one]⟩
        · exact ⟨(2, Fin.last m), by rw [combineFun_last, targetOf, h2, absCell_one]⟩

def splitState (m : ℕ) (g : Cell1 (m + 1) → Cell1 (m + 2)) : State :=
  (decide (∃ u : Cell1 m, g (u.1, u.2.castSucc) = (1, (Fin.last m).castSucc)),
   decide (target1 (extract1 m (g (1, Fin.last m))) = (0, 0)),
   decide (∃ u : Cell1 m, g (u.1, u.2.castSucc) = (2, (Fin.last m).castSucc)),
   decide (target2 (extract2 m (g (2, Fin.last m))) = (1, 0)))

def splitTriple (m : ℕ) (g : Cell1 (m + 1) → Cell1 (m + 2)) : Fin 3 × Fin 5 × Fin 3 :=
  (extract0 m (g (0, Fin.last m)), extract1 m (g (1, Fin.last m)), extract2 m (g (2, Fin.last m)))

private lemma split_valid_f {m : ℕ} {ns : State} {g : Cell1 (m + 1) → Cell1 (m + 2)}
    (hg : ValidPred (m + 1) ns g) :
    ValidPred m (splitState m g) (restrictFun m g (g_col_lt hg.2.1)) := by
  rcases hg with ⟨hginj, hgall, _, _, hgcov, _, _⟩
  set f := restrictFun m g (g_col_lt hgall)
  have hfg : ∀ u : Cell1 m, g (u.1, u.2.castSucc) = ((f u).1, (f u).2.castSucc) := fun u =>
    Prod.ext rfl (Fin.ext rfl)
  set i0 := extract0 m (g (0, Fin.last m))
  set i1 := extract1 m (g (1, Fin.last m))
  set i2 := extract2 m (g (2, Fin.last m))
  have hi1_both := absCell_extract1 (hgall (1, Fin.last m))
  have hi1 : absCell m (target1 i1) = g (1, Fin.last m) := hi1_both.1
  have hi1_pos : target1 i1 = (0, 0) → 0 < m := hi1_both.2
  have hi2_both := absCell_extract2 (hgall (2, Fin.last m))
  have hi2 : absCell m (target2 i2) = g (2, Fin.last m) := hi2_both.1
  have hi2_pos : target2 i2 = (1, 0) → 0 < m := hi2_both.2
  have hout_iff : ∀ r : Fin 3,
      (∃ u : Cell1 m, g (u.1, u.2.castSucc) = (r, (Fin.last m).castSucc)) ↔
      (∃ u : Cell1 m, f u = (r, Fin.last m)) := by
    intro r
    constructor <;> rintro ⟨u, hu⟩
    · rw [hfg] at hu
      rcases Prod.mk.inj hu with ⟨hr, hc⟩
      exact ⟨u, Prod.ext hr (Fin.castSucc_inj.mp hc)⟩
    · exact ⟨u, by rw [hfg, hu]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u1 u2 heq
    have hge : g (u1.1, u1.2.castSucc) = g (u2.1, u2.2.castSucc) := by rw [hfg, hfg, heq]
    rcases Prod.mk.inj (hginj hge) with ⟨hr, hc⟩
    exact Prod.ext hr (Fin.castSucc_inj.mp hc)
  · intro u
    have h1 := hgall (u.1, u.2.castSucc)
    rw [hfg] at h1
    exact (allowed1_castSucc (u.1, u.2.castSucc) (f u)).mp h1
  · simp only [splitState, decide_eq_true_eq, hout_iff 1]
  · simp only [splitState, decide_eq_true_eq, hout_iff 2]
  · intro v
    have hv_cov : ∃ w : Cell1 (m + 1), g w = (v.1, v.2.castSucc.castSucc) := by
      rw [hgcov (v.1, v.2.castSucc)]
      have := v.2.isLt
      simp only [Fin.val_castSucc]
      omega
    constructor
    · rintro ⟨u, hu⟩ hbad
      rcases hbad with ⟨hin0t, hv0, hvm⟩ | ⟨hin1t, hv1, hvm⟩
      · have ht1 : target1 i1 = (0, 0) := by simpa [splitState, i1] using hin0t
        have h1 : g (1, Fin.last m) = g (u.1, u.2.castSucc) := by
          rw [← hi1, ht1, hfg, hu]
          refine Prod.ext (by simp [absCell, hv0]) (Fin.ext ?_)
          simp only [absCell, Fin.val_zero, Fin.val_castSucc]
          omega
        have hne := congrArg (fun y : Cell1 (m + 1) => y.2.val) (hginj h1)
        simp only [Fin.val_last, Fin.val_castSucc] at hne
        omega
      · have ht2 : target2 i2 = (1, 0) := by simpa [splitState, i2] using hin1t
        have h2 : g (2, Fin.last m) = g (u.1, u.2.castSucc) := by
          rw [← hi2, ht2, hfg, hu]
          refine Prod.ext (by simp [absCell, hv1]) (Fin.ext ?_)
          simp only [absCell, Fin.val_zero, Fin.val_castSucc]
          omega
        have hne := congrArg (fun y : Cell1 (m + 1) => y.2.val) (hginj h2)
        simp only [Fin.val_last, Fin.val_castSucc] at hne
        omega
    · intro hnot
      obtain ⟨⟨wr, wc⟩, hw⟩ := hv_cov
      by_cases hwm : wc.val < m
      · refine ⟨(wr, ⟨wc.val, hwm⟩), ?_⟩
        have hw' : (wr, wc) = (wr, (⟨wc.val, hwm⟩ : Fin m).castSucc) := Prod.ext rfl (Fin.ext rfl)
        rw [hw', hfg (wr, ⟨wc.val, hwm⟩)] at hw
        rcases Prod.mk.inj hw with ⟨hr, hc⟩
        exact Prod.ext hr (Fin.castSucc_inj.mp hc)
      · have hwc : wc = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
        subst hwc
        have hallow := hgall (wr, Fin.last m)
        rw [hw] at hallow
        simp only [allowed1, Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_last] at hallow
        have hvlt : v.2.val < m := v.2.isLt
        have hvm : v.2.val + 1 = m := by omega
        have hrow : wr.val = v.1.val + 1 := by omega
        have hwr_cases : wr = 0 ∨ wr = 1 ∨ wr = 2 := by fin_cases wr <;> simp
        rcases hwr_cases with rfl | rfl | rfl
        · simp only [Fin.val_zero] at hrow; omega
        · have hv0 : v.1 = 0 := Fin.ext (by simp only [Fin.val_one, Fin.val_zero] at hrow ⊢; omega)
          have h1 : absCell m (target1 i1) = absCell m (0, 0) := by
            rw [hi1, hw]
            exact Prod.ext hv0 (Fin.ext (by simp [absCell]; omega))
          have ht1 : target1 i1 = (0, 0) := absCell_inj
            (fun hr => hi1_pos ((target_col0_iff (i0, i1, i2)).2.1 hr))
            (fun _ => by omega) h1
          exact False.elim (hnot (Or.inl ⟨by simp [splitState, i1, ht1], hv0, hvm⟩))
        · have hv1 : v.1 = 1 := Fin.ext (by simp only [Fin.val_two, Fin.val_one] at hrow ⊢; omega)
          have h2 : absCell m (target2 i2) = absCell m (1, 0) := by
            rw [hi2, hw]
            exact Prod.ext hv1 (Fin.ext (by simp [absCell]; omega))
          have ht2 : target2 i2 = (1, 0) := absCell_inj
            (fun hr => hi2_pos ((target_col0_iff (i0, i1, i2)).2.2 hr))
            (fun _ => by omega) h2
          exact False.elim (hnot (Or.inr ⟨by simp [splitState, i2, ht2], hv1, hvm⟩))
  · intro h; exact hi1_pos (by simpa [splitState, i1] using h)
  · intro h; exact hi2_pos (by simpa [splitState, i2] using h)

private lemma split_valid_step {m : ℕ} {ns : State} {g : Cell1 (m + 1) → Cell1 (m + 2)}
    (hg : ValidPred (m + 1) ns g) :
    stepValid (splitState m g) ns (splitTriple m g) = true := by
  have hf_valid := split_valid_f hg
  rcases hg with ⟨hginj, hgall, hgout0, hgout1, hgcov, _, _⟩
  rcases ns with ⟨nout0, nin0, nout1, nin1⟩
  set i0 := extract0 m (g (0, Fin.last m))
  set i1 := extract1 m (g (1, Fin.last m))
  set i2 := extract2 m (g (2, Fin.last m))
  have hi0 : absCell m (target0 i0) = g (0, Fin.last m) := absCell_extract0 (hgall (0, Fin.last m))
  have hi1_both := absCell_extract1 (hgall (1, Fin.last m))
  have hi1 : absCell m (target1 i1) = g (1, Fin.last m) := hi1_both.1
  have hi1_pos : target1 i1 = (0, 0) → 0 < m := hi1_both.2
  have hi2_both := absCell_extract2 (hgall (2, Fin.last m))
  have hi2 : absCell m (target2 i2) = g (2, Fin.last m) := hi2_both.1
  have hi2_pos : target2 i2 = (1, 0) → 0 < m := hi2_both.2
  have hd01 : target0 i0 ≠ target1 i1 := fun heq => by
    have h := congrArg (absCell m) heq
    rw [hi0, hi1] at h
    exact absurd (congrArg Prod.fst (hginj h)) (by simp)
  have hd02 : target0 i0 ≠ target2 i2 := fun heq => by
    have h := congrArg (absCell m) heq
    rw [hi0, hi2] at h
    exact absurd (congrArg Prod.fst (hginj h)) (by simp)
  have hd12 : target1 i1 ≠ target2 i2 := fun heq => by
    have h := congrArg (absCell m) heq
    rw [hi1, hi2] at h
    exact absurd (congrArg Prod.fst (hginj h)) (by simp)
  have hno_out : ∀ r : Fin 3,
      (∃ u : Cell1 m, g (u.1, u.2.castSucc) = (r, (Fin.last m).castSucc)) →
      target0 i0 ≠ (r, 1) ∧ target1 i1 ≠ (r, 1) ∧ target2 i2 ≠ (r, 1) := by
    rintro r ⟨u, hu⟩
    have hgu : g (u.1, u.2.castSucc) = absCell m (r, 1) := hu.trans (absCell_one m r).symm
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := congrArg (fun y : Cell1 (m + 1) => y.2.val) (hginj (hgu.trans (by rw [← h, hi0])))
      simp only [Fin.val_castSucc, Fin.val_last] at this; omega
    · have := congrArg (fun y : Cell1 (m + 1) => y.2.val) (hginj (hgu.trans (by rw [← h, hi1])))
      simp only [Fin.val_castSucc, Fin.val_last] at this; omega
    · have := congrArg (fun y : Cell1 (m + 1) => y.2.val) (hginj (hgu.trans (by rw [← h, hi2])))
      simp only [Fin.val_castSucc, Fin.val_last] at this; omega
  have h_nout0 : nout0 = (target0 i0 == (1, 2)) := by
    rw [beq_eq_dec]
    apply Bool.eq_iff_iff.mpr
    rw [hgout0, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨wr, wc⟩, hw⟩
      by_cases hwm : wc.val < m
      · have h := allowed1_col_le (hgall (wr, wc))
        rw [hw] at h
        simp only [Fin.val_castSucc, Fin.val_last] at h
        omega
      · have hwc : wc = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
        subst hwc
        fin_cases wr <;> dsimp only at hw
        · exact absCell_inj (fun hr => False.elim ((target_col0_iff (i0, i1, i2)).1 hr))
            (by simp) ((hi0.trans hw).trans (absCell_two m 1).symm)
        · exact absurd (absCell_inj (fun hr => hi1_pos ((target_col0_iff (i0, i1, i2)).2.1 hr))
            (by simp) ((hi1.trans hw).trans (absCell_two m 1).symm)) (target1_ne_12 i1)
        · exact absurd (absCell_inj (fun hr => hi2_pos ((target_col0_iff (i0, i1, i2)).2.2 hr))
            (by simp) ((hi2.trans hw).trans (absCell_two m 1).symm)) (target2_ne_12 i2)
    · intro h
      exact ⟨(0, Fin.last m), by rw [← hi0, h, absCell_two]⟩
  have h_nout1 : nout1 = (target1 i1 == (2, 2)) := by
    rw [beq_eq_dec]
    apply Bool.eq_iff_iff.mpr
    rw [hgout1, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨wr, wc⟩, hw⟩
      by_cases hwm : wc.val < m
      · have h := allowed1_col_le (hgall (wr, wc))
        rw [hw] at h
        simp only [Fin.val_castSucc, Fin.val_last] at h
        omega
      · have hwc : wc = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
        subst hwc
        fin_cases wr <;> dsimp only at hw
        · exact absurd (absCell_inj (fun hr => False.elim ((target_col0_iff (i0, i1, i2)).1 hr))
            (by simp) ((hi0.trans hw).trans (absCell_two m 2).symm)) (target0_ne_22 i0)
        · exact absCell_inj (fun hr => hi1_pos ((target_col0_iff (i0, i1, i2)).2.1 hr))
            (by simp) ((hi1.trans hw).trans (absCell_two m 2).symm)
        · exact absurd (absCell_inj (fun hr => hi2_pos ((target_col0_iff (i0, i1, i2)).2.2 hr))
            (by simp) ((hi2.trans hw).trans (absCell_two m 2).symm)) (target2_ne_22 i2)
    · intro h
      exact ⟨(1, Fin.last m), by rw [← hi1, h, absCell_two]⟩
  have hhit_last : ∀ r : Fin 3,
      (∃ w : Cell1 (m + 1), g w = (r, (Fin.last m).castSucc)) ↔
      (∃ u : Cell1 m, g (u.1, u.2.castSucc) = (r, (Fin.last m).castSucc)) ∨
        target0 i0 = (r, 1) ∨ target1 i1 = (r, 1) ∨ target2 i2 = (r, 1) := by
    intro r
    constructor
    · rintro ⟨⟨wr, wc⟩, hw⟩
      by_cases hwm : wc.val < m
      · left
        exact ⟨(wr, ⟨wc.val, hwm⟩), hw⟩
      · right
        have hwc : wc = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
        subst hwc
        fin_cases wr <;> dsimp only at hw
        · left
          exact absCell_inj (fun hr => False.elim ((target_col0_iff (i0, i1, i2)).1 hr))
            (by simp) ((hi0.trans hw).trans (absCell_one m r).symm)
        · right; left
          exact absCell_inj (fun hr => hi1_pos ((target_col0_iff (i0, i1, i2)).2.1 hr))
            (by simp) ((hi1.trans hw).trans (absCell_one m r).symm)
        · right; right
          exact absCell_inj (fun hr => hi2_pos ((target_col0_iff (i0, i1, i2)).2.2 hr))
            (by simp) ((hi2.trans hw).trans (absCell_one m r).symm)
    · intro h
      rcases h with ⟨u, hu⟩ | h0 | h1 | h2
      · exact ⟨(u.1, u.2.castSucc), hu⟩
      · exact ⟨(0, Fin.last m), by rw [← hi0, h0, absCell_one]⟩
      · exact ⟨(1, Fin.last m), by rw [← hi1, h1, absCell_one]⟩
      · exact ⟨(2, Fin.last m), by rw [← hi2, h2, absCell_one]⟩
  have h_hit2 : (∃ u : Cell1 m, g (u.1, u.2.castSucc) = (2, (Fin.last m).castSucc)) ∨
      target0 i0 = (2, 1) ∨ target1 i1 = (2, 1) ∨ target2 i2 = (2, 1) := by
    have h2 := (hgcov (2, Fin.last m)).mpr (by simp)
    exact (hhit_last 2).mp h2
  have h_nin0 : nin0 = !((target0 i0 == (0, 1)) || (target1 i1 == (0, 1)) || (target2 i2 == (0, 1))) := by
    apply Bool.eq_iff_iff.mpr
    have h0 := hgcov (0, Fin.last m)
    rw [hhit_last 0] at h0
    have hno0 : ¬ ∃ u : Cell1 m, g (u.1, u.2.castSucc) = (0, (Fin.last m).castSucc) := fun ⟨u, hu⟩ => by
      rcases Prod.mk.inj hu with ⟨hr, hc⟩
      have hfu : restrictFun m g (g_col_lt hgall) u = (0, Fin.last m) :=
        Prod.ext hr (Fin.ext (by simpa [restrictFun] using congrArg Fin.val hc))
      exact allowed1_not_zero_last u (hfu ▸ hf_valid.2.1 u)
    have h0' : (target0 i0 = (0, 1) ∨ target1 i1 = (0, 1) ∨ target2 i2 = (0, 1)) ↔ ¬ (nin0 = true) := by
      simpa [hno0] using h0
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    constructor
    · intro hnin
      have hnot : ¬ (target0 i0 = (0, 1) ∨ target1 i1 = (0, 1) ∨ target2 i2 = (0, 1)) :=
        fun h => h0'.mp h hnin
      exact ⟨⟨fun h => hnot (Or.inl h), fun h => hnot (Or.inr (Or.inl h))⟩,
        fun h => hnot (Or.inr (Or.inr h))⟩
    · intro ⟨⟨ha, hb⟩, hc⟩
      by_contra hnin
      rcases h0'.mpr hnin with h | h | h <;> contradiction
  have h_nin1 : nin1 = !(decide (∃ u : Cell1 m, g (u.1, u.2.castSucc) = (1, (Fin.last m).castSucc)) ||
      (target0 i0 == (1, 1)) || (target1 i1 == (1, 1)) || (target2 i2 == (1, 1))) := by
    apply Bool.eq_iff_iff.mpr
    have h1 := hgcov (1, Fin.last m)
    rw [hhit_last 1] at h1
    have h1' : ((∃ u : Cell1 m, g (u.1, u.2.castSucc) = (1, (Fin.last m).castSucc)) ∨
        target0 i0 = (1, 1) ∨ target1 i1 = (1, 1) ∨ target2 i2 = (1, 1)) ↔ ¬ (nin1 = true) := by
      simpa using h1
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne]
    constructor
    · intro hnin
      have hnot : ¬ ((∃ u : Cell1 m, g (u.1, u.2.castSucc) = (1, (Fin.last m).castSucc)) ∨
          target0 i0 = (1, 1) ∨ target1 i1 = (1, 1) ∨ target2 i2 = (1, 1)) :=
        fun h => h1'.mp h hnin
      exact ⟨⟨⟨fun h => hnot (Or.inl h), fun h => hnot (Or.inr (Or.inl h))⟩,
        fun h => hnot (Or.inr (Or.inr (Or.inl h)))⟩, fun h => hnot (Or.inr (Or.inr (Or.inr h)))⟩
    · intro ⟨⟨⟨ho, ha⟩, hb⟩, hc⟩
      by_contra hnin
      rcases h1'.mpr hnin with h | h | h | h <;> contradiction
  simp only [stepValid, splitState, splitTriple, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', bne_iff_ne, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd01, hd02⟩, hd12⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact (beq_eq_dec (target1 i1) (0, 0)).symm
  · exact (beq_eq_dec (target2 i2) (1, 0)).symm
  · by_cases ho : ∃ u : Cell1 m, g (u.1, u.2.castSucc) = (1, (Fin.last m).castSucc)
    · right; exact ⟨⟨(hno_out 1 ho).1, (hno_out 1 ho).2.1⟩, (hno_out 1 ho).2.2⟩
    · left; simp [ho]
  · by_cases ho : ∃ u : Cell1 m, g (u.1, u.2.castSucc) = (2, (Fin.last m).castSucc)
    · right; exact ⟨⟨(hno_out 2 ho).1, (hno_out 2 ho).2.1⟩, (hno_out 2 ho).2.2⟩
    · left; simp [ho]
  · exact h_nout0
  · exact h_nout1
  · simp only [decide_eq_true_eq]
    rcases h_hit2 with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · exact h_nin0
  · exact h_nin1

private def splitStep (m : ℕ) (ns : State) :
    Valid (m + 1) ns ≃ Σ (s : State), Valid m s × Step s ns where
  toFun g :=
    ⟨splitState m g.1,
     ⟨restrictFun m g.1 (g_col_lt g.2.2.1), split_valid_f g.2⟩,
     ⟨splitTriple m g.1, split_valid_step g.2⟩⟩
  invFun p := ⟨combineFun m p.2.1.1 p.2.2.1, combine_valid p.2.1.2 p.2.2.2⟩
  left_inv g := by
    apply Subtype.ext
    funext u
    rcases u with ⟨r, c⟩
    by_cases h : c.val < m
    · simp only [combineFun, h, ↓reduceDIte, restrictFun]
      exact Prod.ext rfl (Fin.ext rfl)
    · have hcm : c = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
      subst hcm
      simp only [combineFun, Fin.val_last, lt_self_iff_false, ↓reduceDIte, splitTriple, targetOf]
      fin_cases r
      · exact absCell_extract0 (g.2.2.1 (0, Fin.last m))
      · exact (absCell_extract1 (g.2.2.1 (1, Fin.last m))).1
      · exact (absCell_extract2 (g.2.2.1 (2, Fin.last m))).1
  right_inv p := by
    rcases p with ⟨s, ⟨f, hf⟩, ⟨⟨i0, i1, i2⟩, hst⟩⟩
    rcases s with ⟨out0, in0, out1, in1⟩
    have hst' := hst
    simp only [stepValid, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      bne_iff_ne, beq_iff_eq] at hst'
    have h_in0 : in0 = decide (target1 i1 = (0, 0)) :=
      hst'.1.1.1.1.1.1.1.1.2.trans (beq_eq_dec _ _)
    have h_in1 : in1 = decide (target2 i2 = (1, 0)) :=
      hst'.1.1.1.1.1.1.1.2.trans (beq_eq_dec _ _)
    have ht1_pos : target1 i1 = (0, 0) → 0 < m := fun h =>
      hf.2.2.2.2.2.1 (h_in0.trans (by simp [h]))
    have ht2_pos : target2 i2 = (1, 0) → 0 < m := fun h =>
      hf.2.2.2.2.2.2 (h_in1.trans (by simp [h]))
    have htr : splitTriple m (combineFun m f (i0, i1, i2)) = (i0, i1, i2) := by
      simp only [splitTriple, combineFun_last, targetOf]
      exact Prod.ext (extract0_absCell m i0)
        (Prod.ext (extract1_absCell m i1 ht1_pos) (extract2_absCell m i2 ht2_pos))
    have hst_eq : splitState m (combineFun m f (i0, i1, i2)) = (out0, in0, out1, in1) := by
      simp only [splitState, combineFun_old, combineFun_last, targetOf,
        extract1_absCell m i1 ht1_pos, extract2_absCell m i2 ht2_pos]
      refine Prod.ext ?_ (Prod.ext h_in0.symm (Prod.ext ?_ h_in1.symm))
      · apply Bool.eq_iff_iff.mpr
        rw [decide_eq_true_eq, hf.2.2.1]
        constructor <;> rintro ⟨u, hu⟩
        · rcases Prod.mk.inj hu with ⟨hr, hc⟩
          exact ⟨u, Prod.ext hr (Fin.castSucc_inj.mp hc)⟩
        · exact ⟨u, by rw [hu]⟩
      · apply Bool.eq_iff_iff.mpr
        rw [decide_eq_true_eq, hf.2.2.2.1]
        constructor <;> rintro ⟨u, hu⟩
        · rcases Prod.mk.inj hu with ⟨hr, hc⟩
          exact ⟨u, Prod.ext hr (Fin.castSucc_inj.mp hc)⟩
        · exact ⟨u, by rw [hu]⟩
    have hf_eq : restrictFun m (combineFun m f (i0, i1, i2))
        (g_col_lt (combine_valid hf hst).2.1) = f := by
      funext u
      simp only [restrictFun, combineFun_old]
      exact Prod.ext rfl (Fin.ext rfl)
    have hsigma : ∀ {s1 s2 : State} (hs : s1 = s2) (a : Valid m s1) (b : Step s1 ns)
        (a' : Valid m s2) (b' : Step s2 ns),
        a.1 = a'.1 → b.1 = b'.1 →
        (⟨s1, (a, b)⟩ : Σ s, Valid m s × Step s ns) = ⟨s2, (a', b')⟩ := by
      rintro s1 _ rfl ⟨a, _⟩ ⟨b, _⟩ ⟨a', _⟩ ⟨b', _⟩ ha hb
      subst ha; subst hb; rfl
    exact hsigma hst_eq _ _ _ _ hf_eq htr

lemma cnt_succ (m : ℕ) (ns : State) :
    cnt (m + 1) ns = ∑ s : State, cnt m s * stepCard s ns := by
  classical
  unfold cnt stepCard
  rw [Nat.card_congr (splitStep m ns)]
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fintype.card_prod, Nat.card_eq_fintype_card]
  congr 1
  exact Fintype.card_subtype _

/-! #### Exact transfer-matrix computation and eigenvector induction -/

def v1 : State → ℕ
  | (false, false, false, false) => 3
  | (false, false, true, true) => 1
  | (false, true, true, false) => 1
  | (true, false, false, true) => 1
  | (true, true, false, false) => 2
  | (true, true, true, true) => 1
  | _ => 0

def v2 : State → ℕ
  | (false, false, false, false) => 16
  | (false, false, true, true) => 4
  | (false, true, true, false) => 4
  | (true, false, false, true) => 4
  | (true, true, false, false) => 12
  | (true, true, true, true) => 4
  | _ => 0

private lemma sum_state_eq (g : State → ℕ)
    (h0 : ∀ s : State, v1 s = 0 → g s = 0) :
    (∑ s : State, g s) =
      g (false, false, false, false) +
      g (false, false, true, true) +
      g (false, true, true, false) +
      g (true, false, false, true) +
      g (true, true, false, false) +
      g (true, true, true, true) := by
  have huniv : (Finset.univ : Finset State) =
      {(false, false, false, false), (false, false, false, true),
       (false, false, true, false), (false, false, true, true),
       (false, true, false, false), (false, true, false, true),
       (false, true, true, false), (false, true, true, true),
       (true, false, false, false), (true, false, false, true),
       (true, false, true, false), (true, false, true, true),
       (true, true, false, false), (true, true, false, true),
       (true, true, true, false), (true, true, true, true)} := by decide
  rw [huniv]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
    Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
    or_self, not_false_eq_true]
  rw [h0 (false, false, false, true) rfl,
      h0 (false, false, true, false) rfl,
      h0 (false, true, false, false) rfl,
      h0 (false, true, false, true) rfl,
      h0 (false, true, true, true) rfl,
      h0 (true, false, false, false) rfl,
      h0 (true, false, true, false) rfl,
      h0 (true, false, true, true) rfl,
      h0 (true, true, false, true) rfl,
      h0 (true, true, true, false) rfl]
  omega

private lemma stepCard_zero :
    ∀ ns : State, stepCard (false, false, false, false) ns = v1 ns := by
  decide

private lemma sum_v1_stepCard :
    ∀ ns : State,
      v1 (false, false, false, false) * stepCard (false, false, false, false) ns +
      v1 (false, false, true, true) * stepCard (false, false, true, true) ns +
      v1 (false, true, true, false) * stepCard (false, true, true, false) ns +
      v1 (true, false, false, true) * stepCard (true, false, false, true) ns +
      v1 (true, true, false, false) * stepCard (true, true, false, false) ns +
      v1 (true, true, true, true) * stepCard (true, true, true, true) ns = v2 ns := by
  decide

private lemma sum_v2_stepCard :
    ∀ ns : State,
      v2 (false, false, false, false) * stepCard (false, false, false, false) ns +
      v2 (false, false, true, true) * stepCard (false, false, true, true) ns +
      v2 (false, true, true, false) * stepCard (false, true, true, false) ns +
      v2 (true, false, false, true) * stepCard (true, false, false, true) ns +
      v2 (true, true, false, false) * stepCard (true, true, false, false) ns +
      v2 (true, true, true, true) * stepCard (true, true, true, true) ns = 5 * v2 ns := by
  decide

lemma cnt_one (ns : State) : cnt 1 ns = v1 ns := by
  rw [cnt_succ 0 ns]
  have hsum : (∑ s : State, cnt 0 s * stepCard s ns) =
      stepCard (false, false, false, false) ns := by
    rw [Finset.sum_eq_single (false, false, false, false)]
    · simp [cnt_zero]
    · intro s _ hs
      simp [cnt_zero, hs]
    · simp
  rw [hsum, stepCard_zero]

lemma cnt_two (ns : State) : cnt 2 ns = v2 ns := by
  rw [cnt_succ 1 ns]
  have h1 : (∑ s : State, cnt 1 s * stepCard s ns) =
      ∑ s : State, v1 s * stepCard s ns :=
    Finset.sum_congr rfl fun s _ => by rw [cnt_one]
  rw [h1, sum_state_eq _ (fun s hs => by simp [hs])]
  exact sum_v1_stepCard ns

lemma cnt_ge_two (k : ℕ) (ns : State) : cnt (k + 2) ns = v2 ns * 5 ^ k := by
  induction k generalizing ns with
  | zero => simp [cnt_two]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by omega, cnt_succ]
    have h1 : (∑ s : State, cnt (k + 2) s * stepCard s ns) =
        (∑ s : State, v2 s * stepCard s ns) * 5 ^ k := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [ih s]
      ring
    rw [h1, sum_state_eq _ (fun s hs => by
      have hv2 : v2 s = 0 := by
        rcases s with ⟨a, b, c, d⟩
        cases a <;> cases b <;> cases c <;> cases d <;> simp [v1, v2] at hs ⊢
      simp [hv2])]
    rw [sum_v2_stepCard ns]
    ring

lemma F_one : F 1 = 3 := by
  rw [F_eq_cnt, cnt_one]
  rfl

lemma F_ge_two {m : ℕ} (hm : 2 ≤ m) : F m = 16 * 5 ^ (m - 2) := by
  rw [F_eq_cnt, show m = (m - 2) + 2 by omega, cnt_ge_two]
  simp [v2]

/-! ### Part 3: Closed form for `a n` and generating series -/

lemma a_one : a 1 = 9 := by
  rw [a_eq_mul]
  norm_num [F_one]

lemma a_two : a 2 = 48 := by
  rw [a_eq_mul]
  norm_num [F_one, F_ge_two]

lemma a_three : a 3 = 256 := by
  rw [a_eq_mul]
  norm_num [F_ge_two]

lemma a_formula {n : ℕ} (hn : 2 < n) : a n = 256 * 5 ^ (n - 3) := by
  rw [a_eq_mul, F_ge_two (by omega), F_ge_two (by omega)]
  calc 16 * 5 ^ (n / 2 + 1 - 2) * (16 * 5 ^ ((n + 1) / 2 - 2))
      = 256 * (5 ^ (n / 2 + 1 - 2) * 5 ^ ((n + 1) / 2 - 2)) := by ring
    _ = 256 * 5 ^ ((n / 2 + 1 - 2) + ((n + 1) / 2 - 2)) := by rw [← pow_add]
    _ = 256 * 5 ^ (n - 3) := by congr 2; omega

open PowerSeries in
lemma gen_series :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
      (1 - 5 * X) = X * (9 + 3 * X + 16 * X ^ 2) := by
  set P : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ))
  have hL : P * (1 - 5 * X) = P - (5 : ℤ) • (P * X) := by
    rw [zsmul_eq_mul]; norm_num; ring
  have hR : X * (9 + 3 * X + 16 * X ^ 2) =
      (9 : ℤ) • (X : PowerSeries ℤ) ^ 1 + (3 : ℤ) • (X : PowerSeries ℤ) ^ 2 +
      (16 : ℤ) • (X : PowerSeries ℤ) ^ 3 := by
    simp only [zsmul_eq_mul]; norm_num; ring
  rw [hL, hR]
  ext k
  match k with
  | 0 =>
    simp only [P, map_sub, map_add, map_zsmul, coeff_zero_mul_X, coeff_X_pow, coeff_mk]
    norm_num
  | 1 =>
    simp only [P, map_sub, map_add, map_zsmul, coeff_succ_mul_X, coeff_X_pow, coeff_mk]
    norm_num [a_one]
  | 2 =>
    simp only [P, map_sub, map_add, map_zsmul, coeff_succ_mul_X, coeff_X_pow, coeff_mk]
    norm_num [a_one, a_two]
  | 3 =>
    simp only [P, map_sub, map_add, map_zsmul, coeff_succ_mul_X, coeff_X_pow, coeff_mk]
    norm_num [a_two, a_three]
  | m + 4 =>
    have h4 : a (m + 4) = 256 * 5 ^ (m + 1) := by simpa using a_formula (n := m + 4) (by omega)
    have h3 : a (m + 3) = 256 * 5 ^ m := by simpa using a_formula (n := m + 3) (by omega)
    simp only [P, map_sub, map_add, map_zsmul, coeff_succ_mul_X, coeff_X_pow, coeff_mk]
    have hne0 : m + 4 ≠ 0 := by omega
    have hne0' : m + 3 ≠ 0 := by omega
    have hne1 : m + 4 ≠ 1 := by omega
    have hne2 : m + 4 ≠ 2 := by omega
    have hne3 : m + 4 ≠ 3 := by omega
    simp only [hne0, hne0', hne1, hne2, hne3, ↓reduceIte, smul_zero, add_zero, zsmul_eq_mul]
    rw [h4, h3]
    push_cast
    ring

end A264273

theorem OMA.solution : type_of% @OMA.S_oeis_a264273.main :=
  ⟨A264273.gen_series, fun _ hn => A264273.a_formula hn⟩
