import OMAStatements.S_arxiv_2609_22667

open OMA.S_arxiv_2609_22667

namespace OMA.P_arxiv_2609_22667

/-! ### Section 1: Theorem 2.1 — Classification of Compatible Additions & Isomorphisms -/

private lemma addR_compat (i j : Fin 3) : IsCompatAdd (addR i j) := by
  fin_cases i <;> fin_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide⟩

private lemma mulM_diag (x : Elem6) : mulM x x = .zero := by
  cases x <;> rfl

private lemma mulM_comm (x y : Elem6) : mulM x y = mulM y x := by
  cases x <;> cases y <;> rfl

private lemma mulM_zero_or_c (x y : Elem6) : mulM x y = .zero ∨ mulM x y = .c := by
  cases x <;> cases y <;> simp [mulM]

private lemma compat_eq_addR {add : Elem6 → Elem6 → Elem6} (h : IsCompatAdd add) :
    ∃ i j : Fin 3, add = addR i j := by
  rcases h with ⟨hassoc, hcomm, hidem, hld, hrd⟩
  -- Step 1: `add .zero .c = .zero` via `(a + b) * (a + b) = 0`.
  have hzc : add .zero .c = .zero := by
    have h1 : mulM (add .a .b) (add .a .b) = .zero := mulM_diag _
    rw [hld, hrd, hrd] at h1
    have h2 : mulM .a .a = .zero := rfl
    have h3 : mulM .b .a = .c := rfl
    have h4 : mulM .a .b = .c := rfl
    have h5 : mulM .b .b = .zero := rfl
    rw [h2, h3, h4, h5] at h1
    -- `add (add .zero .c) (add .c .zero) = .zero`
    rw [hcomm .c .zero, hidem] at h1
    exact h1
  have hcz : add .c .zero = .zero := by rw [hcomm, hzc]
  -- Step 2: `∀ s, add s .zero = .zero`.
  have hsz : ∀ s : Elem6, add s .zero = .zero := by
    intro s
    have hmul : ∀ t : Elem6, mulM (add s .zero) t = .zero := by
      intro t
      rw [hrd]
      have h0 : mulM .zero t = .zero := by cases t <;> rfl
      rw [h0]
      rcases mulM_zero_or_c s t with hm | hm <;> rw [hm]
      · exact hidem .zero
      · exact hcz
    have hmem : add s .zero = .zero ∨ add s .zero = .c := by
      cases hval : add s .zero with
      | zero => left; rfl
      | c => right; rfl
      | p => exfalso; have := hmul .b; rw [hval] at this; cases this
      | q => exfalso; have := hmul .a; rw [hval] at this; cases this
      | a => exfalso; have := hmul .b; rw [hval] at this; cases this
      | b => exfalso; have := hmul .a; rw [hval] at this; cases this
    rcases hmem with h0 | hc
    · exact h0
    · exfalso
      have h1 : add (add s .zero) .zero = add s (add .zero .zero) := hassoc s .zero .zero
      rw [hidem, hc, hcz] at h1
      cases h1
  have hzs : ∀ s : Elem6, add .zero s = .zero := fun s => by rw [hcomm, hsz]
  -- Step 3: Neighborhood intersection `mulM (add s t) v = .c ↔ mulM s v = .c ∧ mulM t v = .c`.
  have hnbhd : ∀ s t v : Elem6, mulM (add s t) v = .c ↔ mulM s v = .c ∧ mulM t v = .c := by
    intro s t v
    rw [hrd]
    rcases mulM_zero_or_c s v with hs | hs <;> rcases mulM_zero_or_c t v with ht | ht <;>
      rw [hs, ht]
    · simp [hidem .zero]
    · simp [hzs .c]
    · simp [hsz .c]
    · simp [hidem .c]
  -- Step 4: `add .a .p = .p` and `add .b .q = .q`.
  have hap : add .a .p = .p := by
    have hb : mulM (add .a .p) .b = .c := (hnbhd .a .p .b).mpr ⟨rfl, rfl⟩
    have hq : mulM (add .a .p) .q ≠ .c := by
      intro h1; have := ((hnbhd .a .p .q).mp h1).2; cases this
    cases hval : add .a .p with
    | p => rfl
    | zero => rw [hval] at hb; cases hb
    | c => rw [hval] at hb; cases hb
    | q => rw [hval] at hb; cases hb
    | b => rw [hval] at hb; cases hb
    | a => rw [hval] at hq; exact absurd rfl hq
  have hpa : add .p .a = .p := by rw [hcomm, hap]
  have hbq : add .b .q = .q := by
    have ha : mulM (add .b .q) .a = .c := (hnbhd .b .q .a).mpr ⟨rfl, rfl⟩
    have hp : mulM (add .b .q) .p ≠ .c := by
      intro h1; have := ((hnbhd .b .q .p).mp h1).2; cases this
    cases hval : add .b .q with
    | q => rfl
    | zero => rw [hval] at ha; cases ha
    | c => rw [hval] at ha; cases ha
    | p => rw [hval] at ha; cases ha
    | a => rw [hval] at ha; cases ha
    | b => rw [hval] at hp; exact absurd rfl hp
  have hqb : add .q .b = .q := by rw [hcomm, hbq]
  -- Step 5: Any pair `(s, t)` with disjoint neighborhoods has `add s t ∈ {.zero, .c}`.
  have hdisj_zc : ∀ s t : Elem6, (∀ v, ¬ (mulM s v = .c ∧ mulM t v = .c)) →
      add s t = .zero ∨ add s t = .c := by
    intro s t hd
    have hno : ∀ v, mulM (add s t) v ≠ .c := fun v hv => hd v ((hnbhd s t v).mp hv)
    cases hval : add s t with
    | zero => left; rfl
    | c => right; rfl
    | p => exfalso; exact hno .b (by rw [hval]; rfl)
    | q => exfalso; exact hno .a (by rw [hval]; rfl)
    | a => exfalso; exact hno .b (by rw [hval]; rfl)
    | b => exfalso; exact hno .a (by rw [hval]; rfl)
  -- Step 6: Extract `i` from `add .a .c`, `add .p .c` and `j` from `add .b .c`, `add .q .c`.
  have hxc_zc : ∀ x : Elem6, x ≠ .c → add x .c = .zero ∨ add x .c = .c := fun x _ =>
    hdisj_zc x .c (fun v hv => by cases v <;> cases hv.2)
  have hpc_imp_ac : add .p .c = .c → add .a .c = .c := by
    intro hp
    calc add .a .c = add .a (add .p .c) := by rw [hp]
      _ = add (add .a .p) .c := (hassoc .a .p .c).symm
      _ = add .p .c := by rw [hap]
      _ = .c := hp
  have hqc_imp_bc : add .q .c = .c → add .b .c = .c := by
    intro hq
    calc add .b .c = add .b (add .q .c) := by rw [hq]
      _ = add (add .b .q) .c := (hassoc .b .q .c).symm
      _ = add .q .c := by rw [hbq]
      _ = .c := hq
  let i : Fin 3 := if add .p .c = .c then 2 else if add .a .c = .c then 1 else 0
  let j : Fin 3 := if add .q .c = .c then 2 else if add .b .c = .c then 1 else 0
  have hbelow_iff : ∀ x : Elem6, x ≠ .zero → (belowC i j x = true ↔ add x .c = .c) := by
    intro x hx
    cases x with
    | zero => exact absurd rfl hx
    | c => simp [belowC, hidem .c]
    | a =>
      dsimp only [belowC, i]
      by_cases hp : add .p .c = .c
      · simp [hp, hpc_imp_ac hp]
      · by_cases ha : add .a .c = .c <;> simp [hp, ha]
    | p =>
      dsimp only [belowC, i]
      by_cases hp : add .p .c = .c
      · simp [hp]
      · by_cases ha : add .a .c = .c <;> simp [hp, ha]
    | b =>
      dsimp only [belowC, j]
      by_cases hq : add .q .c = .c
      · simp [hq, hqc_imp_bc hq]
      · by_cases hb : add .b .c = .c <;> simp [hq, hb]
    | q =>
      dsimp only [belowC, j]
      by_cases hq : add .q .c = .c
      · simp [hq]
      · by_cases hb : add .b .c = .c <;> simp [hq, hb]
  -- Step 7: For any disjoint-neighborhood pair `(x, y)` (neither `zero`), `add x y = .c ↔ add x .c = .c ∧ add y .c = .c`.
  have hcross : ∀ x y : Elem6, x ≠ .zero → y ≠ .zero →
      (∀ v, ¬ (mulM x v = .c ∧ mulM y v = .c)) →
      (add x y = .c ↔ add x .c = .c ∧ add y .c = .c) := by
    intro x y _ _ hdisj
    constructor
    · intro hxy
      constructor
      · calc add x .c = add x (add x y) := by rw [hxy]
          _ = add (add x x) y := (hassoc x x y).symm
          _ = add x y := by rw [hidem]
          _ = .c := hxy
      · calc add y .c = add y (add x y) := by rw [hxy]
          _ = add y (add y x) := by rw [hcomm x y]
          _ = add (add y y) x := (hassoc y y x).symm
          _ = add y x := by rw [hidem]
          _ = add x y := hcomm y x
          _ = .c := hxy
    · rintro ⟨hx, hy⟩
      rcases hdisj_zc x y hdisj with h0 | hc
      · exfalso
        have h1 : add (add x y) .c = add x (add y .c) := hassoc x y .c
        rw [h0, hy, hzc, hx] at h1
        cases h1
      · exact hc
  have hpair : ∀ x y : Elem6, x ≠ y → x ≠ .zero → y ≠ .zero →
      ¬ ((x = .a ∧ y = .p) ∨ (x = .p ∧ y = .a)) →
      ¬ ((x = .b ∧ y = .q) ∨ (x = .q ∧ y = .b)) →
      (∀ v, ¬ (mulM x v = .c ∧ mulM y v = .c)) →
      add x y = addR i j x y := by
    intro x y hxy hx0 hy0 hnap hnbq hd
    have hzc_xy := hdisj_zc x y hd
    have hiff := hcross x y hx0 hy0 hd
    have haddR : addR i j x y = if belowC i j x && belowC i j y then .c else .zero := by
      unfold addR
      rw [if_neg hxy, if_neg (by tauto), if_neg hnap, if_neg hnbq]
    rw [haddR]
    by_cases hcond : (belowC i j x && belowC i j y) = true
    · rw [if_pos hcond]
      rw [Bool.and_eq_true] at hcond
      exact hiff.mpr ⟨(hbelow_iff x hx0).mp hcond.1, (hbelow_iff y hy0).mp hcond.2⟩
    · rw [if_neg hcond]
      rcases hzc_xy with h0 | hc
      · exact h0
      · exfalso
        obtain ⟨hx, hy⟩ := hiff.mp hc
        exact hcond (Bool.and_eq_true _ _ |>.mpr ⟨(hbelow_iff x hx0).mpr hx, (hbelow_iff y hy0).mpr hy⟩)
  refine ⟨i, j, funext fun x => funext fun y => ?_⟩
  by_cases hxy : x = y
  · subst hxy; simp [addR, hidem]
  · cases x <;> cases y <;> try (exact absurd rfl hxy)
    all_goals try (simp [addR, hsz, hzs, hap, hpa, hbq, hqb]; done)
    all_goals exact hpair _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private lemma addR_injective : Function.Injective fun p : Fin 3 × Fin 3 => addR p.1 p.2 := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have ha := congrFun (congrFun h .a) .c
  have hp := congrFun (congrFun h .p) .c
  have hb := congrFun (congrFun h .b) .c
  have hq := congrFun (congrFun h .q) .c
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [addR, belowC] at ha hp hb hq ⊢

private def refl6 : Elem6 ≃ Elem6 where
  toFun
    | .zero => .zero
    | .c => .c
    | .a => .b
    | .b => .a
    | .p => .q
    | .q => .p
  invFun
    | .zero => .zero
    | .c => .c
    | .a => .b
    | .b => .a
    | .p => .q
    | .q => .p
  left_inv := fun x => by cases x <;> rfl
  right_inv := fun x => by cases x <;> rfl

private lemma addIso_iff (i j i' j' : Fin 3) :
    AddIso (addR i j) (addR i' j') ↔ (i = i' ∧ j = j') ∨ (i = j' ∧ j = i') := by
  constructor
  · rintro ⟨e, hmul, hadd⟩
    have he0 : e .zero = .zero := by
      have := hmul .zero .zero
      rw [mulM_diag, mulM_diag] at this
      exact this
    have hec : e .c = .c := by
      have h1 : e .c = mulM (e .a) (e .b) := by
        have := hmul .a .b; exact this
      rcases mulM_zero_or_c (e .a) (e .b) with h0 | hc
      · exfalso; rw [h0] at h1; exact absurd (e.injective (h1.trans he0.symm)) (by decide)
      · exact h1.trans hc
    -- `e` maps `{a, b}` to `{a, b}` (the only elements with 2 nonzero products)
    have hdeg : ∀ x : Elem6, (Finset.univ.filter fun y => mulM (e x) y = .c).card =
        (Finset.univ.filter fun y => mulM x y = .c).card := fun x => by
      refine Finset.card_bij (fun y _ => e.symm y) ?_ ?_ ?_
      · intro y hy
        rw [Finset.mem_filter] at hy ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        apply e.injective
        rw [hmul, e.apply_symm_apply, hec]; exact hy.2
      · intro y₁ _ y₂ _ h; exact e.symm.injective h
      · intro y hy
        rw [Finset.mem_filter] at hy
        refine ⟨e y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.symm_apply_apply y⟩
        rw [← hmul, hy.2, hec]
    have hdeg_val : ∀ z : Elem6, (Finset.univ.filter fun y => mulM z y = .c).card =
        match z with | .a => 2 | .b => 2 | .p => 1 | .q => 1 | .zero => 0 | .c => 0 := fun z => by
      cases z <;> decide
    have hea : e .a = .a ∨ e .a = .b := by
      have hd := hdeg .a
      cases h : e .a <;> rw [h] at hd <;> simp only [hdeg_val] at hd <;> try contradiction
      · left; rfl
      · right; rfl
    rcases hea with ha_eq | ha_eq
    · -- `e = id` on `a, b, p, q`
      have hq_eq : e .q = .q := by
        have h1 : mulM .a (e .q) = .c := by rw [← ha_eq, ← hmul]; exact hec
        have hd := hdeg .q
        cases h : e .q <;> rw [h] at h1 hd <;> simp only [mulM] at h1 hd <;> try contradiction
      have hb_eq : e .b = .b := by
        have h1 : mulM (e .a) (e .b) = .c := by rw [← hmul]; exact hec
        rw [ha_eq] at h1
        have hne : e .b ≠ .q := fun h => absurd (e.injective (h.trans hq_eq.symm)) (by decide)
        cases h : e .b <;> rw [h] at h1 hne <;> simp [mulM] at h1 hne
      have hp_eq : e .p = .p := by
        have h1 : mulM (e .b) (e .p) = .c := by rw [← hmul]; exact hec
        rw [hb_eq] at h1
        have hne : e .p ≠ .a := fun h => absurd (e.injective (h.trans ha_eq.symm)) (by decide)
        cases h : e .p <;> rw [h] at h1 hne <;> simp [mulM] at h1 hne
      have he_id : ∀ x, e x = x := fun x => by cases x <;> assumption
      have heq : addR i j = addR i' j' := funext fun x => funext fun y => by
        have := hadd x y; rwa [he_id, he_id, he_id] at this
      have hp := addR_injective (a₁ := (i, j)) (a₂ := (i', j')) heq
      left; exact Prod.mk.inj hp
    · -- `e = refl6`
      have hq_eq : e .q = .p := by
        have h1 : mulM (e .a) (e .q) = .c := by rw [← hmul]; exact hec
        rw [ha_eq] at h1
        have hd := hdeg .q
        cases h : e .q <;> rw [h] at h1 hd <;> simp only [mulM] at h1 hd <;> try contradiction
      have hb_eq : e .b = .a := by
        have h1 : mulM (e .a) (e .b) = .c := by rw [← hmul]; exact hec
        rw [ha_eq] at h1
        have hne : e .b ≠ .p := fun h => absurd (e.injective (h.trans hq_eq.symm)) (by decide)
        cases h : e .b <;> rw [h] at h1 hne <;> simp [mulM] at h1 hne
      have hp_eq : e .p = .q := by
        have h1 : mulM (e .b) (e .p) = .c := by rw [← hmul]; exact hec
        rw [hb_eq] at h1
        have hne : e .p ≠ .b := fun h => absurd (e.injective (h.trans ha_eq.symm)) (by decide)
        cases h : e .p <;> rw [h] at h1 hne <;> simp [mulM] at h1 hne
      have he_r : ∀ x, e x = refl6 x := fun x => by cases x <;> simp [refl6, *]
      have hadd_r : ∀ x y, refl6 (addR i j x y) = addR i' j' (refl6 x) (refl6 y) := fun x y => by
        have := hadd x y; rwa [he_r, he_r, he_r] at this
      have ha' := hadd_r .a .c
      have hp' := hadd_r .p .c
      have hb' := hadd_r .b .c
      have hq' := hadd_r .q .c
      fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
        simp [refl6, addR, belowC] at ha' hp' hb' hq' ⊢
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Equiv.refl _, fun _ _ => rfl, fun _ _ => rfl⟩
    · refine ⟨refl6, fun x y => by cases x <;> cases y <;> rfl, fun x y => ?_⟩
      fin_cases i <;> fin_cases j <;> cases x <;> cases y <;> rfl

/-! ### Section 2: Polynomial Normal Forms and Equational Equivalence -/

private abbrev Mon := Multiset ℕ
private abbrev Poly := Finset Mon

private def mulPoly (P Q : Poly) : Poly :=
  P.biUnion fun m₁ => Q.image fun m₂ => m₁ + m₂

private def toPoly : SemiringTerm → Poly
  | .var n => {{n}}
  | .add s t => (toPoly s) ∪ (toPoly t)
  | .mul s t => mulPoly (toPoly s) (toPoly t)

private lemma mem_mulPoly {P Q : Poly} {m : Mon} :
    m ∈ mulPoly P Q ↔ ∃ m₁ ∈ P, ∃ m₂ ∈ Q, m₁ + m₂ = m := by
  simp [mulPoly]

private lemma toPoly_nonempty (s : SemiringTerm) : (toPoly s).Nonempty := by
  induction s with
  | var n => exact ⟨{n}, by simp [toPoly]⟩
  | add s t ihs _ =>
    obtain ⟨m, hm⟩ := ihs; exact ⟨m, Finset.mem_union_left _ hm⟩
  | mul s t ihs iht =>
    obtain ⟨m₁, h1⟩ := ihs; obtain ⟨m₂, h2⟩ := iht
    exact ⟨m₁ + m₂, mem_mulPoly.mpr ⟨m₁, h1, m₂, h2, rfl⟩⟩

private lemma toPoly_card_pos (s : SemiringTerm) {m : Mon} (hm : m ∈ (toPoly s)) : 1 ≤ m.card := by
  induction s generalizing m with
  | var n =>
    simp only [toPoly, Finset.mem_singleton] at hm
    subst hm; simp
  | add s t ihs iht =>
    rcases Finset.mem_union.mp hm with h | h
    · exact ihs h
    · exact iht h
  | mul s t ihs iht =>
    obtain ⟨m₁, h1, m₂, h2, rfl⟩ := mem_mulPoly.mp hm
    have := ihs h1; have := iht h2; simp; omega

-- Cleaner recursive monomial evaluation under a substitution `σ`:
private def substMonPoly (σ : ℕ → SemiringTerm) : List ℕ → Poly
  | [] => {0}
  | [x] => (toPoly (σ x))
  | x :: xs => mulPoly (toPoly (σ x)) (substMonPoly σ xs)

private lemma mulPoly_assoc (P Q R : Poly) : mulPoly (mulPoly P Q) R = mulPoly P (mulPoly Q R) := by
  ext m; simp only [mem_mulPoly]
  constructor
  · rintro ⟨m₁₂, ⟨m₁, h1, m₂, h2, rfl⟩, m₃, h3, rfl⟩
    exact ⟨m₁, h1, m₂ + m₃, ⟨m₂, h2, m₃, h3, rfl⟩, (add_assoc _ _ _).symm⟩
  · rintro ⟨m₁, h1, m₂₃, ⟨m₂, h2, m₃, h3, rfl⟩, rfl⟩
    exact ⟨m₁ + m₂, ⟨m₁, h1, m₂, h2, rfl⟩, m₃, h3, add_assoc _ _ _⟩

private lemma mulPoly_comm (P Q : Poly) : mulPoly P Q = mulPoly Q P := by
  ext m; simp only [mem_mulPoly]
  constructor
  · rintro ⟨m₁, h1, m₂, h2, rfl⟩; exact ⟨m₂, h2, m₁, h1, add_comm _ _⟩
  · rintro ⟨m₁, h1, m₂, h2, rfl⟩; exact ⟨m₂, h2, m₁, h1, add_comm _ _⟩

private lemma mulPoly_union_left (P Q R : Poly) :
    mulPoly (P ∪ Q) R = mulPoly P R ∪ mulPoly Q R := by
  ext m; simp only [mem_mulPoly, Finset.mem_union]
  constructor
  · rintro ⟨m₁, h1 | h1, m₂, h2, rfl⟩
    · left; exact ⟨m₁, h1, m₂, h2, rfl⟩
    · right; exact ⟨m₁, h1, m₂, h2, rfl⟩
  · rintro (⟨m₁, h1, m₂, h2, rfl⟩ | ⟨m₁, h1, m₂, h2, rfl⟩)
    · exact ⟨m₁, Or.inl h1, m₂, h2, rfl⟩
    · exact ⟨m₁, Or.inr h1, m₂, h2, rfl⟩

private lemma mulPoly_union_right (P Q R : Poly) :
    mulPoly P (Q ∪ R) = mulPoly P Q ∪ mulPoly P R := by
  rw [mulPoly_comm, mulPoly_union_left, mulPoly_comm Q P, mulPoly_comm R P]

private lemma mulPoly_mono {P₁ P₂ Q₁ Q₂ : Poly} (hP : P₁ ⊆ P₂) (hQ : Q₁ ⊆ Q₂) :
    mulPoly P₁ Q₁ ⊆ mulPoly P₂ Q₂ := by
  intro m hm
  obtain ⟨m₁, h1, m₂, h2, rfl⟩ := mem_mulPoly.mp hm
  exact mem_mulPoly.mpr ⟨m₁, hP h1, m₂, hQ h2, rfl⟩

private lemma mulPoly_nonempty {P Q : Poly} (hP : P.Nonempty) (hQ : Q.Nonempty) :
    (mulPoly P Q).Nonempty := by
  obtain ⟨m₁, h1⟩ := hP; obtain ⟨m₂, h2⟩ := hQ
  exact ⟨m₁ + m₂, mem_mulPoly.mpr ⟨m₁, h1, m₂, h2, rfl⟩⟩

private lemma substMonPoly_perm (σ : ℕ → SemiringTerm) {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) :
    substMonPoly σ l₁ = substMonPoly σ l₂ := by
  induction h with
  | nil => rfl
  | @cons x l₁ l₂ h ih =>
    cases l₁ with
    | nil => rw [h.nil_eq]
    | cons y ys =>
      have hne : l₂ ≠ [] := fun h0 => by rw [h0] at h; cases h.symm.nil_eq
      cases l₂ with
      | nil => exact absurd rfl hne
      | cons z zs => simp only [substMonPoly, ih]
  | @swap x y l =>
    cases l with
    | nil => simp only [substMonPoly]; exact mulPoly_comm _ _
    | cons z zs =>
      simp only [substMonPoly]
      rw [← mulPoly_assoc, mulPoly_comm (toPoly (σ y)) (toPoly (σ x)), mulPoly_assoc]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private lemma substMonPoly_append (σ : ℕ → SemiringTerm) {l₁ l₂ : List ℕ}
    (h1 : l₁ ≠ []) (h2 : l₂ ≠ []) :
    substMonPoly σ (l₁ ++ l₂) = mulPoly (substMonPoly σ l₁) (substMonPoly σ l₂) := by
  induction l₁ with
  | nil => exact absurd rfl h1
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases l₂ with
      | nil => exact absurd rfl h2
      | cons y ys => rfl
    | cons y ys =>
      have hsub := ih (by simp)
      simp only [List.cons_append] at hsub ⊢
      simp only [substMonPoly]
      rw [hsub, mulPoly_assoc]

private def substMon (σ : ℕ → SemiringTerm) (m : Mon) : Poly :=
  Quot.liftOn m (substMonPoly σ) (fun _ _ h => substMonPoly_perm σ h)

private lemma substMon_singleton (σ : ℕ → SemiringTerm) (x : ℕ) :
    substMon σ ({x} : Mon) = (toPoly (σ x)) := rfl

private lemma substMon_add (σ : ℕ → SemiringTerm) {m₁ m₂ : Mon} (h1 : m₁ ≠ 0) (h2 : m₂ ≠ 0) :
    substMon σ (m₁ + m₂) = mulPoly (substMon σ m₁) (substMon σ m₂) := by
  induction m₁ using Quot.inductionOn with | _ l₁ =>
  induction m₂ using Quot.inductionOn with | _ l₂ =>
  have hl1 : l₁ ≠ [] := fun h => h1 (by subst h; rfl)
  have hl2 : l₂ ≠ [] := fun h => h2 (by subst h; rfl)
  exact substMonPoly_append σ hl1 hl2

private lemma toPoly_subst_eq (σ : ℕ → SemiringTerm) (s : SemiringTerm) :
    (toPoly (s.subst σ)) = (toPoly s).biUnion (substMon σ) := by
  induction s with
  | var n => simp [SemiringTerm.subst, toPoly, substMon_singleton]
  | add s t ihs iht =>
    simp only [SemiringTerm.subst, toPoly, ihs, iht]
    ext m; simp only [Finset.mem_union, Finset.mem_biUnion]
    exact ⟨fun h => h.elim (fun ⟨a, ha, hm⟩ => ⟨a, Or.inl ha, hm⟩) (fun ⟨a, ha, hm⟩ => ⟨a, Or.inr ha, hm⟩),
           fun ⟨a, ha, hm⟩ => ha.elim (fun h => Or.inl ⟨a, h, hm⟩) (fun h => Or.inr ⟨a, h, hm⟩)⟩
  | mul s t ihs iht =>
    simp only [SemiringTerm.subst, toPoly, ihs, iht]
    ext m
    simp only [mem_mulPoly, Finset.mem_biUnion]
    constructor
    · rintro ⟨a, ⟨m₁, hm₁, ha⟩, b, ⟨m₂, hm₂, hb⟩, rfl⟩
      have h1 : m₁ ≠ 0 := by intro h0; have := toPoly_card_pos s hm₁; simp [h0] at this
      have h2 : m₂ ≠ 0 := by intro h0; have := toPoly_card_pos t hm₂; simp [h0] at this
      refine ⟨m₁ + m₂, ⟨m₁, hm₁, m₂, hm₂, rfl⟩, ?_⟩
      rw [substMon_add σ h1 h2]
      exact mem_mulPoly.mpr ⟨a, ha, b, hb, rfl⟩
    · rintro ⟨m', ⟨m₁, hm₁, m₂, hm₂, rfl⟩, hm⟩
      have h1 : m₁ ≠ 0 := by intro h0; have := toPoly_card_pos s hm₁; simp [h0] at this
      have h2 : m₂ ≠ 0 := by intro h0; have := toPoly_card_pos t hm₂; simp [h0] at this
      rw [substMon_add σ h1 h2] at hm
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_mulPoly.mp hm
      exact ⟨a, ⟨m₁, hm₁, ha⟩, b, ⟨m₂, hm₂, hb⟩, rfl⟩

/-! ### Evaluation via Polynomials -/

private def evalMonList (v : ℕ → Elem6) : List ℕ → Elem6
  | [] => .zero
  | [x] => v x
  | [x, y] => mulM (v x) (v y)
  | _ :: _ :: _ :: _ => .zero

private lemma evalMonList_perm (v : ℕ → Elem6) {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) :
    evalMonList v l₁ = evalMonList v l₂ := by
  have hlen := h.length_eq
  cases l₁ with
  | nil => rw [h.nil_eq]
  | cons a l₁ =>
    cases l₁ with
    | nil =>
      cases l₂ with
      | nil => simp at hlen
      | cons b l₂ =>
        cases l₂ with
        | nil =>
          have : a = b := by
            have := h.subset (List.mem_cons_self ..); simpa using this
          simp [evalMonList, this]
        | cons _ _ => simp at hlen
    | cons b l₁ =>
      cases l₁ with
      | nil =>
        cases l₂ with
        | nil => simp at hlen
        | cons c l₂ =>
          cases l₂ with
          | nil => simp at hlen
          | cons d l₂ =>
            cases l₂ with
            | nil =>
              have h1 := h.subset (List.mem_cons_self ..)
              have h2 := h.subset (List.mem_cons_of_mem _ (List.mem_cons_self ..))
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
              rcases h1 with rfl | rfl
              · have hbd : b = d := by
                  have h' := h.cons_inv; have := h'.subset (List.mem_cons_self ..); simpa using this
                subst hbd; rfl
              · have hbc : b = c := by
                  have h' := (List.Perm.swap c a []).trans h.symm
                  have h'' := h'.cons_inv; have := h''.subset (List.mem_cons_self ..); simpa [eq_comm] using this
                subst hbc; exact mulM_comm _ _
            | cons _ _ => simp at hlen
      | cons c l₁ =>
        cases l₂ with
        | nil => simp at hlen
        | cons _ l₂ =>
          cases l₂ with
          | nil => simp at hlen
          | cons _ l₂ =>
            cases l₂ with
            | nil => simp at hlen
            | cons _ _ => rfl

private def evalMon (v : ℕ → Elem6) (m : Mon) : Elem6 :=
  Quot.liftOn m (evalMonList v) (fun _ _ h => evalMonList_perm v h)

private lemma evalMon_singleton (v : ℕ → Elem6) (x : ℕ) : evalMon v {x} = v x := rfl

private lemma evalMon_pair (v : ℕ → Elem6) (x y : ℕ) : evalMon v {x, y} = mulM (v x) (v y) := rfl

private lemma evalMon_card_ge_three (v : ℕ → Elem6) {m : Mon} (h : 3 ≤ m.card) :
    evalMon v m = .zero := by
  induction m using Quot.inductionOn with | _ l =>
  cases l with
  | nil => simp at h
  | cons _ l =>
    cases l with
    | nil => simp at h
    | cons _ l =>
      cases l with
      | nil => simp at h
      | cons _ _ => rfl

private lemma evalMon_add (v : ℕ → Elem6) {m₁ m₂ : Mon} (h1 : 1 ≤ m₁.card) (h2 : 1 ≤ m₂.card) :
    evalMon v (m₁ + m₂) = mulM (evalMon v m₁) (evalMon v m₂) := by
  induction m₁ using Quot.inductionOn with | _ l₁ =>
  induction m₂ using Quot.inductionOn with | _ l₂ =>
  cases l₁ with
  | nil => simp at h1
  | cons a l₁ =>
    cases l₂ with
    | nil => simp at h2
    | cons b l₂ =>
      cases l₁ with
      | nil =>
        cases l₂ with
        | nil => rfl
        | cons c l₂ =>
          change evalMonList v (a :: b :: c :: l₂) = mulM (v a) (evalMonList v (b :: c :: l₂))
          cases l₂ with
          | nil =>
            simp only [evalMonList]
            rcases mulM_zero_or_c (v b) (v c) with hm | hm <;> rw [hm] <;> cases v a <;> rfl
          | cons d l₂ =>
            simp only [evalMonList]; cases v a <;> rfl
      | cons c l₁ =>
        change evalMonList v (a :: c :: (l₁ ++ b :: l₂)) = mulM (evalMonList v (a :: c :: l₁)) (evalMonList v (b :: l₂))
        have hlen : 3 ≤ (a :: c :: (l₁ ++ b :: l₂)).length := by simp; omega
        have hlhs : evalMonList v (a :: c :: (l₁ ++ b :: l₂)) = .zero := by
          cases htail : l₁ ++ b :: l₂ with
          | nil => rw [htail] at hlen; simp at hlen
          | cons _ _ => rfl
        rw [hlhs]
        cases l₁ with
        | nil =>
          simp only [evalMonList]
          rcases mulM_zero_or_c (v a) (v c) with hm | hm <;> rw [hm] <;> cases evalMonList v (b :: l₂) <;> rfl
        | cons d l₁ =>
          simp only [evalMonList]; cases evalMonList v (b :: l₂) <;> rfl

/-- Additive order `x ≤_R y` in `R_{ij}`: `addR i j x y = y`. -/
private def leR (i j : Fin 3) (x y : Elem6) : Prop := addR i j x y = y

private lemma addR_assoc' (i j : Fin 3) (x y z : Elem6) :
    addR i j (addR i j x y) z = addR i j x (addR i j y z) := (addR_compat i j).1 x y z

private lemma addR_comm' (i j : Fin 3) (x y : Elem6) :
    addR i j x y = addR i j y x := (addR_compat i j).2.1 x y

private lemma addR_idem' (i j : Fin 3) (x : Elem6) :
    addR i j x x = x := (addR_compat i j).2.2.1 x

private lemma addR_zero_left (i j : Fin 3) (x : Elem6) : addR i j .zero x = .zero := by
  fin_cases i <;> fin_cases j <;> cases x <;> rfl

private lemma addR_zero_right (i j : Fin 3) (x : Elem6) : addR i j x .zero = .zero := by
  rw [addR_comm', addR_zero_left]

private lemma addR_ldistrib (i j : Fin 3) (x y z : Elem6) :
    mulM x (addR i j y z) = addR i j (mulM x y) (mulM x z) := (addR_compat i j).2.2.2.1 x y z

private lemma addR_rdistrib (i j : Fin 3) (x y z : Elem6) :
    mulM (addR i j x y) z = addR i j (mulM x z) (mulM y z) := (addR_compat i j).2.2.2.2 x y z

/-- Evaluate a nonempty polynomial `P` in `R_{ij}` by folding `addR i j` over `P`!
For empty `P` (never used on `(toPoly s)`), returns `.zero`. -/
private def evalPolyList (i j : Fin 3) (v : ℕ → Elem6) : List Mon → Elem6
  | [] => .zero
  | [m] => evalMon v m
  | m :: ms => addR i j (evalMon v m) (evalPolyList i j v ms)

private lemma evalPolyList_perm (i j : Fin 3) (v : ℕ → Elem6) {l₁ l₂ : List Mon} (h : l₁.Perm l₂) :
    evalPolyList i j v l₁ = evalPolyList i j v l₂ := by
  induction h with
  | nil => rfl
  | @cons m l₁ l₂ h ih =>
    cases l₁ with
    | nil => rw [h.nil_eq]
    | cons a as =>
      cases l₂ with
      | nil => cases h.symm.nil_eq
      | cons b bs => simp only [evalPolyList, ih]
  | @swap m₁ m₂ l =>
    cases l with
    | nil => simp only [evalPolyList, addR_comm']
    | cons a as =>
      simp only [evalPolyList]
      rw [← addR_assoc', addR_comm' i j (evalMon v m₂) (evalMon v m₁), addR_assoc']
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private lemma evalPolyList_append (i j : Fin 3) (v : ℕ → Elem6) {l₁ l₂ : List Mon}
    (h1 : l₁ ≠ []) (h2 : l₂ ≠ []) :
    evalPolyList i j v (l₁ ++ l₂) = addR i j (evalPolyList i j v l₁) (evalPolyList i j v l₂) := by
  induction l₁ with
  | nil => exact absurd rfl h1
  | cons a as ih =>
    cases as with
    | nil =>
      cases l₂ with
      | nil => exact absurd rfl h2
      | cons b bs => rfl
    | cons b bs =>
      have hih := ih (by simp)
      simp only [List.cons_append] at hih ⊢
      simp only [evalPolyList]
      rw [hih, addR_assoc']

private def evalPoly (i j : Fin 3) (v : ℕ → Elem6) (P : Poly) : Elem6 :=
  Quot.liftOn P.val (evalPolyList i j v) (fun _ _ h => evalPolyList_perm i j v h)

private lemma evalPoly_singleton (i j : Fin 3) (v : ℕ → Elem6) (m : Mon) :
    evalPoly i j v {m} = evalMon v m := rfl

private lemma evalPoly_insert (i j : Fin 3) (v : ℕ → Elem6) {m : Mon} {P : Poly} (hP : P.Nonempty) :
    evalPoly i j v (insert m P) = addR i j (evalMon v m) (evalPoly i j v P) := by
  by_cases hm : m ∈ P
  · rw [Finset.insert_eq_of_mem hm]
    obtain ⟨Q, hQ⟩ : ∃ Q : Multiset Mon, P.val = m ::ₘ Q := Multiset.exists_cons_of_mem hm
    induction Q using Quot.inductionOn with | _ l =>
    have heq : evalPoly i j v P = evalPolyList i j v (m :: l) := by
      unfold evalPoly; rw [hQ]; rfl
    rw [heq]
    cases l with
    | nil => simp [evalPolyList, addR_idem']
    | cons a as => simp only [evalPolyList, ← addR_assoc', addR_idem']
  · have hval : (insert m P).val = m ::ₘ P.val := Multiset.ndinsert_of_notMem hm
    have hPne : P.val ≠ 0 := by intro h0; obtain ⟨x, hx⟩ := hP; exact Multiset.notMem_zero x (h0 ▸ hx)
    unfold evalPoly; rw [hval]
    rcases P with ⟨s, hs⟩
    induction s using Quot.inductionOn with | _ l =>
    cases l with
    | nil => exact absurd rfl hPne
    | cons a as => rfl

private lemma evalPoly_union (i j : Fin 3) (v : ℕ → Elem6) {P Q : Poly}
    (hP : P.Nonempty) (hQ : Q.Nonempty) :
    evalPoly i j v (P ∪ Q) = addR i j (evalPoly i j v P) (evalPoly i j v Q) := by
  classical
  induction P using Finset.induction with
  | empty => exact absurd hP Finset.not_nonempty_empty
  | @insert m P hm ih =>
    by_cases hPe : P.Nonempty
    · rw [Finset.insert_union, evalPoly_insert i j v (Finset.Nonempty.mono Finset.subset_union_right hQ),
          evalPoly_insert i j v hPe, ih hPe, addR_assoc']
    · rw [Finset.not_nonempty_iff_eq_empty.mp hPe, show insert m ∅ = ({m} : Poly) from rfl,
          Finset.singleton_union, evalPoly_insert i j v hQ, evalPoly_singleton]

private lemma evalPoly_mulPoly (i j : Fin 3) (v : ℕ → Elem6) {P Q : Poly}
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hcP : ∀ m ∈ P, 1 ≤ m.card) (hcQ : ∀ m ∈ Q, 1 ≤ m.card) :
    evalPoly i j v (mulPoly P Q) = mulM (evalPoly i j v P) (evalPoly i j v Q) := by
  classical
  induction P using Finset.induction with
  | empty => exact absurd hP Finset.not_nonempty_empty
  | @insert m₁ P hm₁ ih =>
    have h1 : 1 ≤ m₁.card := hcP m₁ (Finset.mem_insert_self _ _)
    have hsingle : evalPoly i j v (mulPoly {m₁} Q) = mulM (evalMon v m₁) (evalPoly i j v Q) := by
      clear ih hm₁ hP hcP P
      induction Q using Finset.induction with
      | empty => exact absurd hQ Finset.not_nonempty_empty
      | @insert m₂ Q hm₂ ihQ =>
        have h2 : 1 ≤ m₂.card := hcQ m₂ (Finset.mem_insert_self _ _)
        by_cases hQe : Q.Nonempty
        · have hmul_ins : mulPoly {m₁} (insert m₂ Q) = insert (m₁ + m₂) (mulPoly {m₁} Q) := by
            ext m; simp [mulPoly]
          rw [hmul_ins, evalPoly_insert i j v (mulPoly_nonempty (Finset.singleton_nonempty _) hQe),
              evalPoly_insert i j v hQe, ihQ hQe (fun m hm => hcQ m (Finset.mem_insert_of_mem hm)),
              evalMon_add v h1 h2, addR_ldistrib]
        · rw [Finset.not_nonempty_iff_eq_empty.mp hQe, show insert m₂ ∅ = ({m₂} : Poly) from rfl]
          have hmul_s : mulPoly {m₁} {m₂} = {m₁ + m₂} := by ext m; simp [mulPoly]
          rw [hmul_s, evalPoly_singleton, evalPoly_singleton, evalMon_add v h1 h2]
    by_cases hPe : P.Nonempty
    · have hmul_u : mulPoly (insert m₁ P) Q = mulPoly {m₁} Q ∪ mulPoly P Q := by
        rw [Finset.insert_eq, mulPoly_union_left]
      rw [hmul_u,
          evalPoly_union i j v (mulPoly_nonempty (Finset.singleton_nonempty _) hQ) (mulPoly_nonempty hPe hQ),
          evalPoly_insert i j v hPe, hsingle,
          ih hPe (fun m hm => hcP m (Finset.mem_insert_of_mem hm)), addR_rdistrib]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hPe, show insert m₁ ∅ = ({m₁} : Poly) from rfl,
          evalPoly_singleton, hsingle]

private lemma eval_eq_evalPoly (i j : Fin 3) (v : ℕ → Elem6) (s : SemiringTerm) :
    s.eval i j v = evalPoly i j v (toPoly s) := by
  induction s with
  | var n => rfl
  | add s t ihs iht =>
    simp only [SemiringTerm.eval, toPoly, ihs, iht]
    rw [evalPoly_union i j v (toPoly_nonempty s) (toPoly_nonempty t)]
  | mul s t ihs iht =>
    simp only [SemiringTerm.eval, toPoly, ihs, iht]
    rw [evalPoly_mulPoly i j v (toPoly_nonempty s) (toPoly_nonempty t)
      (fun m hm => toPoly_card_pos s hm) (fun m hm => toPoly_card_pos t hm)]

private lemma leR_of_mem_evalPoly (i j : Fin 3) (v : ℕ → Elem6) {P : Poly} {m : Mon} (hm : m ∈ P) :
    addR i j (evalMon v m) (evalPoly i j v P) = evalPoly i j v P := by
  have h1 := evalPoly_insert i j v (⟨m, hm⟩ : P.Nonempty) (m := m)
  rw [Finset.insert_eq_of_mem hm] at h1
  exact h1.symm

private lemma evalPoly_eq_zero_of_mem_zero (i j : Fin 3) (v : ℕ → Elem6) {P : Poly} {m : Mon}
    (hm : m ∈ P) (h0 : evalMon v m = .zero) : evalPoly i j v P = .zero := by
  have h1 := leR_of_mem_evalPoly i j v hm
  rw [h0, addR_zero_left] at h1
  exact h1.symm

private lemma evalPoly_eq_of_subset_eval (i j : Fin 3) (v : ℕ → Elem6) {P : Poly} (hP : P.Nonempty)
    {e : Elem6} (hle : ∀ m ∈ P, addR i j (evalMon v m) e = e)
    (heq : ∃ m ∈ P, evalMon v m = e) : evalPoly i j v P = e := by
  classical
  have h1 : addR i j (evalPoly i j v P) e = e := by
    clear heq
    induction P using Finset.induction with
    | empty => exact absurd hP Finset.not_nonempty_empty
    | @insert m P hm ih =>
      by_cases hPe : P.Nonempty
      · rw [evalPoly_insert i j v hPe, addR_assoc',
            ih hPe (fun m' hm' => hle m' (Finset.mem_insert_of_mem hm')),
            hle m (Finset.mem_insert_self _ _)]
      · rw [Finset.not_nonempty_iff_eq_empty.mp hPe, show insert m ∅ = ({m} : Poly) from rfl, evalPoly_singleton]
        exact hle m (Finset.mem_insert_self m P)
  obtain ⟨m, hm, hme⟩ := heq
  have h2 : addR i j e (evalPoly i j v P) = evalPoly i j v P := hme ▸ leR_of_mem_evalPoly i j v hm
  rw [addR_comm'] at h2
  exact h2.symm.trans h1

/-! ### Section 3: Commutative ai-Semiring Equational Normalization -/

private def termOfList : List ℕ → SemiringTerm
  | [] => .var 0
  | [x] => .var x
  | x :: xs => .mul (.var x) (termOfList xs)

private def termOfMon (m : Mon) : SemiringTerm :=
  termOfList (m.sort (· ≤ ·))

private lemma toPoly_termOfList {l : List ℕ} (hl : l ≠ []) :
    (toPoly (termOfList l)) = {↑l} := by
  induction l with
  | nil => exact absurd rfl hl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      simp only [termOfList, toPoly, ih (by simp)]
      ext m; simp [mulPoly]

private lemma toPoly_termOfMon {m : Mon} (hm : 1 ≤ m.card) :
    (toPoly (termOfMon m)) = {m} := by
  have hne : m.sort (· ≤ ·) ≠ [] := by
    intro h0
    have := Multiset.length_sort (s := m) (r := (· ≤ ·))
    rw [h0] at this; simp at this; omega
  rw [termOfMon, toPoly_termOfList hne, Multiset.sort_eq]

private lemma eqDerives_termOfList_perm (Ax : Set (SemiringTerm × SemiringTerm))
    {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) :
    EqDerives Ax (termOfList l₁) (termOfList l₂) := by
  induction h with
  | nil => exact EqDerives.refl _
  | @cons x l₁ l₂ h ih =>
    cases l₁ with
    | nil => rw [h.nil_eq]; exact EqDerives.refl _
    | cons y ys =>
      cases l₂ with
      | nil => cases h.symm.nil_eq
      | cons z zs => exact EqDerives.mul_cong (EqDerives.refl _) ih
  | @swap x y l =>
    cases l with
    | nil => exact EqDerives.mul_comm _ _
    | cons z zs =>
      simp only [termOfList]
      exact EqDerives.trans (EqDerives.symm (EqDerives.mul_assoc _ _ _))
        (EqDerives.trans (EqDerives.mul_cong (EqDerives.mul_comm _ _) (EqDerives.refl _))
          (EqDerives.mul_assoc _ _ _))
  | trans _ _ ih₁ ih₂ => exact EqDerives.trans ih₁ ih₂

private lemma eqDerives_termOfList_append (Ax : Set (SemiringTerm × SemiringTerm))
    {l₁ l₂ : List ℕ} (h1 : l₁ ≠ []) (h2 : l₂ ≠ []) :
    EqDerives Ax (termOfList (l₁ ++ l₂)) (.mul (termOfList l₁) (termOfList l₂)) := by
  induction l₁ with
  | nil => exact absurd rfl h1
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases l₂ with
      | nil => exact absurd rfl h2
      | cons y ys => exact EqDerives.refl _
    | cons y ys =>
      have hstep := ih (by simp)
      simp only [List.cons_append] at hstep ⊢
      simp only [termOfList]
      exact EqDerives.trans (EqDerives.mul_cong (EqDerives.refl _) hstep)
        (EqDerives.symm (EqDerives.mul_assoc _ _ _))

private lemma eqDerives_termOfMon_mul (Ax : Set (SemiringTerm × SemiringTerm))
    {m₁ m₂ : Mon} (h1 : 1 ≤ m₁.card) (h2 : 1 ≤ m₂.card) :
    EqDerives Ax (.mul (termOfMon m₁) (termOfMon m₂)) (termOfMon (m₁ + m₂)) := by
  have hne1 : m₁.sort (· ≤ ·) ≠ [] := by
    intro h0; have := Multiset.length_sort (s := m₁) (r := (· ≤ ·)); rw [h0] at this; simp at this; omega
  have hne2 : m₂.sort (· ≤ ·) ≠ [] := by
    intro h0; have := Multiset.length_sort (s := m₂) (r := (· ≤ ·)); rw [h0] at this; simp at this; omega
  have hperm : (m₁.sort (· ≤ ·) ++ m₂.sort (· ≤ ·)).Perm ((m₁ + m₂).sort (· ≤ ·)) := by
    rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, Multiset.sort_eq, Multiset.sort_eq, Multiset.sort_eq]
  exact EqDerives.trans
    (EqDerives.symm (eqDerives_termOfList_append Ax hne1 hne2))
    (eqDerives_termOfList_perm Ax hperm)

private def sumTerms : List SemiringTerm → SemiringTerm
  | [] => .var 0
  | [t] => t
  | t :: ts => .add t (sumTerms ts)

private lemma eqDerives_sumTerms_perm (Ax : Set (SemiringTerm × SemiringTerm))
    {l₁ l₂ : List SemiringTerm} (h : l₁.Perm l₂) :
    EqDerives Ax (sumTerms l₁) (sumTerms l₂) := by
  induction h with
  | nil => exact EqDerives.refl _
  | @cons x l₁ l₂ h ih =>
    cases l₁ with
    | nil => rw [h.nil_eq]; exact EqDerives.refl _
    | cons y ys =>
      cases l₂ with
      | nil => cases h.symm.nil_eq
      | cons z zs => exact EqDerives.add_cong (EqDerives.refl _) ih
  | @swap x y l =>
    cases l with
    | nil => exact EqDerives.add_comm _ _
    | cons z zs =>
      simp only [sumTerms]
      exact EqDerives.trans (EqDerives.symm (EqDerives.add_assoc _ _ _))
        (EqDerives.trans (EqDerives.add_cong (EqDerives.add_comm _ _) (EqDerives.refl _))
          (EqDerives.add_assoc _ _ _))
  | trans _ _ ih₁ ih₂ => exact EqDerives.trans ih₁ ih₂

private lemma eqDerives_sumTerms_append (Ax : Set (SemiringTerm × SemiringTerm))
    {l₁ l₂ : List SemiringTerm} (h1 : l₁ ≠ []) (h2 : l₂ ≠ []) :
    EqDerives Ax (sumTerms (l₁ ++ l₂)) (.add (sumTerms l₁) (sumTerms l₂)) := by
  induction l₁ with
  | nil => exact absurd rfl h1
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases l₂ with
      | nil => exact absurd rfl h2
      | cons y ys => exact EqDerives.refl _
    | cons y ys =>
      have hstep := ih (by simp)
      simp only [List.cons_append] at hstep ⊢
      simp only [sumTerms]
      exact EqDerives.trans (EqDerives.add_cong (EqDerives.refl _) hstep)
        (EqDerives.symm (EqDerives.add_assoc _ _ _))

private lemma eqDerives_add_mem_sumTerms (Ax : Set (SemiringTerm × SemiringTerm))
    {t : SemiringTerm} {l : List SemiringTerm} (ht : t ∈ l) :
    EqDerives Ax (.add t (sumTerms l)) (sumTerms l) := by
  have hperm : l.Perm (t :: l.erase t) := List.perm_cons_erase ht
  generalize l.erase t = l' at hperm
  have h1 := eqDerives_sumTerms_perm Ax hperm
  cases l' with
  | nil =>
    exact EqDerives.trans (EqDerives.add_cong (EqDerives.refl t) h1)
      (EqDerives.trans (EqDerives.add_idem t) (EqDerives.symm h1))
  | cons a as =>
    refine EqDerives.trans (EqDerives.add_cong (EqDerives.refl t) h1) ?_
    refine EqDerives.trans (EqDerives.symm (EqDerives.add_assoc t t (sumTerms (a :: as)))) ?_
    refine EqDerives.trans (EqDerives.add_cong (EqDerives.add_idem t) (EqDerives.refl _)) ?_
    exact EqDerives.symm h1

private lemma eqDerives_sumTerms_dedup (Ax : Set (SemiringTerm × SemiringTerm))
    {l₁ l₂ : List SemiringTerm} (h1 : l₁ ≠ []) (h2 : l₂ ≠ [])
    (hsub1 : ∀ x ∈ l₁, x ∈ l₂) (hsub2 : ∀ x ∈ l₂, x ∈ l₁) :
    EqDerives Ax (sumTerms l₁) (sumTerms l₂) := by
  have habs : ∀ {a b : List SemiringTerm}, a ≠ [] → b ≠ [] → (∀ x ∈ a, x ∈ b) →
      EqDerives Ax (.add (sumTerms a) (sumTerms b)) (sumTerms b) := by
    intro a b ha hb hsub
    induction a with
    | nil => exact absurd rfl ha
    | cons x xs ih =>
      cases xs with
      | nil => exact eqDerives_add_mem_sumTerms Ax (hsub x (List.mem_cons_self ..))
      | cons y ys =>
        simp only [sumTerms]
        exact EqDerives.trans (EqDerives.add_assoc _ _ _)
          (EqDerives.trans
            (EqDerives.add_cong (EqDerives.refl x) (ih (by simp) (fun z hz => hsub z (List.mem_cons_of_mem _ hz))))
            (eqDerives_add_mem_sumTerms Ax (hsub x (List.mem_cons_self ..))))
  have hab := habs h1 h2 hsub1
  have hba := habs h2 h1 hsub2
  exact EqDerives.trans (EqDerives.symm hba) (EqDerives.trans (EqDerives.add_comm _ _) hab)

private lemma eqDerives_mul_sumTerms_left (Ax : Set (SemiringTerm × SemiringTerm))
    (t : SemiringTerm) {l : List SemiringTerm} (hl : l ≠ []) :
    EqDerives Ax (.mul t (sumTerms l)) (sumTerms (l.map (.mul t))) := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a as ih =>
    cases as with
    | nil => exact EqDerives.refl _
    | cons b bs =>
      simp only [sumTerms, List.map_cons]
      exact EqDerives.trans (EqDerives.left_distrib t a (sumTerms (b :: bs)))
        (EqDerives.add_cong (EqDerives.refl _) (ih (by simp)))

private lemma eqDerives_mul_sumTerms_right (Ax : Set (SemiringTerm × SemiringTerm))
    {l : List SemiringTerm} (hl : l ≠ []) (t : SemiringTerm) :
    EqDerives Ax (.mul (sumTerms l) t) (sumTerms (l.map (fun a => .mul a t))) := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a as ih =>
    cases as with
    | nil => exact EqDerives.refl _
    | cons b bs =>
      simp only [sumTerms, List.map_cons]
      exact EqDerives.trans (EqDerives.right_distrib a (sumTerms (b :: bs)) t)
        (EqDerives.add_cong (EqDerives.refl _) (ih (by simp)))

/-- Every term `s` is derivably equal (in pure commutative ai-semiring theory) to `sumTerms`
of `termOfMon` over any list `l` whose elements are precisely `(toPoly s)`. -/
private lemma eqDerives_of_list_eq_toPoly (Ax : Set (SemiringTerm × SemiringTerm))
    (s : SemiringTerm) :
    ∃ l : List Mon, l ≠ [] ∧ (∀ m, m ∈ l ↔ m ∈ (toPoly s)) ∧
      EqDerives Ax s (sumTerms (l.map termOfMon)) := by
  induction s with
  | var n =>
    have htm : termOfMon ({n} : Mon) = .var n := by
      have hsort : ({n} : Mon).sort (· ≤ ·) = [n] := by
        have h1 : (({n} : Mon).sort (· ≤ ·) : Multiset ℕ) = {n} := Multiset.sort_eq (s := ({n} : Mon)) (r := (· ≤ ·))
        cases h : ({n} : Mon).sort (· ≤ ·) with
        | nil => rw [h] at h1; simp at h1
        | cons a as =>
          cases as with
          | nil => rw [h] at h1; simpa using h1
          | cons b bs => rw [h] at h1; have := congrArg Multiset.card h1; simp at this
      rw [termOfMon, hsort]; rfl
    exact ⟨[{n}], by simp, fun m => by simp [toPoly], by simp only [List.map_cons, List.map_nil, sumTerms, htm]; exact EqDerives.refl _⟩
  | add s t ihs iht =>
    obtain ⟨ls, hls, hms, hds⟩ := ihs
    obtain ⟨lt, hlt, hmt, hdt⟩ := iht
    refine ⟨ls ++ lt, by simp [hls], fun m => by simp [toPoly, hms, hmt], ?_⟩
    rw [List.map_append]
    exact EqDerives.trans (EqDerives.add_cong hds hdt)
      (EqDerives.symm (eqDerives_sumTerms_append Ax (by simp [hls]) (by simp [hlt])))
  | mul s t ihs iht =>
    obtain ⟨ls, hls, hms, hds⟩ := ihs
    obtain ⟨lt, hlt, hmt, hdt⟩ := iht
    let pairs : List Mon := ls.flatMap fun m₁ => lt.map fun m₂ => m₁ + m₂
    have hpne : pairs ≠ [] := by
      cases ls with
      | nil => exact absurd rfl hls
      | cons a as =>
        cases lt with
        | nil => exact absurd rfl hlt
        | cons b bs => simp [pairs]
    have hpmem : ∀ m, m ∈ pairs ↔ m ∈ (toPoly (SemiringTerm.mul s t)) := by
      intro m
      simp only [pairs, List.mem_flatMap, List.mem_map, toPoly, mem_mulPoly, hms, hmt]
    refine ⟨pairs, hpne, hpmem, ?_⟩
    -- Distribute `sumTerms (ls.map termOfMon) * sumTerms (lt.map termOfMon)`!
    have hstep1 : EqDerives Ax (.mul s t)
        (.mul (sumTerms (ls.map termOfMon)) (sumTerms (lt.map termOfMon))) :=
      EqDerives.mul_cong hds hdt
    have hsingle_gen : ∀ (m₁ : Mon), 1 ≤ m₁.card → ∀ (lb : List Mon), lb ≠ [] → (∀ m₂ ∈ lb, 1 ≤ m₂.card) →
        EqDerives Ax (.mul (termOfMon m₁) (sumTerms (lb.map termOfMon)))
          (sumTerms ((lb.map fun m₂ => m₁ + m₂).map termOfMon)) := by
      intro m₁ h1 lb hlb hcb
      have hmulL := eqDerives_mul_sumTerms_left Ax (termOfMon m₁) (l := lb.map termOfMon) (by simp [hlb])
      refine EqDerives.trans hmulL ?_
      clear hmulL
      rw [List.map_map, List.map_map]
      induction lb with
      | nil => exact absurd rfl hlb
      | cons m₂ ms₂ ih₂ =>
        cases ms₂ with
        | nil =>
          exact eqDerives_termOfMon_mul Ax h1 (hcb m₂ (List.mem_cons_self ..))
        | cons m₃ ms₃ =>
          simp only [List.map_cons, Function.comp_apply, sumTerms]
          exact EqDerives.add_cong
            (eqDerives_termOfMon_mul Ax h1 (hcb m₂ (List.mem_cons_self ..)))
            (ih₂ (by simp) (fun m hm => hcb m (List.mem_cons_of_mem _ hm)))
    have hlt_card : ∀ m₂ ∈ lt, 1 ≤ m₂.card := fun m₂ hm₂ => toPoly_card_pos t ((hmt m₂).mp hm₂)
    have hstep2 : ∀ (la : List Mon), la ≠ [] → (∀ m ∈ la, 1 ≤ m.card) →
        EqDerives Ax (.mul (sumTerms (la.map termOfMon)) (sumTerms (lt.map termOfMon)))
          (sumTerms ((la.flatMap fun m₁ => lt.map fun m₂ => m₁ + m₂).map termOfMon)) := by
      intro la hla hca
      induction la with
      | nil => exact absurd rfl hla
      | cons m₁ ms ih =>
        have h1 : 1 ≤ m₁.card := hca m₁ (List.mem_cons_self ..)
        have hsingle := hsingle_gen m₁ h1 lt hlt hlt_card
        cases ms with
        | nil =>
          simp only [List.map_cons, List.map_nil, sumTerms, List.flatMap_cons, List.flatMap_nil, List.append_nil]
          exact hsingle
        | cons m₂ ms' =>
          change EqDerives Ax
            (.mul (.add (termOfMon m₁) (sumTerms (List.map termOfMon (m₂ :: ms')))) (sumTerms (List.map termOfMon lt)))
            (sumTerms (List.map termOfMon (List.map (fun m₂ => m₁ + m₂) lt ++
              List.flatMap (fun m₁ => List.map (fun m₂ => m₁ + m₂) lt) (m₂ :: ms'))))
          rw [List.map_append]
          refine EqDerives.trans (EqDerives.right_distrib _ _ _) ?_
          refine EqDerives.trans
            (EqDerives.add_cong hsingle (ih (by simp) (fun m hm => hca m (List.mem_cons_of_mem _ hm)))) ?_
          have hneL : (List.map termOfMon (List.map (fun m₂ => m₁ + m₂) lt)) ≠ [] := by simp [hlt]
          have hneR : (List.map termOfMon (List.flatMap (fun a => List.map (fun b => a + b) lt) (m₂ :: ms'))) ≠ [] := by
            cases lt with
            | nil => exact absurd rfl hlt
            | cons _ _ => simp
          exact EqDerives.symm (eqDerives_sumTerms_append Ax hneL hneR)
    exact EqDerives.trans hstep1 (hstep2 ls hls (fun m hm => toPoly_card_pos s ((hms m).mp hm)))

private lemma eqDerives_of_toPoly_eq (Ax : Set (SemiringTerm × SemiringTerm))
    {s t : SemiringTerm} (h : (toPoly s) = (toPoly t)) : EqDerives Ax s t := by
  obtain ⟨ls, hls, hms, hds⟩ := eqDerives_of_list_eq_toPoly Ax s
  obtain ⟨lt, hlt, hmt, hdt⟩ := eqDerives_of_list_eq_toPoly Ax t
  refine EqDerives.trans hds (EqDerives.trans ?_ (EqDerives.symm hdt))
  refine eqDerives_sumTerms_dedup Ax (by simp [hls]) (by simp [hlt]) ?_ ?_
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    exact List.mem_map.mpr ⟨m, (hmt m).mpr (h ▸ (hms m).mp hm), rfl⟩
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    exact List.mem_map.mpr ⟨m, (hms m).mpr (h.symm ▸ (hmt m).mp hm), rfl⟩

/-- Absorption helper: if `(toPoly s) ⊆ (toPoly t)`, then `s + t ≈ t` is derivable in pure ai-semiring theory. -/
private lemma eqDerives_abs_of_subset (Ax : Set (SemiringTerm × SemiringTerm))
    {s t : SemiringTerm} (h : (toPoly s) ⊆ (toPoly t)) : EqDerives Ax (.add s t) t :=
  eqDerives_of_toPoly_eq Ax (by simp [toPoly, Finset.union_eq_right.mpr h])

/-- Absorption from monomials: if `m ⪯ t` for every `m ∈ (toPoly s)`, then `s ⪯ t`. -/
private lemma eqDerives_abs_of_monomials (Ax : Set (SemiringTerm × SemiringTerm))
    {s t : SemiringTerm}
    (hm : ∀ m ∈ (toPoly s), EqDerives Ax (.add (termOfMon m) t) t) :
    EqDerives Ax (.add s t) t := by
  obtain ⟨ls, hls, hms, hds⟩ := eqDerives_of_list_eq_toPoly Ax s
  refine EqDerives.trans (EqDerives.add_cong hds (EqDerives.refl t)) ?_
  have hmem : ∀ m ∈ ls, EqDerives Ax (.add (termOfMon m) t) t := fun m h => hm m ((hms m).mp h)
  clear hms hds
  induction ls with
  | nil => exact absurd rfl hls
  | cons m ms ih =>
    cases ms with
    | nil => exact hmem m (List.mem_cons_self ..)
    | cons m' ms' =>
      simp only [List.map_cons, sumTerms]
      exact EqDerives.trans (EqDerives.add_assoc _ _ _)
        (EqDerives.trans
          (EqDerives.add_cong (EqDerives.refl _) (ih (by simp) (fun x hx => hmem x (List.mem_cons_of_mem _ hx))))
          (hmem m (List.mem_cons_self ..)))

/-- Antisymmetry of absorption: `s ⪯ t` and `t ⪯ s` imply `s ≈ t`. -/
private lemma eqDerives_of_abs_both (Ax : Set (SemiringTerm × SemiringTerm))
    {s t : SemiringTerm} (h1 : EqDerives Ax (.add s t) t) (h2 : EqDerives Ax (.add t s) s) :
    EqDerives Ax s t :=
  EqDerives.trans (EqDerives.symm h2) (EqDerives.trans (EqDerives.add_comm t s) h1)

/-- Monotonicity of absorption: if `m ⪯ u` and `(toPoly u) ⊆ (toPoly v)`, then `m ⪯ v`. -/
private lemma eqDerives_abs_context (Ax : Set (SemiringTerm × SemiringTerm))
    {a u v : SemiringTerm} (ha : EqDerives Ax (.add a u) u) (huv : (toPoly u) ⊆ (toPoly v)) :
    EqDerives Ax (.add a v) v := by
  have huv_eq : EqDerives Ax (.add u v) v := eqDerives_abs_of_subset Ax huv
  exact EqDerives.trans (EqDerives.add_cong (EqDerives.refl a) (EqDerives.symm huv_eq))
    (EqDerives.trans (EqDerives.symm (EqDerives.add_assoc a u v))
      (EqDerives.trans (EqDerives.add_cong ha (EqDerives.refl v)) huv_eq))

/-- Transitivity of absorption: if `a ⪯ b + v` and `b ⪯ v`, then `a ⪯ v`. -/
private lemma eqDerives_abs_cut (Ax : Set (SemiringTerm × SemiringTerm))
    {a b v : SemiringTerm}
    (h1 : EqDerives Ax (.add a (.add b v)) (.add b v))
    (h2 : EqDerives Ax (.add b v) v) :
    EqDerives Ax (.add a v) v :=
  EqDerives.trans (EqDerives.add_cong (EqDerives.refl a) (EqDerives.symm h2))
    (EqDerives.trans h1 h2)

/-! ### Section 4: Graph Theory on Polynomials & Theorem 3.1 (Identity Criteria) -/

private def quadAdj (P : Poly) (x y : ℕ) : Prop := x ≠ y ∧ ({x, y} : Mon) ∈ P
private def quadVert (P : Poly) (x : ℕ) : Prop := ∃ y, quadAdj P x y
private def marked (P : Poly) (x : ℕ) : Prop := ({x} : Mon) ∈ P ∧ quadVert P x

private lemma quadAdj_symm {P : Poly} {x y : ℕ} (h : quadAdj P x y) : quadAdj P y x :=
  ⟨h.1.symm, by rw [Multiset.pair_comm]; exact h.2⟩

private inductive Walk (P : Poly) : ℕ → ℕ → ℕ → Prop where
  | zero (x : ℕ) : Walk P x x 0
  | step {x y z k : ℕ} : quadAdj P x y → Walk P y z k → Walk P x z (k + 1)

private lemma walk_trans {P : Poly} {x y z k₁ k₂ : ℕ}
    (h1 : Walk P x y k₁) (h2 : Walk P y z k₂) : Walk P x z (k₁ + k₂) := by
  induction h1 with
  | zero _ => simpa using h2
  | @step a b c k hab _ ih =>
    rw [show k + 1 + k₂ = k + k₂ + 1 by omega]
    exact Walk.step hab (ih h2)

private lemma walk_symm {P : Poly} {x y k : ℕ} (h : Walk P x y k) : Walk P y x k := by
  induction h with
  | zero _ => exact Walk.zero _
  | @step a b c k hab _ ih =>
    exact walk_trans ih (Walk.step (quadAdj_symm hab) (Walk.zero a))

private def HasOddCycle (P : Poly) : Prop := ∃ x k : ℕ, Walk P x x (2 * k + 1)

private def IsBasicZero (P : Poly) : Prop :=
  (∃ m ∈ P, 3 ≤ m.card) ∨ (∃ x : ℕ, ({x, x} : Mon) ∈ P) ∨ HasOddCycle P

/-- In a graph without odd cycles, any two walks between the same endpoints have the same parity. -/
private lemma walk_parity_unique {P : Poly} (hbip : ¬ HasOddCycle P) {x y k₁ k₂ : ℕ}
    (h1 : Walk P x y k₁) (h2 : Walk P x y k₂) : k₁ % 2 = k₂ % 2 := by
  by_contra hne
  have hloop : Walk P x x (k₁ + k₂) := walk_trans h1 (walk_symm h2)
  have hodd : (k₁ + k₂) % 2 = 1 := by omega
  exact hbip ⟨x, (k₁ + k₂) / 2, by rwa [show 2 * ((k₁ + k₂) / 2) + 1 = k₁ + k₂ by omega]⟩

/-- Any odd cycle evaluates to `.zero` under every valuation in `R_{ij}`! -/
private lemma evalPoly_eq_zero_of_oddCycle (i j : Fin 3) (v : ℕ → Elem6) {P : Poly}
    (h : HasOddCycle P) : evalPoly i j v P = .zero := by
  obtain ⟨x, k, hw⟩ := h
  -- On `P₄ = p - b - a - q`, adjacent vertices alternate between `{a, p}` and `{b, q}`!
  have hside : ∀ {u w n : ℕ}, Walk P u w n →
      (∀ a b, quadAdj P a b → mulM (v a) (v b) = .c) →
      ((v u = .a ∨ v u = .p) ↔ ((n % 2 = 0 ∧ (v w = .a ∨ v w = .p)) ∨ (n % 2 = 1 ∧ (v w = .b ∨ v w = .q)))) := by
    intro u w n hwalk hall
    induction hwalk with
    | zero u =>
      simp only [Nat.zero_mod, true_and, Nat.zero_ne_one, false_and, or_false]
    | @step a b c m hab hbc ih =>
      have hc := hall a b hab
      have hstep : ((v a = .a ∨ v a = .p) ∧ (v b = .b ∨ v b = .q)) ∨
          ((v a = .b ∨ v a = .q) ∧ (v b = .a ∨ v b = .p)) := by
        cases h1 : v a <;> cases h2 : v b <;> rw [h1, h2] at hc <;> simp [mulM] at hc ⊢
      rcases hstep with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have hnot : ¬ (v b = .a ∨ v b = .p) := by rcases hb with h | h <;> simp [h]
        have h' := ih.not.mp hnot
        have hm2 : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one m
        have hcb : (m % 2 = 0 → ¬ (v c = .a ∨ v c = .p)) ∧ (m % 2 = 1 → ¬ (v c = .b ∨ v c = .q)) := by
          constructor <;> intro hm <;> intro hc' <;> exact h' (by simp [hm, hc'])
        have hcv : (v c = .a ∨ v c = .p) ∨ (v c = .b ∨ v c = .q) := by
          cases hbc with
          | zero _ => right; exact hb
          | @step _ d _ _ hbd _ =>
            have h' := hall _ _ hbd
            -- Wait: `c` is the END of the walk, so check `walk_symm hbc`!
            have hrev := walk_symm (Walk.step hbd (by assumption))
            cases hrev with
            | @step _ e _ _ hce _ =>
              have hce' := hall _ _ hce
              cases h1 : v c <;> cases h2 : v e <;> rw [h1, h2] at hce' <;> simp [mulM] at hce' ⊢
        simp only [ha, true_iff]
        rcases hm2 with hm0 | hm1
        · right; refine ⟨by omega, ?_⟩
          rcases hcv with h | h; exact absurd h (hcb.1 hm0); exact h
        · left; refine ⟨by omega, ?_⟩
          rcases hcv with h | h; exact h; exact absurd h (hcb.2 hm1)
      · have hnot : ¬ (v a = .a ∨ v a = .p) := by rcases ha with h | h <;> simp [h]
        have h' := ih.mp hb
        simp only [hnot, false_iff]
        rcases h' with ⟨hm0, hc'⟩ | ⟨hm1, hc'⟩
        · rintro (⟨h1, _⟩ | ⟨_, hc2⟩); omega
          rcases hc' with h | h <;> rcases hc2 with h2 | h2 <;> rw [h] at h2 <;> cases h2
        · rintro (⟨_, hc2⟩ | ⟨h1, _⟩)
          rcases hc' with h | h <;> rcases hc2 with h2 | h2 <;> rw [h] at h2 <;> cases h2
          omega
  by_contra hne
  have hall : ∀ a b, quadAdj P a b → mulM (v a) (v b) = .c := by
    intro a b hab
    rcases mulM_zero_or_c (v a) (v b) with h0 | hc
    · exact absurd (evalPoly_eq_zero_of_mem_zero i j v hab.2 (by rw [evalMon_pair, h0])) hne
    · exact hc
  have hs := hside hw hall
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  rw [hmod] at hs
  simp only [Nat.one_ne_zero, false_and, true_and, false_or] at hs
  have hvx : (v x = .a ∨ v x = .p) ∨ (v x = .b ∨ v x = .q) := by
    cases hw with
    | @step _ y _ _ hxy _ =>
      have h' := hall x y hxy
      cases h1 : v x <;> cases h2 : v y <;> rw [h1, h2] at h' <;> simp [mulM] at h' ⊢
  rcases hvx with h1 | h2
  · have := hs.mp h1
    rcases h1 with h | h <;> rcases this with h' | h' <;> rw [h] at h' <;> cases h'
  · have := hs.mpr h2
    rcases h2 with h | h <;> rcases this with h' | h' <;> rw [h] at h' <;> cases h'

private lemma evalPoly_eq_zero_of_basicZero (i j : Fin 3) (v : ℕ → Elem6) {P : Poly}
    (h : IsBasicZero P) : evalPoly i j v P = .zero := by
  rcases h with ⟨m, hm, h3⟩ | ⟨x, hx⟩ | hodd
  · exact evalPoly_eq_zero_of_mem_zero i j v hm (evalMon_card_ge_three v h3)
  · exact evalPoly_eq_zero_of_mem_zero i j v hx (by rw [evalMon_pair, mulM_diag])
  · exact evalPoly_eq_zero_of_oddCycle i j v hodd

/-- Soundness of `Σ₀`: every identity in `Σ₀` holds in every `R_{ij}`. -/
private lemma sigma0_sound (i j : Fin 3) : ∀ p ∈ Sigma0, SatisfiesId i j p.1 p.2 := by
  intro p hp v
  rcases hp with (rfl | rfl) | ⟨n, hn, rfl⟩
  · simp [absId, SemiringTerm.eval, mulM_diag, addR_zero_right]
  · simp only [SemiringTerm.eval, mulM_diag]
    rcases mulM_zero_or_c (v 1) (v 2) with h | h <;> rw [h] <;> cases v 3 <;> rfl
  · simp only [absId, SemiringTerm.eval]
    rw [eval_eq_evalPoly]
    have hodd : HasOddCycle (toPoly (oddCycleTerm n)) := by
      have hpath : ∀ k : ℕ, ∀ m ≤ k, ({m, m + 1} : Mon) ∈ (toPoly (pathTerm k)) := by
        intro k; induction k with
        | zero =>
          intro m hm; have hm0 : m = 0 := by omega
          rw [hm0]
          exact mem_mulPoly.mpr ⟨{0}, Finset.mem_singleton_self _, {1}, Finset.mem_singleton_self _, Multiset.singleton_add 0 {1}⟩
        | succ k ih =>
          intro m hm
          simp only [pathTerm, toPoly, Finset.mem_union]
          by_cases hmk : m ≤ k
          · left; exact ih m hmk
          · right
            have hmeq : m = k + 1 := by omega
            rw [hmeq]
            exact mem_mulPoly.mpr ⟨{k + 1}, Finset.mem_singleton_self _, {k + 2}, Finset.mem_singleton_self _, Multiset.singleton_add (k + 1) {k + 2}⟩
      have hedge : ∀ m < 2 * n, quadAdj (toPoly (oddCycleTerm n)) m (m + 1) := by
        intro m hm
        refine ⟨by omega, ?_⟩
        simp only [oddCycleTerm, toPoly, Finset.mem_union]
        left; exact hpath (2 * n - 1) m (by omega)
      have hwalk : ∀ r ≤ 2 * n, Walk (toPoly (oddCycleTerm n)) 0 r r := by
        intro r; induction r with
        | zero => intro _; exact Walk.zero 0
        | succ r ih =>
          intro hr
          exact walk_trans (ih (by omega)) (Walk.step (hedge r (by omega)) (Walk.zero _))
      have hlast : quadAdj (toPoly (oddCycleTerm n)) (2 * n) 0 := by
        refine ⟨by omega, ?_⟩
        simp only [oddCycleTerm, toPoly, Finset.mem_union]
        right; simp [mulPoly]
      exact ⟨0, n, walk_trans (hwalk (2 * n) le_rfl) (Walk.step hlast (Walk.zero 0))⟩
    rw [evalPoly_eq_zero_of_oddCycle i j v hodd, addR_zero_right]

/-- Soundness of `idXi`, `idAlpha`, `idBeta`, `idEta`, `idTheta`. -/
private lemma basis01_sound : ∀ p ∈ basis01, SatisfiesId 0 1 p.1 p.2 := by
  rintro p (hp | rfl | rfl | rfl)
  · exact sigma0_sound 0 1 p hp
  · intro v; simp [idXi, SemiringTerm.eval, mulM_diag]
    cases v 0 <;> cases v 1 <;> rfl
  · intro v; simp [idAlpha, absId, pathTerm, SemiringTerm.eval]
    cases v 0 <;> cases v 1 <;> cases v 2 <;> cases v 3 <;> rfl
  · intro v; simp [idBeta, absId, SemiringTerm.eval]
    cases v 0 <;> cases v 1 <;> cases v 2 <;> cases v 3 <;> rfl

private lemma basis02_sound : ∀ p ∈ basis02, SatisfiesId 0 2 p.1 p.2 := by
  rintro p (hp | rfl | rfl)
  · exact sigma0_sound 0 2 p hp
  · intro v; simp [idXi, SemiringTerm.eval, mulM_diag]
    cases v 0 <;> cases v 1 <;> rfl
  · intro v; simp [idEta, absId, pathTerm, SemiringTerm.eval]
    cases v 0 <;> cases v 1 <;> cases v 2 <;> rfl

private lemma basis11_sound : ∀ p ∈ basis11, SatisfiesId 1 1 p.1 p.2 := by
  rintro p (hp | rfl)
  · exact sigma0_sound 1 1 p hp
  · intro v; simp [idAlpha, absId, pathTerm, SemiringTerm.eval]
    cases v 0 <;> cases v 1 <;> cases v 2 <;> cases v 3 <;> rfl

private lemma basis12_sound : ∀ p ∈ basis12, SatisfiesId 1 2 p.1 p.2 := by
  rintro p (hp | ⟨n, hn, rfl⟩)
  · exact sigma0_sound 1 2 p hp
  · intro v
    simp only [idTheta, absId]
    change addR 1 2 (mulM (v 0) (v (2 * n + 1)))
        ((SemiringTerm.add (.add (.var 0) (.var (2 * n + 1))) (pathTerm (2 * n))).eval 1 2 v) =
      (SemiringTerm.add (.add (.var 0) (.var (2 * n + 1))) (pathTerm (2 * n))).eval 1 2 v
    rw [eval_eq_evalPoly]
    set P := (toPoly (SemiringTerm.add (.add (.var 0) (.var (2 * n + 1))) (pathTerm (2 * n))))
    by_cases h0 : evalPoly 1 2 v P = .zero
    · rw [h0, addR_zero_right]
    · have hpath : ∀ k : ℕ, ∀ m ≤ k, ({m, m + 1} : Mon) ∈ (toPoly (pathTerm k)) := by
        intro k; induction k with
        | zero =>
          intro m hm; have hm0 : m = 0 := by omega
          rw [hm0]
          exact mem_mulPoly.mpr ⟨{0}, Finset.mem_singleton_self _, {1}, Finset.mem_singleton_self _, Multiset.singleton_add 0 {1}⟩
        | succ k ih =>
          intro m hm
          simp only [pathTerm, toPoly, Finset.mem_union]
          by_cases hmk : m ≤ k
          · left; exact ih m hmk
          · right
            have hmeq : m = k + 1 := by omega
            rw [hmeq]
            exact mem_mulPoly.mpr ⟨{k + 1}, Finset.mem_singleton_self _, {k + 2}, Finset.mem_singleton_self _, Multiset.singleton_add (k + 1) {k + 2}⟩
      have hedge_c : ∀ m ≤ 2 * n, mulM (v m) (v (m + 1)) = .c := by
        intro m hm
        have hmem : ({m, m + 1} : Mon) ∈ P := by
          simp only [P, toPoly, Finset.mem_union]
          right; exact hpath (2 * n) m hm
        rcases mulM_zero_or_c (v m) (v (m + 1)) with hz | hc
        · exact absurd (evalPoly_eq_zero_of_mem_zero 1 2 v hmem (by rw [evalMon_pair, hz])) h0
        · exact hc
      have hPc : evalPoly 1 2 v P = .c := by
        have hmem01 : ({0, 1} : Mon) ∈ P := by
          simp only [P, toPoly, Finset.mem_union]; right; exact hpath (2 * n) 0 (by omega)
        have hle := leR_of_mem_evalPoly 1 2 v hmem01
        rw [evalMon_pair, hedge_c 0 (by omega)] at hle
        cases hval : evalPoly 1 2 v P <;> rw [hval] at hle h0 <;> simp [addR, belowC] at hle h0
      have hv_below : ∀ x : ℕ, ({x} : Mon) ∈ P → v x = .a ∨ v x = .b ∨ v x = .q ∨ v x = .c := by
        intro x hx
        have hle := leR_of_mem_evalPoly 1 2 v hx
        rw [evalMon_singleton, hPc] at hle
        cases hv : v x <;> rw [hv] at hle <;> simp [addR, belowC] at hle ⊢
      have hv0_mem : ({0} : Mon) ∈ P := by simp [P, toPoly]
      have hvL_mem : ({2 * n + 1} : Mon) ∈ P := by simp [P, toPoly]
      have h0_abq : v 0 = .a ∨ v 0 = .b ∨ v 0 = .q := by
        rcases hv_below 0 hv0_mem with h | h | h | h
        · left; exact h
        · right; left; exact h
        · right; right; exact h
        · have hc0 := hedge_c 0 (by omega); rw [h] at hc0; cases hv1 : v 1 <;> rw [hv1] at hc0 <;> cases hc0
      have hL_abq : v (2 * n + 1) = .a ∨ v (2 * n + 1) = .b ∨ v (2 * n + 1) = .q := by
        rcases hv_below (2 * n + 1) hvL_mem with h | h | h | h
        · left; exact h
        · right; left; exact h
        · right; right; exact h
        · have hcL := hedge_c (2 * n) le_rfl; rw [h] at hcL; cases hv2 : v (2 * n) <;> rw [hv2] at hcL <;> cases hcL
      -- Parity along the path `0 - 1 - ... - (2n+1)`: `v 0` and `v (2n+1)` are in opposite sides of `P₄`!
      have hpar : ∀ r ≤ 2 * n + 1,
          (v 0 = .a ∨ v 0 = .p) ↔ ((r % 2 = 0 ∧ (v r = .a ∨ v r = .p)) ∨ (r % 2 = 1 ∧ (v r = .b ∨ v r = .q))) := by
        intro r; induction r with
        | zero => intro _; simp
        | succ r ih =>
          intro hr
          have hc := hedge_c r (by omega)
          have hstep : ((v r = .a ∨ v r = .p) ∧ (v (r + 1) = .b ∨ v (r + 1) = .q)) ∨
              ((v r = .b ∨ v r = .q) ∧ (v (r + 1) = .a ∨ v (r + 1) = .p)) := by
            cases h1 : v r <;> cases h2 : v (r + 1) <;> rw [h1, h2] at hc <;> simp [mulM] at hc ⊢
          have hih := ih (by omega)
          rcases Nat.mod_two_eq_zero_or_one r with hr0 | hr1
          · rw [hr0] at hih
            have hr1' : (r + 1) % 2 = 1 := by omega
            rw [hr1']
            simp only [true_and, Nat.zero_ne_one, false_and, or_false, Nat.one_ne_zero, false_or] at hih ⊢
            rw [hih]
            rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · simp [h1, h2]
            · have hn1 : ¬ (v r = .a ∨ v r = .p) := by rcases h1 with h | h <;> simp [h]
              have hn2 : ¬ (v (r + 1) = .b ∨ v (r + 1) = .q) := by rcases h2 with h | h <;> simp [h]
              simp [hn1, hn2]
          · rw [hr1] at hih
            have hr0' : (r + 1) % 2 = 0 := by omega
            rw [hr0']
            simp only [true_and, Nat.zero_ne_one, false_and, or_false, Nat.one_ne_zero, false_or] at hih ⊢
            rw [hih]
            rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · have hn1 : ¬ (v r = .b ∨ v r = .q) := by rcases h1 with h | h <;> simp [h]
              have hn2 : ¬ (v (r + 1) = .a ∨ v (r + 1) = .p) := by rcases h2 with h | h <;> simp [h]
              simp [hn1, hn2]
            · simp [h1, h2]
      have hpL := hpar (2 * n + 1) le_rfl
      rw [show (2 * n + 1) % 2 = 1 by omega] at hpL
      simp only [Nat.one_ne_zero, false_and, true_and, false_or] at hpL
      have hprod : mulM (v 0) (v (2 * n + 1)) = .c := by
        rcases h0_abq with h0a | h0b | h0q
        · have h1 := hpL.mp (Or.inl h0a)
          rcases h1 with h | h <;> rw [h0a, h] <;> rfl
        · have h1 : ¬ (v 0 = .a ∨ v 0 = .p) := by simp [h0b]
          have h2 : ¬ (v (2 * n + 1) = .b ∨ v (2 * n + 1) = .q) := hpL.not.mp h1
          rcases hL_abq with ha | hb | hq
          · rw [h0b, ha]; rfl
          · exact absurd (Or.inl hb) h2
          · exact absurd (Or.inr hq) h2
        · have h1 : ¬ (v 0 = .a ∨ v 0 = .p) := by simp [h0q]
          have h2 : ¬ (v (2 * n + 1) = .b ∨ v (2 * n + 1) = .q) := hpL.not.mp h1
          rcases hL_abq with ha | hb | hq
          · rw [h0q, ha]; rfl
          · exact absurd (Or.inl hb) h2
          · exact absurd (Or.inr hq) h2
      rw [hPc, hprod, addR_idem']

/-! ### Section 5: Countervaluations (Necessity of Theorem 3.1) -/

/-- Pick a canonical proper 2-coloring of any bipartite graph `G(P)` into `Bool` (`true`/`false`),
choosing the color of a specified component or every marked component! -/
private lemma exists_bipartite_coloring {P : Poly} (hbip : ¬ HasOddCycle P) :
    ∃ col : ℕ → Bool, ∀ x y, quadAdj P x y → col x ≠ col y := by
  classical
  -- For each vertex `x`, pick a canonical representative `rep x` of its connected component,
  -- and set `col x := decide (∃ k, Walk P (rep x) x (2 * k))`!
  let sameC : ℕ → ℕ → Prop := fun x y => ∃ k, Walk P x y k
  have hrefl : ∀ x, sameC x x := fun x => ⟨0, Walk.zero x⟩
  have hsymm : ∀ {x y}, sameC x y → sameC y x := fun ⟨k, h⟩ => ⟨k, walk_symm h⟩
  have htrans : ∀ {x y z}, sameC x y → sameC y z → sameC x z :=
    fun ⟨k₁, h1⟩ ⟨k₂, h2⟩ => ⟨k₁ + k₂, walk_trans h1 h2⟩
  let rep : ℕ → ℕ := fun x => Classical.choose (show ({y : ℕ | sameC x y}).Nonempty from ⟨x, hrefl x⟩)
  have hrep_same : ∀ x, sameC x (rep x) := fun x =>
    Classical.choose_spec (show ({y : ℕ | sameC x y}).Nonempty from ⟨x, hrefl x⟩)
  have hrep_eq : ∀ {x y}, sameC x y → rep x = rep y := by
    intro x y h
    have hset : ({z : ℕ | sameC x z} : Set ℕ) = {z : ℕ | sameC y z} := by
      ext z; exact ⟨fun hz => htrans (hsymm h) hz, fun hz => htrans h hz⟩
    dsimp only [rep]; congr 1
  refine ⟨fun x => decide (∃ k, Walk P (rep x) x (2 * k)), fun x y hxy => ?_⟩
  have hsc : sameC x y := ⟨1, Walk.step hxy (Walk.zero y)⟩
  have hre : rep x = rep y := hrep_eq hsc
  obtain ⟨kx, hwx⟩ := hsymm (hrep_same x)
  have hwy : Walk P (rep x) y (kx + 1) := walk_trans hwx (Walk.step hxy (Walk.zero y))
  dsimp only
  rw [← hre]
  by_cases hx : ∃ k, Walk P (rep x) x (2 * k)
  · obtain ⟨k, hk⟩ := hx
    have hny : ¬ ∃ k', Walk P (rep x) y (2 * k') := by
      rintro ⟨k', hk'⟩
      have hp1 := walk_parity_unique hbip hwx hk
      have hp2 := walk_parity_unique hbip hwy hk'
      omega
    simp [show ∃ k, Walk P (rep x) x (2 * k) from ⟨k, hk⟩, hny]
  · have hodd : kx % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one kx with h0 | h1
      · exfalso; exact hx ⟨kx / 2, by rwa [show 2 * (kx / 2) = kx by omega]⟩
      · exact h1
    have hy : ∃ k', Walk P (rep x) y (2 * k') :=
      ⟨(kx + 1) / 2, by rwa [show 2 * ((kx + 1) / 2) = kx + 1 by omega]⟩
    simp [hx, hy]

/-- Helper: given any valuation `v` on `P` (with `P` having an edge) such that every edge of `P`
maps to `.c` and every linear monomial of `P` maps to `≤_R .c`, then `evalPoly i j v P = .c`! -/
private lemma evalPoly_eq_c_of_hom' (i j : Fin 3) (v : ℕ → Elem6) {P : Poly}
    (hpos : ∀ m ∈ P, 1 ≤ m.card) (hnbz : ¬ IsBasicZero P) (hedge : ∃ a b, quadAdj P a b)
    (hlin : ∀ x, ({x} : Mon) ∈ P → addR i j (v x) .c = .c)
    (hquad : ∀ a b, quadAdj P a b → mulM (v a) (v b) = .c) :
    evalPoly i j v P = .c := by
  obtain ⟨a₀, b₀, hab₀⟩ := hedge
  refine evalPoly_eq_of_subset_eval i j v ⟨{a₀, b₀}, hab₀.2⟩ ?_
    ⟨{a₀, b₀}, hab₀.2, by rw [evalMon_pair, hquad a₀ b₀ hab₀]⟩
  intro m hm
  have h1 := hpos m hm
  have hlt3 : m.card ≤ 2 := by by_contra h; exact hnbz (Or.inl ⟨m, hm, by omega⟩)
  interval_cases hc : m.card
  · obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp hc
    rw [evalMon_singleton]; exact hlin x hm
  · obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.mp hc
    have hne : x ≠ y := fun h => by subst h; exact hnbz (Or.inr (Or.inl ⟨x, hm⟩))
    rw [evalMon_pair, hquad x y ⟨hne, hm⟩, addR_idem']

/-- Purely linear polynomials absorb ONLY their displayed linear monomials in any `R_{ij}`! -/
private lemma linear_poly_abs_only_mem (i j : Fin 3) {P : Poly} (hP : P.Nonempty)
    (hpos : ∀ m ∈ P, 1 ≤ m.card) (hnbz : ¬ IsBasicZero P)
    (hno_edge : ∀ a b, ¬ quadAdj P a b) {m : Mon} (hm_pos : 1 ≤ m.card)
    (habs : ∀ v : ℕ → Elem6, addR i j (evalMon v m) (evalPoly i j v P) = evalPoly i j v P) :
    m ∈ P := by
  classical
  -- Every `m' ∈ P` has card 1 (since `¬ IsBasicZero` and `hno_edge`).
  have hcard1 : ∀ m' ∈ P, m'.card = 1 := by
    intro m' hm'
    have h1 := hpos m' hm'
    have hlt3 : m'.card ≤ 2 := by by_contra h; exact hnbz (Or.inl ⟨m', hm', by omega⟩)
    by_contra hne1
    have h2 : m'.card = 2 := by omega
    obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.mp h2
    by_cases hxy : x = y
    · subst hxy; exact hnbz (Or.inr (Or.inl ⟨x, hm'⟩))
    · exact hno_edge x y ⟨hxy, hm'⟩
  -- Define `v x := if ({x} : Mon) ∈ P then .c else .zero`!
  let v : ℕ → Elem6 := fun x => if ({x} : Mon) ∈ P then .c else .zero
  have hPv : evalPoly i j v P = .c := by
    obtain ⟨m₀, hm₀⟩ := hP
    obtain ⟨x₀, rfl⟩ := Multiset.card_eq_one.mp (hcard1 m₀ hm₀)
    refine evalPoly_eq_of_subset_eval i j v ⟨{x₀}, hm₀⟩ ?_ ⟨{x₀}, hm₀, by simp [evalMon_singleton, v, hm₀]⟩
    intro m' hm'
    obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp (hcard1 m' hm')
    simp [evalMon_singleton, v, hm', addR_idem']
  have hm_c := habs v
  rw [hPv] at hm_c
  -- Thus `evalMon v m ≠ .zero`, so `m.card = 1` (since `mulM .c .c = .zero` and `mulM _ .zero = .zero`!)
  have hm1 : m.card = 1 := by
    by_contra hne1
    have hm_z : evalMon v m = .zero := by
      by_cases h2 : m.card = 2
      · obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.mp h2
        rw [evalMon_pair]; dsimp only [v]; split_ifs <;> rfl
      · exact evalMon_card_ge_three v (by omega)
    rw [hm_z, addR_zero_left] at hm_c
    cases hm_c
  obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp hm1
  rw [evalMon_singleton] at hm_c
  by_contra hnot
  simp only [v, if_neg hnot, addR_zero_left] at hm_c
  cases hm_c

/-- Helper: `col` flipped on whole components remains a proper 2-coloring. -/
private lemma col_flip_proper {P : Poly} {col flip : ℕ → Bool}
    (hcol : ∀ a b, quadAdj P a b → col a ≠ col b)
    (hfl : ∀ a b, quadAdj P a b → flip a = flip b) :
    ∀ a b, quadAdj P a b → (xor (col a) (flip a)) ≠ (xor (col b) (flip b)) := by
  intro a b hab
  rw [hfl a b hab]
  have hne := hcol a b hab
  cases h1 : col a <;> cases h2 : col b <;> cases flip b <;> rw [h1, h2] at hne <;> simp_all

/-- Helper: parity of walks along a proper 2-coloring. -/
private lemma walk_col_parity {P : Poly} {col : ℕ → Bool}
    (hcol : ∀ a b, quadAdj P a b → col a ≠ col b)
    {u w k : ℕ} (hw : Walk P u w k) : (col u = col w ↔ k % 2 = 0) := by
  induction hw with
  | zero u => simp
  | @step a b c r hab _ ih =>
    have hne := hcol a b hab
    rcases Nat.mod_two_eq_zero_or_one r with hr0 | hr1
    · have hbc : col b = col c := ih.mpr hr0
      rw [← hbc]
      have h1 : (r + 1) % 2 ≠ 0 := by omega
      simp [hne, h1]
    · have hbc : col b ≠ col c := fun h => by have := ih.mp h; omega
      have hac : col a = col c := by cases h1 : col a <;> cases h2 : col b <;> cases h3 : col c <;> simp_all
      have h1 : (r + 1) % 2 = 0 := by omega
      simp [hac, h1]

/-- Helper: rule out `m.card ≥ 3` and `m = {x, x}` from any `R_{ij}`-homomorphism. -/
private lemma no_high_or_sq_of_hom {P : Poly} (hpos : ∀ m ∈ P, 1 ≤ m.card)
    (hnbz : ¬ IsBasicZero P) (hedge : ∃ a b, quadAdj P a b) {m : Mon} (hm_pos : 1 ≤ m.card)
    (i j : Fin 3) (v : ℕ → Elem6)
    (hlin : ∀ x, ({x} : Mon) ∈ P → addR i j (v x) .c = .c)
    (hquad : ∀ a b, quadAdj P a b → mulM (v a) (v b) = .c)
    (habs : ∀ w, addR i j (evalMon w m) (evalPoly i j w P) = evalPoly i j w P) :
    m.card = 1 ∨ (∃ x y, m = {x, y} ∧ x ≠ y) := by
  have hPc := evalPoly_eq_c_of_hom' i j v hpos hnbz hedge hlin hquad
  have hmc : addR i j (evalMon v m) .c = .c := by simpa [hPc] using habs v
  have hlt3 : m.card ≤ 2 := by
    by_contra h
    rw [evalMon_card_ge_three v (by omega), addR_zero_left] at hmc; cases hmc
  interval_cases hc : m.card
  · left; rfl
  · right
    obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.mp hc
    refine ⟨x, y, rfl, ?_⟩
    rintro rfl
    rw [evalMon_pair, mulM_diag, addR_zero_left] at hmc; cases hmc

/-- Helper: orient all marked components so marks have `col = false` when no odd walk links marks. -/
private lemma exists_marked_coloring {P : Poly} (hbip : ¬ HasOddCycle P)
    (hno_odd : ¬ ∃ w₁ w₂ k, marked P w₁ ∧ marked P w₂ ∧ Walk P w₁ w₂ (2 * k + 1)) :
    ∃ col : ℕ → Bool, (∀ a b, quadAdj P a b → col a ≠ col b) ∧ (∀ w, marked P w → col w = false) := by
  classical
  obtain ⟨col0, hcol0⟩ := exists_bipartite_coloring hbip
  let flip : ℕ → Bool := fun x => decide (∃ w k, marked P w ∧ Walk P w x k ∧ col0 w = true)
  have hfl : ∀ a b, quadAdj P a b → flip a = flip b := fun a b hab => by
    dsimp only [flip]; congr 1; apply propext
    constructor
    · rintro ⟨w, k, hmw, hwa, hc⟩
      exact ⟨w, k + 1, hmw, walk_trans hwa (Walk.step hab (Walk.zero b)), hc⟩
    · rintro ⟨w, k, hmw, hwb, hc⟩
      exact ⟨w, k + 1, hmw, walk_trans hwb (Walk.step (quadAdj_symm hab) (Walk.zero a)), hc⟩
  refine ⟨fun x => xor (col0 x) (flip x), col_flip_proper hcol0 hfl, fun w hmw => ?_⟩
  by_cases hc : col0 w = true
  · have hfw : flip w = true := by
      simp only [flip, decide_eq_true_eq]
      exact ⟨w, 0, hmw, Walk.zero w, hc⟩
    simp [hc, hfw]
  · have hc' : col0 w = false := Bool.eq_false_iff.mpr hc
    have hfw : flip w = false := by
      simp only [flip, decide_eq_false_iff_not]
      rintro ⟨w', k, hmw', hw'w, hc'w⟩
      have hne : col0 w' ≠ col0 w := by rw [hc'w, hc']; decide
      have hodd : k % 2 = 1 := by
        have := (walk_col_parity hcol0 hw'w).not.mp hne; omega
      exact hno_odd ⟨w', w, k / 2, hmw', hmw, by rwa [show 2 * (k / 2) + 1 = k by omega]⟩
    simp [hc', hfw]

/-- Tiny decidable multiplication helpers to keep `necessary_criteria_*` fast (< 10k heartbeats). -/
private lemma mulM_ab_of_ne : ∀ b1 b2 : Bool, b1 ≠ b2 → mulM (if b1 then .a else .b) (if b2 then .a else .b) = .c := by decide
private lemma mulM_pq_ab_of_ne : ∀ b1 b2 : Bool, b1 ≠ b2 → mulM (if b1 then .p else .q) (if b2 then .a else .b) = .c := by decide
private lemma mulM_ab_pq_of_ne : ∀ b1 b2 : Bool, b1 ≠ b2 → mulM (if b1 then .a else .b) (if b2 then .p else .q) = .c := by decide
private lemma mulM_pq_pq_of_ne : ∀ b1 b2 : Bool, b1 ≠ b2 → mulM (if b1 then .p else .q) (if b2 then .p else .q) = .zero := by decide
private lemma bool_ne_true : ∀ b : Bool, true ≠ b → b = false := by decide
private lemma bool_ne_false : ∀ b : Bool, false ≠ b → b = true := by decide

/-- Necessary criterion (a) for `R_{01}` (Theorem 3.1(a)). -/
private lemma necessary_criteria_01 {P : Poly} (hpos : ∀ m ∈ P, 1 ≤ m.card)
    (hnbz : ¬ IsBasicZero P) (hedge : ∃ a b, quadAdj P a b) {m : Mon} (hm_pos : 1 ≤ m.card)
    (habs : ∀ v, addR 0 1 (evalMon v m) (evalPoly 0 1 v P) = evalPoly 0 1 v P) :
    m ∈ P ∨
    (∃ w₁ w₂ k, marked P w₁ ∧ marked P w₂ ∧ Walk P w₁ w₂ (2 * k + 1)) ∨
    (∃ x y, m = {x, y} ∧ x ≠ y ∧ marked P x ∧ ∃ w k, marked P w ∧ Walk P w y (2 * k + 1)) := by
  classical
  have hbip : ¬ HasOddCycle P := fun h => hnbz (Or.inr (Or.inr h))
  have hvalid_col : ∀ (v : ℕ → Elem6),
      (∀ x, ({x} : Mon) ∈ P → addR 0 1 (v x) .c = .c) →
      (∀ a b, quadAdj P a b → mulM (v a) (v b) = .c) →
      addR 0 1 (evalMon v m) .c = .c := fun v hlin hquad => by
    have hPc := evalPoly_eq_c_of_hom' 0 1 v hpos hnbz hedge hlin hquad
    simpa [hPc] using habs v
  by_cases hodd_m : ∃ w₁ w₂ k, marked P w₁ ∧ marked P w₂ ∧ Walk P w₁ w₂ (2 * k + 1)
  · right; left; exact hodd_m
  · obtain ⟨col, hcol, hcol_m⟩ := exists_marked_coloring hbip hodd_m
    let v_base : ℕ → Elem6 := fun x =>
      if quadVert P x then (if col x then .a else .b)
      else if ({x} : Mon) ∈ P then .c else .zero
    have hlin_b : ∀ x, ({x} : Mon) ∈ P → addR 0 1 (v_base x) .c = .c := fun x hx => by
      dsimp only [v_base]
      by_cases hqv : quadVert P x
      · rw [if_pos hqv, hcol_m x ⟨hx, hqv⟩]; rfl
      · rw [if_neg hqv, if_pos hx]; rfl
    have hquad_b : ∀ a b, quadAdj P a b → mulM (v_base a) (v_base b) = .c := fun a b hab => by
      have hqa : quadVert P a := ⟨b, hab⟩
      have hqb : quadVert P b := ⟨a, quadAdj_symm hab⟩
      have hne := hcol a b hab
      dsimp only [v_base]; rw [if_pos hqa, if_pos hqb]
      exact mulM_ab_of_ne _ _ hne
    rcases no_high_or_sq_of_hom hpos hnbz hedge hm_pos 0 1 v_base hlin_b hquad_b habs with hm1 | ⟨x, y, rfl, hxy⟩
    · obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp hm1
      left; by_contra hnot
      let v : ℕ → Elem6 := fun z =>
        if z = x then (if quadVert P x then (if col x then .p else .q) else .zero)
        else v_base z
      have hlin : ∀ z, ({z} : Mon) ∈ P → addR 0 1 (v z) .c = .c := fun z hz => by
        have hzx : z ≠ x := fun h => hnot (h ▸ hz)
        simp only [v, if_neg hzx]; exact hlin_b z hz
      have hquad : ∀ a b, quadAdj P a b → mulM (v a) (v b) = .c := fun a b hab => by
        have hqa : quadVert P a := ⟨b, hab⟩
        have hqb : quadVert P b := ⟨a, quadAdj_symm hab⟩
        have hne := hcol a b hab
        by_cases ha : a = x
        · subst ha
          have hb : b ≠ a := hab.1.symm
          simp only [v, if_pos rfl, if_neg hb, v_base, if_pos hqa, if_pos hqb]
          cases h1 : col a <;> cases h2 : col b <;> rw [h1, h2] at hne <;> simp_all [mulM]
        · by_cases hb : b = x
          · subst hb
            simp only [v, if_neg ha, if_pos rfl, v_base, if_pos hqa, if_pos hqb]
            cases h1 : col a <;> cases h2 : col b <;> rw [h1, h2] at hne <;> simp_all [mulM]
          · simp only [v, if_neg ha, if_neg hb]; exact hquad_b a b hab
      have hmc := hvalid_col v hlin hquad
      rw [evalMon_singleton] at hmc
      dsimp only [v] at hmc; rw [if_pos rfl] at hmc
      by_cases hqx : quadVert P x
      · rw [if_pos hqx] at hmc; cases h1 : col x <;> rw [h1] at hmc <;> simp [addR, belowC] at hmc
      · rw [if_neg hqx] at hmc; simp [addR_zero_left] at hmc
    · by_cases hmem : ({x, y} : Mon) ∈ P
      · left; exact hmem
      · have hqx : quadVert P x := by
          by_contra hnx
          have hmc := hvalid_col v_base hlin_b hquad_b
          rw [evalMon_pair] at hmc
          have hvx : v_base x = .c ∨ v_base x = .zero := by dsimp only [v_base]; rw [if_neg hnx]; split_ifs <;> simp
          rcases hvx with h | h <;> rw [h] at hmc <;> cases h2 : v_base y <;> rw [h2] at hmc <;> simp [mulM, addR_zero_left] at hmc
        have hqy : quadVert P y := by
          by_contra hny
          have hmc := hvalid_col v_base hlin_b hquad_b
          rw [evalMon_pair] at hmc
          have hvy : v_base y = .c ∨ v_base y = .zero := by dsimp only [v_base]; rw [if_neg hny]; split_ifs <;> simp
          rcases hvy with h | h <;> rw [h] at hmc <;> cases h2 : v_base x <;> rw [h2] at hmc <;> simp [mulM, addR_zero_left] at hmc
        have hcol_ne : col x ≠ col y := by
          intro heq
          have hmc := hvalid_col v_base hlin_b hquad_b
          rw [evalMon_pair] at hmc
          have : v_base x = v_base y := by simp [v_base, hqx, hqy, heq]
          rw [this, mulM_diag, addR_zero_left] at hmc; cases hmc
        have hcase : ∀ u w : ℕ, ({x, y} : Mon) = {u, w} → u ≠ w → ({u, w} : Mon) ∉ P →
            quadVert P u → quadVert P w → col u = false → col w = true →
            marked P u ∧ ∃ m₀ k, marked P m₀ ∧ Walk P m₀ w (2 * k + 1) := by
          intro u w hxy_uw huw hnotuw hqu hqw hcu hcw
          have hmu : marked P u := by
            by_contra hnu
            let v : ℕ → Elem6 := fun z =>
              if z = u then .q else if z = w then .p else v_base z
            have hlin : ∀ z, ({z} : Mon) ∈ P → addR 0 1 (v z) .c = .c := fun z hz => by
              have hzu : z ≠ u := fun h => hnu ⟨h ▸ hz, hqu⟩
              have hzw : z ≠ w := fun h => by
                have hmw : marked P w := ⟨h ▸ hz, hqw⟩
                have := hcol_m w hmw; rw [hcw] at this; cases this
              simp only [v, if_neg hzu, if_neg hzw]; exact hlin_b z hz
            have hquad : ∀ a b, quadAdj P a b → mulM (v a) (v b) = .c := fun a b hab => by
              have hqa : quadVert P a := ⟨b, hab⟩
              have hqb : quadVert P b := ⟨a, quadAdj_symm hab⟩
              by_cases hau : a = u
              · subst hau
                have hbw : b ≠ w := fun h => hnotuw (h ▸ hab.2)
                have hbu : b ≠ a := hab.1.symm
                have hcb : col b = true := bool_ne_false _ (hcu ▸ hcol a b hab)
                dsimp only [v]; rw [if_pos rfl, if_neg hbu, if_neg hbw]; dsimp only [v_base]; rw [if_pos hqb, hcb]; rfl
              · by_cases hbu : b = u
                · subst hbu
                  have haw : a ≠ w := fun h => hnotuw (by rw [Multiset.pair_comm]; exact h ▸ hab.2)
                  have hca : col a = true := bool_ne_false _ (hcu ▸ (hcol a b hab).symm)
                  dsimp only [v]; rw [if_neg hau, if_neg haw, if_pos rfl]; dsimp only [v_base]; rw [if_pos hqa, hca]; rfl
                · by_cases haw : a = w
                  · subst haw
                    have hbw : b ≠ a := hab.1.symm
                    have hcb : col b = false := bool_ne_true _ (hcw ▸ hcol a b hab)
                    dsimp only [v]; rw [if_neg hau, if_pos rfl, if_neg hbu, if_neg hbw]; dsimp only [v_base]; rw [if_pos hqb, hcb]; rfl
                  · by_cases hbw : b = w
                    · subst hbw
                      have hca : col a = false := bool_ne_true _ (hcw ▸ (hcol a b hab).symm)
                      dsimp only [v]; rw [if_neg hau, if_neg haw, if_neg hbu, if_pos rfl]; dsimp only [v_base]; rw [if_pos hqa, hca]; rfl
                    · simp only [v, if_neg hau, if_neg haw, if_neg hbu, if_neg hbw]; exact hquad_b a b hab
            have hmc := hvalid_col v hlin hquad
            rw [hxy_uw, evalMon_pair] at hmc
            simp only [v, if_pos rfl, if_neg huw.symm, mulM] at hmc
            simp [addR_zero_left] at hmc
          refine ⟨hmu, ?_⟩
          by_contra hno_w
          have hno_comp_mark : ∀ z k, Walk P w z k → ¬ marked P z := by
            intro z k hwz hmz
            have hcz : col z = false := hcol_m z hmz
            have hne : col w ≠ col z := by rw [hcw, hcz]; decide
            have hodd : k % 2 = 1 := by have := (walk_col_parity hcol hwz).not.mp hne; omega
            exact hno_w ⟨z, k / 2, hmz, by rw [show 2 * (k / 2) + 1 = k by omega]; exact walk_symm hwz⟩
          let flipW : ℕ → Bool := fun z => decide (∃ k, Walk P w z k)
          have hflW : ∀ a b, quadAdj P a b → flipW a = flipW b := fun a b hab => by
            dsimp only [flipW]; congr 1; apply propext
            exact ⟨fun ⟨k, h⟩ => ⟨k + 1, walk_trans h (Walk.step hab (Walk.zero b))⟩,
                   fun ⟨k, h⟩ => ⟨k + 1, walk_trans h (Walk.step (quadAdj_symm hab) (Walk.zero a))⟩⟩
          let col' : ℕ → Bool := fun z => xor (col z) (flipW z)
          have hcol' : ∀ a b, quadAdj P a b → col' a ≠ col' b := col_flip_proper hcol hflW
          have hcol'_m : ∀ z, marked P z → col' z = false := fun z hmz => by
            have hfw : flipW z = false := by
              simp only [flipW, decide_eq_false_iff_not]; rintro ⟨k, hk⟩; exact hno_comp_mark z k hk hmz
            simp [col', hcol_m z hmz, hfw]
          have hcol'_w : col' w = false := by
            have hfw : flipW w = true := by simp only [flipW, decide_eq_true_eq]; exact ⟨0, Walk.zero w⟩
            simp [col', hcw, hfw]
          let v' : ℕ → Elem6 := fun z =>
            if quadVert P z then (if col' z then .a else .b)
            else if ({z} : Mon) ∈ P then .c else .zero
          have hlin' : ∀ z, ({z} : Mon) ∈ P → addR 0 1 (v' z) .c = .c := fun z hz => by
            dsimp only [v']
            by_cases hqv : quadVert P z
            · rw [if_pos hqv, hcol'_m z ⟨hz, hqv⟩]; rfl
            · rw [if_neg hqv, if_pos hz]; rfl
          have hquad' : ∀ a b, quadAdj P a b → mulM (v' a) (v' b) = .c := fun a b hab => by
            have hqa : quadVert P a := ⟨b, hab⟩
            have hqb : quadVert P b := ⟨a, quadAdj_symm hab⟩
            have hne := hcol' a b hab
            dsimp only [v']; rw [if_pos hqa, if_pos hqb]
            exact mulM_ab_of_ne _ _ hne
          have hmc := hvalid_col v' hlin' hquad'
          rw [hxy_uw, evalMon_pair] at hmc
          have hvu : v' u = .b := by simp [v', hqu, hcol'_m u hmu]
          have hvw : v' w = .b := by simp [v', hqw, hcol'_w]
          rw [hvu, hvw, mulM_diag, addR_zero_left] at hmc
          cases hmc
        right; right
        cases hx : col x
        · have hy : col y = true := by cases h : col y <;> simp_all
          obtain ⟨hmx, m₀, k, hm₀, hwalk⟩ := hcase x y rfl hxy hmem hqx hqy hx hy
          exact ⟨x, y, rfl, hxy, hmx, m₀, k, hm₀, hwalk⟩
        · have hy : col y = false := by cases h : col y <;> simp_all
          obtain ⟨hmy, m₀, k, hm₀, hwalk⟩ :=
            hcase y x (Multiset.pair_comm x y) hxy.symm (by rwa [Multiset.pair_comm]) hqy hqx hy hx
          exact ⟨y, x, Multiset.pair_comm x y, hxy.symm, hmy, m₀, k, hm₀, hwalk⟩

/-- Necessary criterion (b) for `R_{02}` (Theorem 3.1(b)). -/
private lemma necessary_criteria_02 {P : Poly} (hpos : ∀ m ∈ P, 1 ≤ m.card)
    (hnbz : ¬ IsBasicZero P) (hedge : ∃ a b, quadAdj P a b) {m : Mon} (hm_pos : 1 ≤ m.card)
    (habs : ∀ v, addR 0 2 (evalMon v m) (evalPoly 0 2 v P) = evalPoly 0 2 v P) :
    m ∈ P ∨
    (∃ w₁ w₂ k, marked P w₁ ∧ marked P w₂ ∧ Walk P w₁ w₂ (2 * k + 1)) ∨
    (∃ x, m = {x} ∧ ∃ w k, marked P w ∧ Walk P w x (2 * k)) := by
  classical
  have hbip : ¬ HasOddCycle P := fun h => hnbz (Or.inr (Or.inr h))
  have hvalid_col : ∀ (v : ℕ → Elem6),
      (∀ x, ({x} : Mon) ∈ P → addR 0 2 (v x) .c = .c) →
      (∀ a b, quadAdj P a b → mulM (v a) (v b) = .c) →
      addR 0 2 (evalMon v m) .c = .c := fun v hlin hquad => by
    have hPc := evalPoly_eq_c_of_hom' 0 2 v hpos hnbz hedge hlin hquad
    simpa [hPc] using habs v
  by_cases hodd_m : ∃ w₁ w₂ k, marked P w₁ ∧ marked P w₂ ∧ Walk P w₁ w₂ (2 * k + 1)
  · right; left; exact hodd_m
  · obtain ⟨col, hcol, hcol_m⟩ := exists_marked_coloring hbip hodd_m
    let v_base : ℕ → Elem6 := fun x =>
      if quadVert P x then (if col x then .a else .b)
      else if ({x} : Mon) ∈ P then .c else .zero
    have hlin_b : ∀ x, ({x} : Mon) ∈ P → addR 0 2 (v_base x) .c = .c := fun x hx => by
      dsimp only [v_base]
      by_cases hqv : quadVert P x
      · rw [if_pos hqv, hcol_m x ⟨hx, hqv⟩]; rfl
      · rw [if_neg hqv, if_pos hx]; rfl
    have hquad_b : ∀ a b, quadAdj P a b → mulM (v_base a) (v_base b) = .c := fun a b hab => by
      have hqa : quadVert P a := ⟨b, hab⟩
      have hqb : quadVert P b := ⟨a, quadAdj_symm hab⟩
      have hne := hcol a b hab
      dsimp only [v_base]; rw [if_pos hqa, if_pos hqb]
      exact mulM_ab_of_ne _ _ hne
    rcases no_high_or_sq_of_hom hpos hnbz hedge hm_pos 0 2 v_base hlin_b hquad_b habs with hm1 | ⟨x, y, rfl, hxy⟩
    · obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp hm1
      by_cases hmem : ({x} : Mon) ∈ P
      · left; exact hmem
      · right; right
        refine ⟨x, rfl, ?_⟩
        by_contra hno_ew
        have hqx : quadVert P x := by
          by_contra hnx
          have hmc := hvalid_col v_base hlin_b hquad_b
          rw [evalMon_singleton] at hmc
          simp only [v_base, if_neg hnx, if_neg hmem, addR_zero_left] at hmc
          cases hmc
        have hno_comp_mark : ∀ z k, Walk P x z k → ¬ marked P z := by
          intro z k hxz hmz
          have hcz : col z = false := hcol_m z hmz
          by_cases hcx : col x = false
          · have hev : k % 2 = 0 := (walk_col_parity hcol hxz).mp (hcx.trans hcz.symm)
            exact hno_ew ⟨z, k / 2, hmz, by rw [show 2 * (k / 2) = k by omega]; exact walk_symm hxz⟩
          · have hcx' : col x = true := Bool.eq_true_of_not_eq_false hcx
            have hmc := hvalid_col v_base hlin_b hquad_b
            rw [evalMon_singleton] at hmc
            simp only [v_base, if_pos hqx, hcx', if_true] at hmc
            simp [addR, belowC] at hmc
        let flipX : ℕ → Bool := fun z => decide (∃ k, Walk P x z k)
        have hflX : ∀ a b, quadAdj P a b → flipX a = flipX b := fun a b hab => by
          dsimp only [flipX]; congr 1; apply propext
          exact ⟨fun ⟨k, h⟩ => ⟨k + 1, walk_trans h (Walk.step hab (Walk.zero b))⟩,
                 fun ⟨k, h⟩ => ⟨k + 1, walk_trans h (Walk.step (quadAdj_symm hab) (Walk.zero a))⟩⟩
        let col' : ℕ → Bool := fun z => if col x then col z else xor (col z) (flipX z)
        have hcol' : ∀ a b, quadAdj P a b → col' a ≠ col' b := fun a b hab => by
          dsimp only [col']
          split_ifs
          · exact hcol a b hab
          · exact col_flip_proper hcol hflX a b hab
        have hcol'_m : ∀ z, marked P z → col' z = false := fun z hmz => by
          dsimp only [col']; split_ifs
          · exact hcol_m z hmz
          · have hfx : flipX z = false := by
              simp only [flipX, decide_eq_false_iff_not]; rintro ⟨k, hk⟩; exact hno_comp_mark z k hk hmz
            simp [hcol_m z hmz, hfx]
        have hcol'_x : col' x = true := by
          dsimp only [col']
          cases hx : col x
          · have hfx : flipX x = true := by simp only [flipX, decide_eq_true_eq]; exact ⟨0, Walk.zero x⟩
            simp [hfx]
          · simp
        let v' : ℕ → Elem6 := fun z =>
          if quadVert P z then (if col' z then .a else .b)
          else if ({z} : Mon) ∈ P then .c else .zero
        have hlin' : ∀ z, ({z} : Mon) ∈ P → addR 0 2 (v' z) .c = .c := fun z hz => by
          dsimp only [v']
          by_cases hqv : quadVert P z
          · rw [if_pos hqv, hcol'_m z ⟨hz, hqv⟩]; rfl
          · rw [if_neg hqv, if_pos hz]; rfl
        have hquad' : ∀ a b, quadAdj P a b → mulM (v' a) (v' b) = .c := fun a b hab => by
          have hqa : quadVert P a := ⟨b, hab⟩
          have hqb : quadVert P b := ⟨a, quadAdj_symm hab⟩
          have hne := hcol' a b hab
          dsimp only [v']; rw [if_pos hqa, if_pos hqb]
          cases h1 : col' a <;> cases h2 : col' b <;> rw [h1, h2] at hne <;> simp_all [mulM]
        have hmc := hvalid_col v' hlin' hquad'
        rw [evalMon_singleton] at hmc
        simp only [v', if_pos hqx, hcol'_x, if_true] at hmc
        simp [addR, belowC] at hmc
    · left; by_contra hmem
      have hqx : quadVert P x := by
        by_contra hnx
        have hmc := hvalid_col v_base hlin_b hquad_b
        rw [evalMon_pair] at hmc
        have hvx : v_base x = .c ∨ v_base x = .zero := by dsimp only [v_base]; rw [if_neg hnx]; split_ifs <;> simp
        rcases hvx with h | h <;> rw [h] at hmc <;> cases h2 : v_base y <;> rw [h2] at hmc <;> simp [mulM, addR_zero_left] at hmc
      have hqy : quadVert P y := by
        by_contra hny
        have hmc := hvalid_col v_base hlin_b hquad_b
        rw [evalMon_pair] at hmc
        have hvy : v_base y = .c ∨ v_base y = .zero := by dsimp only [v_base]; rw [if_neg hny]; split_ifs <;> simp
        rcases hvy with h | h <;> rw [h] at hmc <;> cases h2 : v_base x <;> rw [h2] at hmc <;> simp [mulM, addR_zero_left] at hmc
      have hcol_ne : col x ≠ col y := by
        intro heq
        have hmc := hvalid_col v_base hlin_b hquad_b
        rw [evalMon_pair] at hmc
        have : v_base x = v_base y := by simp [v_base, hqx, hqy, heq]
        rw [this, mulM_diag, addR_zero_left] at hmc; cases hmc
      let v : ℕ → Elem6 := fun z =>
        if z = x then (if col x then .p else .q)
        else if z = y then (if col y then .p else .q)
        else v_base z
      have hlin : ∀ z, ({z} : Mon) ∈ P → addR 0 2 (v z) .c = .c := fun z hz => by
        by_cases hzx : z = x
        · subst hzx; have hmx : marked P z := ⟨hz, hqx⟩
          simp [v, hcol_m z hmx, addR, belowC]
        · by_cases hzy : z = y
          · subst hzy; have hmy : marked P z := ⟨hz, hqy⟩
            simp [v, hzx, hcol_m z hmy, addR, belowC]
          · simp only [v, if_neg hzx, if_neg hzy]; exact hlin_b z hz
      have hquad : ∀ a b, quadAdj P a b → mulM (v a) (v b) = .c := fun a b hab => by
        have hqa : quadVert P a := ⟨b, hab⟩
        have hqb : quadVert P b := ⟨a, quadAdj_symm hab⟩
        have hne := hcol a b hab
        by_cases hax : a = x
        · subst hax
          have hby : b ≠ y := fun h => hmem (h ▸ hab.2)
          have hbx : b ≠ a := hab.1.symm
          dsimp only [v]; rw [if_pos rfl, if_neg hbx, if_neg hby]; dsimp only [v_base]; rw [if_pos hqb]
          exact mulM_pq_ab_of_ne _ _ hne
        · by_cases hbx : b = x
          · subst hbx
            have hay : a ≠ y := fun h => hmem (by rw [Multiset.pair_comm]; exact h ▸ hab.2)
            dsimp only [v]; rw [if_neg hax, if_neg hay, if_pos rfl]; dsimp only [v_base]; rw [if_pos hqa]
            exact mulM_ab_pq_of_ne _ _ hne
          · by_cases hay : a = y
            · subst hay
              have hby : b ≠ a := hab.1.symm
              dsimp only [v]; rw [if_neg hax, if_pos rfl, if_neg hbx, if_neg hby]; dsimp only [v_base]; rw [if_pos hqb]
              exact mulM_pq_ab_of_ne _ _ hne
            · by_cases hby : b = y
              · subst hby
                dsimp only [v]; rw [if_neg hax, if_neg hay, if_neg hbx, if_pos rfl]; dsimp only [v_base]; rw [if_pos hqa]
                exact mulM_ab_pq_of_ne _ _ hne
              · simp only [v, if_neg hax, if_neg hay, if_neg hbx, if_neg hby]; exact hquad_b a b hab
      have hmc := hvalid_col v hlin hquad
      rw [evalMon_pair] at hmc
      dsimp only [v] at hmc; rw [if_pos rfl, if_neg hxy.symm, if_pos rfl] at hmc
      rw [mulM_pq_pq_of_ne _ _ hcol_ne, addR_zero_left] at hmc; cases hmc

/-- Necessary criterion (c) for `R_{11}` (Theorem 3.1(c)). -/
private lemma necessary_criteria_11 {P : Poly} (hpos : ∀ m ∈ P, 1 ≤ m.card)
    (hnbz : ¬ IsBasicZero P) (hedge : ∃ a b, quadAdj P a b) {m : Mon} (hm_pos : 1 ≤ m.card)
    (habs : ∀ v, addR 1 1 (evalMon v m) (evalPoly 1 1 v P) = evalPoly 1 1 v P) :
    m ∈ P ∨
    (∃ x y k, m = {x, y} ∧ x ≠ y ∧ (marked P x ∨ marked P y) ∧ Walk P x y (2 * k + 1)) := by
  classical
  have hbip : ¬ HasOddCycle P := fun h => hnbz (Or.inr (Or.inr h))
  obtain ⟨col0, hcol0⟩ := exists_bipartite_coloring hbip
  have hvalid_col : ∀ (v : ℕ → Elem6),
      (∀ x, ({x} : Mon) ∈ P → addR 1 1 (v x) .c = .c) →
      (∀ a b, quadAdj P a b → mulM (v a) (v b) = .c) →
      addR 1 1 (evalMon v m) .c = .c := fun v hlin hquad => by
    have hPc := evalPoly_eq_c_of_hom' 1 1 v hpos hnbz hedge hlin hquad
    simpa [hPc] using habs v
  let v_base : ℕ → Elem6 := fun z =>
    if quadVert P z then (if col0 z then .a else .b)
    else if ({z} : Mon) ∈ P then .c else .zero
  have hlin_b : ∀ z, ({z} : Mon) ∈ P → addR 1 1 (v_base z) .c = .c := fun z hz => by
    dsimp only [v_base]; by_cases hqv : quadVert P z
    · rw [if_pos hqv]; cases col0 z <;> rfl
    · rw [if_neg hqv, if_pos hz]; rfl
  have hquad_b : ∀ a b, quadAdj P a b → mulM (v_base a) (v_base b) = .c := fun a b hab => by
    have hqa : quadVert P a := ⟨b, hab⟩
    have hqb : quadVert P b := ⟨a, quadAdj_symm hab⟩
    have hne := hcol0 a b hab
    dsimp only [v_base]; rw [if_pos hqa, if_pos hqb]
    cases ha : col0 a <;> cases hb : col0 b <;> rw [ha, hb] at hne <;> simp_all [mulM]
  rcases no_high_or_sq_of_hom hpos hnbz hedge hm_pos 1 1 v_base hlin_b hquad_b habs with hm1 | ⟨x, y, rfl, hxy⟩
  · obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp hm1
    left; by_contra hnot
    let v : ℕ → Elem6 := fun z =>
      if z = x then (if quadVert P x then (if col0 x then .p else .q) else .zero)
      else v_base z
    have hlin : ∀ z, ({z} : Mon) ∈ P → addR 1 1 (v z) .c = .c := fun z hz => by
      have hzx : z ≠ x := fun h => hnot (h ▸ hz)
      simp only [v, if_neg hzx]; exact hlin_b z hz
    have hquad : ∀ a b, quadAdj P a b → mulM (v a) (v b) = .c := fun a b hab => by
      have hqa : quadVert P a := ⟨b, hab⟩
      have hqb : quadVert P b := ⟨a, quadAdj_symm hab⟩
      have hne := hcol0 a b hab
      by_cases hax : a = x
      · subst hax; have hbx : b ≠ a := hab.1.symm
        simp only [v, if_pos rfl, if_neg hbx, v_base, if_pos hqa, if_pos hqb]
        cases h1 : col0 a <;> cases h2 : col0 b <;> rw [h1, h2] at hne <;> simp_all [mulM]
      · by_cases hbx : b = x
        · subst hbx
          simp only [v, if_neg hax, if_pos rfl, v_base, if_pos hqa, if_pos hqb]
          cases h1 : col0 a <;> cases h2 : col0 b <;> rw [h1, h2] at hne <;> simp_all [mulM]
        · simp only [v, if_neg hax, if_neg hbx]; exact hquad_b a b hab
    have hmc := hvalid_col v hlin hquad
    rw [evalMon_singleton] at hmc
    dsimp only [v] at hmc; rw [if_pos rfl] at hmc
    by_cases hqx : quadVert P x
    · rw [if_pos hqx] at hmc; cases h1 : col0 x <;> rw [h1] at hmc <;> simp [addR, belowC] at hmc
    · rw [if_neg hqx] at hmc; simp [addR_zero_left] at hmc
  · by_cases hmem : ({x, y} : Mon) ∈ P
    · left; exact hmem
    · right
      have hqx : quadVert P x := by
        by_contra hnx
        have hmc := hvalid_col v_base hlin_b hquad_b
        rw [evalMon_pair] at hmc
        have hvx : v_base x = .c ∨ v_base x = .zero := by dsimp only [v_base]; rw [if_neg hnx]; split_ifs <;> simp
        rcases hvx with h | h <;> rw [h] at hmc <;> cases h2 : v_base y <;> rw [h2] at hmc <;> simp [mulM, addR_zero_left] at hmc
      have hqy : quadVert P y := by
        by_contra hny
        have hmc := hvalid_col v_base hlin_b hquad_b
        rw [evalMon_pair] at hmc
        have hvy : v_base y = .c ∨ v_base y = .zero := by dsimp only [v_base]; rw [if_neg hny]; split_ifs <;> simp
        rcases hvy with h | h <;> rw [h] at hmc <;> cases h2 : v_base x <;> rw [h2] at hmc <;> simp [mulM, addR_zero_left] at hmc
      have hwalk_xy : ∃ k, Walk P x y (2 * k + 1) := by
        by_contra hno_odd
        by_cases hsame : ∃ k, Walk P x y k
        · obtain ⟨k, hwk⟩ := hsame
          have hev : k % 2 = 0 := by
            rcases Nat.mod_two_eq_zero_or_one k with h0 | h1; exact h0
            exfalso; exact hno_odd ⟨k / 2, by rwa [show 2 * (k / 2) + 1 = k by omega]⟩
          have hcol_eq : col0 x = col0 y := (walk_col_parity hcol0 hwk).mpr hev
          have hmc := hvalid_col v_base hlin_b hquad_b
          rw [evalMon_pair] at hmc
          have : v_base x = v_base y := by simp [v_base, hqx, hqy, hcol_eq]
          rw [this, mulM_diag, addR_zero_left] at hmc; cases hmc
        · let flipY : ℕ → Bool := fun z => decide (∃ k, Walk P y z k)
          have hflY : ∀ a b, quadAdj P a b → flipY a = flipY b := fun a b hab => by
            dsimp only [flipY]; congr 1; apply propext
            exact ⟨fun ⟨k, h⟩ => ⟨k + 1, walk_trans h (Walk.step hab (Walk.zero b))⟩,
                   fun ⟨k, h⟩ => ⟨k + 1, walk_trans h (Walk.step (quadAdj_symm hab) (Walk.zero a))⟩⟩
          let col' : ℕ → Bool := fun z => if col0 x = col0 y then col0 z else xor (col0 z) (flipY z)
          have hcol' : ∀ a b, quadAdj P a b → col' a ≠ col' b := fun a b hab => by
            dsimp only [col']; split_ifs
            · exact hcol0 a b hab
            · exact col_flip_proper hcol0 hflY a b hab
          have hcol'_eq : col' x = col' y := by
            dsimp only [col']
            by_cases hxyc : col0 x = col0 y
            · simp [hxyc]
            · have hfx : flipY x = false := by
                simp only [flipY, decide_eq_false_iff_not]; rintro ⟨k, hk⟩; exact hsame ⟨k, walk_symm hk⟩
              have hfy : flipY y = true := by simp only [flipY, decide_eq_true_eq]; exact ⟨0, Walk.zero y⟩
              simp only [if_neg hxyc, hfx, hfy]
              cases h1 : col0 x <;> cases h2 : col0 y <;> simp_all
          let v' : ℕ → Elem6 := fun z =>
            if quadVert P z then (if col' z then .a else .b)
            else if ({z} : Mon) ∈ P then .c else .zero
          have hlin' : ∀ z, ({z} : Mon) ∈ P → addR 1 1 (v' z) .c = .c := fun z hz => by
            dsimp only [v']; by_cases hqv : quadVert P z
            · rw [if_pos hqv]; cases col' z <;> rfl
            · rw [if_neg hqv, if_pos hz]; rfl
          have hquad' : ∀ a b, quadAdj P a b → mulM (v' a) (v' b) = .c := fun a b hab => by
            have hqa : quadVert P a := ⟨b, hab⟩
            have hqb : quadVert P b := ⟨a, quadAdj_symm hab⟩
            have hne := hcol' a b hab
            dsimp only [v']; rw [if_pos hqa, if_pos hqb]
            exact mulM_ab_of_ne _ _ hne
          have hmc := hvalid_col v' hlin' hquad'
          rw [evalMon_pair] at hmc
          have : v' x = v' y := by simp [v', hqx, hqy, hcol'_eq]
          rw [this, mulM_diag, addR_zero_left] at hmc; cases hmc
      obtain ⟨k, hwk⟩ := hwalk_xy
      refine ⟨x, y, k, rfl, hxy, ?_, hwk⟩
      by_contra hboth
      push Not at hboth
      rcases hboth with ⟨hnx, hny⟩
      have hcol_ne : col0 x ≠ col0 y := (walk_col_parity hcol0 hwk).not.mpr (by omega)
      let v : ℕ → Elem6 := fun z =>
        if z = x then (if col0 x then .p else .q)
        else if z = y then (if col0 y then .p else .q)
        else v_base z
      have hlin : ∀ z, ({z} : Mon) ∈ P → addR 1 1 (v z) .c = .c := fun z hz => by
        have hzx : z ≠ x := fun h => hnx ⟨h ▸ hz, hqx⟩
        have hzy : z ≠ y := fun h => hny ⟨h ▸ hz, hqy⟩
        simp only [v, if_neg hzx, if_neg hzy]; exact hlin_b z hz
      have hquad : ∀ a b, quadAdj P a b → mulM (v a) (v b) = .c := fun a b hab => by
        have hqa : quadVert P a := ⟨b, hab⟩
        have hqb : quadVert P b := ⟨a, quadAdj_symm hab⟩
        have hne := hcol0 a b hab
        by_cases hax : a = x
        · subst hax
          have hby : b ≠ y := fun h => hmem (h ▸ hab.2)
          have hbx : b ≠ a := hab.1.symm
          dsimp only [v]; rw [if_pos rfl, if_neg hbx, if_neg hby]; dsimp only [v_base]; rw [if_pos hqb]
          exact mulM_pq_ab_of_ne _ _ hne
        · by_cases hbx : b = x
          · subst hbx
            have hay : a ≠ y := fun h => hmem (by rw [Multiset.pair_comm]; exact h ▸ hab.2)
            dsimp only [v]; rw [if_neg hax, if_neg hay, if_pos rfl]; dsimp only [v_base]; rw [if_pos hqa]
            exact mulM_ab_pq_of_ne _ _ hne
          · by_cases hay : a = y
            · subst hay; have hby : b ≠ a := hab.1.symm
              dsimp only [v]; rw [if_neg hax, if_pos rfl, if_neg hbx, if_neg hby]; dsimp only [v_base]; rw [if_pos hqb]
              exact mulM_pq_ab_of_ne _ _ hne
            · by_cases hby : b = y
              · subst hby
                dsimp only [v]; rw [if_neg hax, if_neg hay, if_neg hbx, if_pos rfl]; dsimp only [v_base]; rw [if_pos hqa]
                exact mulM_ab_pq_of_ne _ _ hne
              · simp only [v, if_neg hax, if_neg hay, if_neg hbx, if_neg hby]; exact hquad_b a b hab
      have hmc := hvalid_col v hlin hquad
      rw [evalMon_pair] at hmc
      dsimp only [v] at hmc; rw [if_pos rfl, if_neg hxy.symm, if_pos rfl] at hmc
      rw [mulM_pq_pq_of_ne _ _ hcol_ne, addR_zero_left] at hmc; cases hmc

/-- Necessary criterion (d) for `R_{12}` (Theorem 3.1(d)). -/
private lemma necessary_criteria_12 {P : Poly} (hpos : ∀ m ∈ P, 1 ≤ m.card)
    (hnbz : ¬ IsBasicZero P) (hedge : ∃ a b, quadAdj P a b) {m : Mon} (hm_pos : 1 ≤ m.card)
    (habs : ∀ v, addR 1 2 (evalMon v m) (evalPoly 1 2 v P) = evalPoly 1 2 v P) :
    m ∈ P ∨
    (∃ x y k, m = {x, y} ∧ x ≠ y ∧ marked P x ∧ marked P y ∧ Walk P x y (2 * k + 1)) := by
  classical
  have hbip : ¬ HasOddCycle P := fun h => hnbz (Or.inr (Or.inr h))
  obtain ⟨col0, hcol0⟩ := exists_bipartite_coloring hbip
  have hvalid_col : ∀ (v : ℕ → Elem6),
      (∀ x, ({x} : Mon) ∈ P → addR 1 2 (v x) .c = .c) →
      (∀ a b, quadAdj P a b → mulM (v a) (v b) = .c) →
      addR 1 2 (evalMon v m) .c = .c := fun v hlin hquad => by
    have hPc := evalPoly_eq_c_of_hom' 1 2 v hpos hnbz hedge hlin hquad
    simpa [hPc] using habs v
  let v_base : ℕ → Elem6 := fun z =>
    if quadVert P z then (if col0 z then .a else .b)
    else if ({z} : Mon) ∈ P then .c else .zero
  have hlin_b : ∀ z, ({z} : Mon) ∈ P → addR 1 2 (v_base z) .c = .c := fun z hz => by
    dsimp only [v_base]; by_cases hqv : quadVert P z
    · rw [if_pos hqv]; cases col0 z <;> rfl
    · rw [if_neg hqv, if_pos hz]; rfl
  have hquad_b : ∀ a b, quadAdj P a b → mulM (v_base a) (v_base b) = .c := fun a b hab => by
    have hqa : quadVert P a := ⟨b, hab⟩
    have hqb : quadVert P b := ⟨a, quadAdj_symm hab⟩
    have hne := hcol0 a b hab
    dsimp only [v_base]; rw [if_pos hqa, if_pos hqb]
    cases ha : col0 a <;> cases hb : col0 b <;> rw [ha, hb] at hne <;> simp_all [mulM]
  rcases no_high_or_sq_of_hom hpos hnbz hedge hm_pos 1 2 v_base hlin_b hquad_b habs with hm1 | ⟨x, y, rfl, hxy⟩
  · obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp hm1
    left; by_contra hnot
    let col1 : ℕ → Bool := fun z => if col0 x then col0 z else !col0 z
    have hcol1 : ∀ a b, quadAdj P a b → col1 a ≠ col1 b := fun a b hab => by
      dsimp only [col1]; split_ifs
      · exact hcol0 a b hab
      · have hne := hcol0 a b hab; cases h1 : col0 a <;> cases h2 : col0 b <;> rw [h1, h2] at hne <;> simp_all
    have hcol1_x : col1 x = true := by dsimp only [col1]; cases col0 x <;> rfl
    let v : ℕ → Elem6 := fun z =>
      if z = x then (if quadVert P x then .p else .zero)
      else if quadVert P z then (if col1 z then .a else .b)
      else if ({z} : Mon) ∈ P then .c else .zero
    have hlin : ∀ z, ({z} : Mon) ∈ P → addR 1 2 (v z) .c = .c := fun z hz => by
      have hzx : z ≠ x := fun h => hnot (h ▸ hz)
      dsimp only [v]; rw [if_neg hzx]
      by_cases hqv : quadVert P z
      · rw [if_pos hqv]; cases col1 z <;> rfl
      · rw [if_neg hqv, if_pos hz]; rfl
    have hquad : ∀ a b, quadAdj P a b → mulM (v a) (v b) = .c := fun a b hab => by
      have hqa : quadVert P a := ⟨b, hab⟩
      have hqb : quadVert P b := ⟨a, quadAdj_symm hab⟩
      have hne := hcol1 a b hab
      by_cases hax : a = x
      · subst hax; have hbx : b ≠ a := hab.1.symm
        have hcb : col1 b = false := by rw [hcol1_x] at hne; cases h : col1 b <;> simp_all
        simp [v, hbx, hqa, hqb, hcb, mulM]
      · by_cases hbx : b = x
        · subst hbx
          have hca : col1 a = false := by rw [hcol1_x] at hne; cases h : col1 a <;> simp_all
          simp [v, hax, hqa, hqb, hca, mulM]
        · dsimp only [v]; rw [if_neg hax, if_neg hbx, if_pos hqa, if_pos hqb]
          cases h1 : col1 a <;> cases h2 : col1 b <;> rw [h1, h2] at hne <;> simp_all [mulM]
    have hmc := hvalid_col v hlin hquad
    rw [evalMon_singleton] at hmc
    dsimp only [v] at hmc; rw [if_pos rfl] at hmc
    by_cases hqx : quadVert P x
    · rw [if_pos hqx] at hmc; simp [addR, belowC] at hmc
    · rw [if_neg hqx] at hmc; simp [addR_zero_left] at hmc
  · by_cases hmem : ({x, y} : Mon) ∈ P
    · left; exact hmem
    · right
      have hqx : quadVert P x := by
        by_contra hnx
        have hmc := hvalid_col v_base hlin_b hquad_b
        rw [evalMon_pair] at hmc
        have hvx : v_base x = .c ∨ v_base x = .zero := by dsimp only [v_base]; rw [if_neg hnx]; split_ifs <;> simp
        rcases hvx with h | h <;> rw [h] at hmc <;> cases h2 : v_base y <;> rw [h2] at hmc <;> simp [mulM, addR_zero_left] at hmc
      have hqy : quadVert P y := by
        by_contra hny
        have hmc := hvalid_col v_base hlin_b hquad_b
        rw [evalMon_pair] at hmc
        have hvy : v_base y = .c ∨ v_base y = .zero := by dsimp only [v_base]; rw [if_neg hny]; split_ifs <;> simp
        rcases hvy with h | h <;> rw [h] at hmc <;> cases h2 : v_base x <;> rw [h2] at hmc <;> simp [mulM, addR_zero_left] at hmc
      have hwalk_xy : ∃ k, Walk P x y (2 * k + 1) := by
        by_contra hno_odd
        by_cases hsame : ∃ k, Walk P x y k
        · obtain ⟨k, hwk⟩ := hsame
          have hev : k % 2 = 0 := by
            rcases Nat.mod_two_eq_zero_or_one k with h0 | h1; exact h0
            exfalso; exact hno_odd ⟨k / 2, by rwa [show 2 * (k / 2) + 1 = k by omega]⟩
          have hcol_eq : col0 x = col0 y := (walk_col_parity hcol0 hwk).mpr hev
          have hmc := hvalid_col v_base hlin_b hquad_b
          rw [evalMon_pair] at hmc
          have : v_base x = v_base y := by simp [v_base, hqx, hqy, hcol_eq]
          rw [this, mulM_diag, addR_zero_left] at hmc; cases hmc
        · let flipY : ℕ → Bool := fun z => decide (∃ k, Walk P y z k)
          have hflY : ∀ a b, quadAdj P a b → flipY a = flipY b := fun a b hab => by
            dsimp only [flipY]; congr 1; apply propext
            exact ⟨fun ⟨k, h⟩ => ⟨k + 1, walk_trans h (Walk.step hab (Walk.zero b))⟩,
                   fun ⟨k, h⟩ => ⟨k + 1, walk_trans h (Walk.step (quadAdj_symm hab) (Walk.zero a))⟩⟩
          let col' : ℕ → Bool := fun z => if col0 x = col0 y then col0 z else xor (col0 z) (flipY z)
          have hcol' : ∀ a b, quadAdj P a b → col' a ≠ col' b := fun a b hab => by
            dsimp only [col']; split_ifs
            · exact hcol0 a b hab
            · exact col_flip_proper hcol0 hflY a b hab
          have hcol'_eq : col' x = col' y := by
            dsimp only [col']
            by_cases hxyc : col0 x = col0 y
            · simp [hxyc]
            · have hfx : flipY x = false := by
                simp only [flipY, decide_eq_false_iff_not]; rintro ⟨k, hk⟩; exact hsame ⟨k, walk_symm hk⟩
              have hfy : flipY y = true := by simp only [flipY, decide_eq_true_eq]; exact ⟨0, Walk.zero y⟩
              simp only [if_neg hxyc, hfx, hfy]
              cases h1 : col0 x <;> cases h2 : col0 y <;> simp_all
          let v' : ℕ → Elem6 := fun z =>
            if quadVert P z then (if col' z then .a else .b)
            else if ({z} : Mon) ∈ P then .c else .zero
          have hlin' : ∀ z, ({z} : Mon) ∈ P → addR 1 2 (v' z) .c = .c := fun z hz => by
            dsimp only [v']; by_cases hqv : quadVert P z
            · rw [if_pos hqv]; cases col' z <;> rfl
            · rw [if_neg hqv, if_pos hz]; rfl
          have hquad' : ∀ a b, quadAdj P a b → mulM (v' a) (v' b) = .c := fun a b hab => by
            have hqa : quadVert P a := ⟨b, hab⟩
            have hqb : quadVert P b := ⟨a, quadAdj_symm hab⟩
            have hne := hcol' a b hab
            dsimp only [v']; rw [if_pos hqa, if_pos hqb]
            exact mulM_ab_of_ne _ _ hne
          have hmc := hvalid_col v' hlin' hquad'
          rw [evalMon_pair] at hmc
          have : v' x = v' y := by simp [v', hqx, hqy, hcol'_eq]
          rw [this, mulM_diag, addR_zero_left] at hmc; cases hmc
      obtain ⟨k, hwk⟩ := hwalk_xy
      have hmust_mark : ∀ u w : ℕ, ({x, y} : Mon) = {u, w} → u ≠ w → ({u, w} : Mon) ∉ P →
          quadVert P u → quadVert P w → col0 u ≠ col0 w → marked P u := by
        intro u w hxy_uw huw hnotuw hqu hqw hne_uw
        by_contra hnu
        let col1 : ℕ → Bool := fun z => if col0 u then col0 z else !col0 z
        have hcol1 : ∀ a b, quadAdj P a b → col1 a ≠ col1 b := fun a b hab => by
          dsimp only [col1]; split_ifs
          · exact hcol0 a b hab
          · have hne := hcol0 a b hab; cases h1 : col0 a <;> cases h2 : col0 b <;> rw [h1, h2] at hne <;> simp_all
        have hcol1_u : col1 u = true := by dsimp only [col1]; cases col0 u <;> rfl
        have hcol1_w : col1 w = false := by
          dsimp only [col1]; cases h1 : col0 u <;> cases h2 : col0 w <;> rw [h1, h2] at hne_uw <;> simp_all
        let v : ℕ → Elem6 := fun z =>
          if z = u then .p
          else if z = w then .q
          else if quadVert P z then (if col1 z then .a else .b)
          else if ({z} : Mon) ∈ P then .c else .zero
        have hlin : ∀ z, ({z} : Mon) ∈ P → addR 1 2 (v z) .c = .c := fun z hz => by
          have hzu : z ≠ u := fun h => hnu ⟨h ▸ hz, hqu⟩
          dsimp only [v]; rw [if_neg hzu]
          by_cases hzw : z = w
          · rw [if_pos hzw]; rfl
          · rw [if_neg hzw]
            by_cases hqv : quadVert P z
            · rw [if_pos hqv]; cases col1 z <;> rfl
            · rw [if_neg hqv, if_pos hz]; rfl
        have hquad : ∀ a b, quadAdj P a b → mulM (v a) (v b) = .c := fun a b hab => by
          have hqa : quadVert P a := ⟨b, hab⟩
          have hqb : quadVert P b := ⟨a, quadAdj_symm hab⟩
          have hne := hcol1 a b hab
          by_cases hau : a = u
          · subst hau
            have hbw : b ≠ w := fun h => hnotuw (h ▸ hab.2)
            have hbu : b ≠ a := hab.1.symm
            have hcb : col1 b = false := bool_ne_true _ (hcol1_u ▸ hne)
            dsimp only [v]; rw [if_pos rfl, if_neg hbu, if_neg hbw, if_pos hqb, hcb]; rfl
          · by_cases hbu : b = u
            · subst hbu
              have haw : a ≠ w := fun h => hnotuw (by rw [Multiset.pair_comm]; exact h ▸ hab.2)
              have hca : col1 a = false := bool_ne_true _ (hcol1_u ▸ hne.symm)
              dsimp only [v]; rw [if_neg hau, if_neg haw, if_pos rfl, if_pos hqa, hca]; rfl
            · by_cases haw : a = w
              · subst haw; have hbw : b ≠ a := hab.1.symm
                have hcb : col1 b = true := bool_ne_false _ (hcol1_w ▸ hne)
                dsimp only [v]; rw [if_neg hau, if_pos rfl, if_neg hbu, if_neg hbw, if_pos hqb, hcb]; rfl
              · by_cases hbw : b = w
                · subst hbw
                  have hca : col1 a = true := bool_ne_false _ (hcol1_w ▸ hne.symm)
                  dsimp only [v]; rw [if_neg hau, if_neg haw, if_neg hbu, if_pos rfl, if_pos hqa, hca]; rfl
                · dsimp only [v]; rw [if_neg hau, if_neg haw, if_neg hbu, if_neg hbw, if_pos hqa, if_pos hqb]
                  exact mulM_ab_of_ne _ _ hne
        have hmc := hvalid_col v hlin hquad
        rw [hxy_uw, evalMon_pair] at hmc
        simp only [v, if_pos rfl, if_neg huw.symm, mulM] at hmc
        simp [addR_zero_left] at hmc
      have hcol_ne : col0 x ≠ col0 y := (walk_col_parity hcol0 hwk).not.mpr (by omega)
      exact ⟨x, y, k, rfl, hxy,
        hmust_mark x y rfl hxy hmem hqx hqy hcol_ne,
        hmust_mark y x (Multiset.pair_comm x y) hxy.symm (by rwa [Multiset.pair_comm]) hqy hqx hcol_ne.symm,
        hwk⟩

private lemma necessary_criteria {P : Poly} (hpos : ∀ m ∈ P, 1 ≤ m.card)
    (hnbz : ¬ IsBasicZero P) (hedge : ∃ a b, quadAdj P a b) {m : Mon} (hm_pos : 1 ≤ m.card) :
    ((∀ v, addR 0 1 (evalMon v m) (evalPoly 0 1 v P) = evalPoly 0 1 v P) →
      m ∈ P ∨
      (∃ w₁ w₂ k, marked P w₁ ∧ marked P w₂ ∧ Walk P w₁ w₂ (2 * k + 1)) ∨
      (∃ x y, m = {x, y} ∧ x ≠ y ∧ marked P x ∧ ∃ w k, marked P w ∧ Walk P w y (2 * k + 1))) ∧
    ((∀ v, addR 0 2 (evalMon v m) (evalPoly 0 2 v P) = evalPoly 0 2 v P) →
      m ∈ P ∨
      (∃ w₁ w₂ k, marked P w₁ ∧ marked P w₂ ∧ Walk P w₁ w₂ (2 * k + 1)) ∨
      (∃ x, m = {x} ∧ ∃ w k, marked P w ∧ Walk P w x (2 * k))) ∧
    ((∀ v, addR 1 1 (evalMon v m) (evalPoly 1 1 v P) = evalPoly 1 1 v P) →
      m ∈ P ∨
      (∃ x y k, m = {x, y} ∧ x ≠ y ∧ (marked P x ∨ marked P y) ∧ Walk P x y (2 * k + 1))) ∧
    ((∀ v, addR 1 2 (evalMon v m) (evalPoly 1 2 v P) = evalPoly 1 2 v P) →
      m ∈ P ∨
      (∃ x y k, m = {x, y} ∧ x ≠ y ∧ marked P x ∧ marked P y ∧ Walk P x y (2 * k + 1))) :=
  ⟨necessary_criteria_01 hpos hnbz hedge hm_pos,
   necessary_criteria_02 hpos hnbz hedge hm_pos,
   necessary_criteria_11 hpos hnbz hedge hm_pos,
   necessary_criteria_12 hpos hnbz hedge hm_pos⟩

/-! ### Section 6: Completeness of the Four Infinite Bases (Theorem 4.1) -/

/-- From `Σ₀`, any basic-zero polynomial `u` absorbs EVERY monomial `m`! -/
private lemma sigma0_derives_basicZero {Ax : Set (SemiringTerm × SemiringTerm)} (hSig : Sigma0 ⊆ Ax)
    {u : SemiringTerm} (hbz : IsBasicZero (toPoly u)) (m : SemiringTerm) :
    EqDerives Ax (.add m u) u := by
  have hsq_abs : ∀ a b : SemiringTerm, EqDerives Ax (.add a (.mul b b)) (.mul b b) := fun a b => by
    have h0 : EqDerives Ax (.add (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 1) (.var 1)) :=
      EqDerives.ax (hSig (Or.inl (Or.inl rfl)))
    simpa [SemiringTerm.subst] using
      EqDerives.subst (fun k => if k = 0 then a else b) h0
  have hcub_eq : ∀ a b c d : SemiringTerm,
      EqDerives Ax (.mul a a) (.mul (.mul b c) d) := fun a b c d => by
    have h0 : EqDerives Ax (.mul (.var 0) (.var 0)) (.mul (.mul (.var 1) (.var 2)) (.var 3)) :=
      EqDerives.ax (hSig (Or.inl (Or.inr rfl)))
    simpa [SemiringTerm.subst] using
      EqDerives.subst (fun k => match k with | 0 => a | 1 => b | 2 => c | _ => d) h0
  rcases hbz with ⟨mon, hmon, h3⟩ | ⟨x, hx⟩ | ⟨x, k, hwalk⟩
  · -- Degree `≥ 3` monomial `mon ∈ (toPoly u)`: `mon = {a, b, c} + rest`, and `termOfMon mon` absorbs `m`!
    have hex_cons : ∀ s : Mon, s ≠ 0 → ∃ a s', s = a ::ₘ s' := fun s hs =>
      let ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hs
      ⟨a, s.erase a, (Multiset.cons_erase ha).symm⟩
    obtain ⟨a, m1, rfl⟩ := hex_cons mon (by intro h; simp [h] at h3)
    obtain ⟨b, m2, rfl⟩ := hex_cons m1 (by intro h; simp [h] at h3)
    obtain ⟨c, m3, rfl⟩ := hex_cons m2 (by intro h; simp [h] at h3)
    let t3 : SemiringTerm := .mul (.mul (.var a) (.var b)) (.var c)
    let rhs : SemiringTerm := if h : m3 = 0 then t3 else .mul t3 (termOfMon m3)
    have hrhs_poly : (toPoly rhs) = {a ::ₘ b ::ₘ c ::ₘ m3} := by
      by_cases hm3 : m3 = 0
      · subst hm3; simp [rhs, t3, toPoly, mulPoly]
      · have hpos3 : 1 ≤ m3.card := Nat.pos_of_ne_zero (Multiset.card_eq_zero.not.mpr hm3)
        simp only [rhs, dif_neg hm3, t3, toPoly, toPoly_termOfMon hpos3]
        ext z; simp [mulPoly]
    have hsub : (toPoly rhs) ⊆ (toPoly u) := by rw [hrhs_poly, Finset.singleton_subset_iff]; exact hmon
    -- Show `m ⪯ rhs`: either `rhs = t3 ≈ a^2` (directly by `hsq_abs`), or `rhs = t3 * w ≈ (a^2)*w = a*a*w ≈ a^2`!
    have hm_rhs : EqDerives Ax (.add m rhs) rhs := by
      by_cases hm3 : m3 = 0
      · simp only [rhs, dif_pos hm3]
        have heq : EqDerives Ax (.mul (.var 0) (.var 0)) t3 := hcub_eq (.var 0) (.var a) (.var b) (.var c)
        exact EqDerives.trans (EqDerives.add_cong (EqDerives.refl m) (EqDerives.symm heq))
          (EqDerives.trans (hsq_abs m (.var 0)) heq)
      · simp only [rhs, dif_neg hm3]
        have h1 : EqDerives Ax (.mul (.var 0) (.var 0)) (.mul (.mul (.var a) (.var b)) (.mul (.var c) (termOfMon m3))) :=
          hcub_eq (.var 0) (.var a) (.var b) (.mul (.var c) (termOfMon m3))
        have h2 : EqDerives Ax (.mul (.mul (.var a) (.var b)) (.mul (.var c) (termOfMon m3))) (.mul t3 (termOfMon m3)) :=
          EqDerives.symm (EqDerives.mul_assoc (.mul (.var a) (.var b)) (.var c) (termOfMon m3))
        have heq := EqDerives.trans h1 h2
        exact EqDerives.trans (EqDerives.add_cong (EqDerives.refl m) (EqDerives.symm heq))
          (EqDerives.trans (hsq_abs m (.var 0)) heq)
    exact eqDerives_abs_context Ax hm_rhs hsub
  · -- Square `{x, x} ∈ (toPoly u)`: directly apply `hsq_abs m (.var x)`!
    have hsub : (toPoly (SemiringTerm.mul (.var x) (.var x))) ⊆ (toPoly u) := by
      simpa [toPoly, mulPoly] using hx
    exact eqDerives_abs_context Ax (hsq_abs m (.var x)) hsub
  · -- Odd closed walk `Walk (toPoly u) x x (2 * k + 1)`: instantiate `σ_k` (`k ≥ 1`, since `quadAdj` has no self-loops so `k = 0` is impossible!)
    have hk1 : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      subst hk0
      simp only [Nat.mul_zero, Nat.zero_add] at hwalk
      cases hwalk with
      | @step _ y _ _ hxy hy =>
        cases hy; exact hxy.1 rfl
    -- Extract vertices `f : ℕ → ℕ` along `hwalk` with `f 0 = x`, `f (2*k + 1) = x`, and `{f r, f (r + 1)} ∈ (toPoly u)`!
    have hex_seq : ∀ {a b len : ℕ}, Walk (toPoly u) a b len →
        ∃ f : ℕ → ℕ, f 0 = a ∧ f len = b ∧ ∀ r < len, ({f r, f (r + 1)} : Mon) ∈ (toPoly u) := by
      intro a b len hw
      induction hw with
      | zero a => exact ⟨fun _ => a, rfl, rfl, fun r hr => absurd hr (Nat.not_lt_zero r)⟩
      | @step a b c len hab _ ih =>
        obtain ⟨f, hf0, hfl, hf⟩ := ih
        refine ⟨fun r => match r with | 0 => a | r + 1 => f r, rfl, hfl, fun r hr => ?_⟩
        cases r with
        | zero => simpa [hf0] using hab.2
        | succ r => exact hf r (by omega)
    obtain ⟨f, hf0, hfl, hf⟩ := hex_seq hwalk
    let σ : ℕ → SemiringTerm := fun i => if i = 2 * k + 1 then m else .var (f i)
    have hax : EqDerives Ax (.add (.var (2 * k + 1)) (oddCycleTerm k)) (oddCycleTerm k) :=
      EqDerives.ax (hSig (Or.inr ⟨k, hk1, rfl⟩))
    have hinst := EqDerives.subst σ hax
    have hsub : (toPoly ((oddCycleTerm k).subst σ)) ⊆ (toPoly u) := by
      have hpath_sub : ∀ r < 2 * k, (toPoly ((pathTerm r).subst σ)) ⊆ (toPoly u) := by
        intro r; induction r with
        | zero =>
          intro hr
          simp only [pathTerm, SemiringTerm.subst, σ, show (0 : ℕ) ≠ 2 * k + 1 by omega,
            show (1 : ℕ) ≠ 2 * k + 1 by omega, ↓reduceIte, toPoly, mulPoly]
          simpa using hf 0 (by omega)
        | succ r ih =>
          intro hr
          simp only [pathTerm, SemiringTerm.subst, toPoly, Finset.union_subset_iff]
          refine ⟨ih (by omega), ?_⟩
          simp only [σ, show r + 1 ≠ 2 * k + 1 by omega, show r + 2 ≠ 2 * k + 1 by omega, ↓reduceIte,
            toPoly, mulPoly]
          simpa using hf (r + 1) (by omega)
      simp only [oddCycleTerm, SemiringTerm.subst, toPoly, Finset.union_subset_iff]
      refine ⟨hpath_sub (2 * k - 1) (by omega), ?_⟩
      simp only [σ, show 2 * k ≠ 2 * k + 1 by omega, show (0 : ℕ) ≠ 2 * k + 1 by omega, ↓reduceIte,
        toPoly, mulPoly]
      have hlast := hf (2 * k) (by omega)
      rw [hfl, ← hf0] at hlast
      simpa using hlast
    have hσm : (SemiringTerm.var (2 * k + 1)).subst σ = m := by simp [SemiringTerm.subst, σ]
    rw [SemiringTerm.subst, hσm] at hinst
    exact eqDerives_abs_context Ax hinst hsub

/-- From `idAlpha`, any odd walk `Walk (toPoly u) x y (2 * k + 1)` with `{x} ∈ (toPoly u)` derives `x * y ⪯ u`! -/
private lemma alpha_derives_oddWalk {Ax : Set (SemiringTerm × SemiringTerm)} (hα : idAlpha ∈ Ax)
    {u : SemiringTerm} {x y k : ℕ} (hx : ({x} : Mon) ∈ (toPoly u)) (hw : Walk (toPoly u) x y (2 * k + 1)) :
    EqDerives Ax (.add (.mul (.var x) (.var y)) u) u := by
  induction k generalizing y with
  | zero =>
    cases hw with
    | @step _ y' _ _ hxy' hy' =>
      cases hy'
      exact eqDerives_abs_of_subset Ax (by simpa [toPoly, mulPoly] using hxy'.2)
  | succ k ih =>
    -- Split the walk of length `2k + 3` into a prefix of length `2k + 1` to `a`, followed by `a - b - y`!
    have hsplit : ∀ {n : ℕ} {a c : ℕ}, Walk (toPoly u) a c (n + 2) →
        ∃ d e, Walk (toPoly u) a d n ∧ quadAdj (toPoly u) d e ∧ quadAdj (toPoly u) e c := by
      intro n a c h
      induction n generalizing a with
      | zero =>
        cases h with
        | @step _ e _ _ hae hec =>
          cases hec with
          | @step _ c' _ _ hec' hc' =>
            cases hc'; exact ⟨a, e, Walk.zero a, hae, hec'⟩
      | succ n ihn =>
        cases h with
        | @step _ b _ _ hab hbc =>
          obtain ⟨d, e, hbd, hde, hec⟩ := ihn hbc
          exact ⟨d, e, Walk.step hab hbd, hde, hec⟩
    obtain ⟨a, b, hxa, hab, hby⟩ := hsplit hw
    have hxa_abs : EqDerives Ax (.add (.mul (.var x) (.var a)) u) u := ih hxa
    -- Apply `idAlpha` on `x - a - b - y` with `x` marked, using `x*a + u` as context!
    let σ : ℕ → SemiringTerm := fun i => match i with | 0 => .var x | 1 => .var a | 2 => .var b | _ => .var y
    have hinst := EqDerives.subst σ (EqDerives.ax hα)
    have hsub : (toPoly ((SemiringTerm.add (.var 0) (pathTerm 2)).subst σ)) ⊆
        (toPoly (SemiringTerm.add (.mul (.var x) (.var a)) u)) := by
      simp only [pathTerm, SemiringTerm.subst, σ, toPoly, Finset.union_subset_iff]
      refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
      · intro m hm; exact Finset.mem_union_right _ ((Finset.mem_singleton.mp hm) ▸ hx)
      · intro m hm; exact Finset.mem_union_left _ hm
      · intro m hm; exact Finset.mem_union_right _ ((by simpa [mulPoly] using hm : m = {a, b}) ▸ hab.2)
      · intro m hm; exact Finset.mem_union_right _ ((by simpa [mulPoly] using hm : m = {b, y}) ▸ hby.2)
    have hstep : EqDerives Ax (.add (.mul (.var x) (.var y)) (.add (.mul (.var x) (.var a)) u))
        (.add (.mul (.var x) (.var a)) u) :=
      eqDerives_abs_context Ax hinst hsub
    exact eqDerives_abs_cut Ax hstep hxa_abs

/-- From `idEta`, any even walk `Walk (toPoly u) x y (2 * k)` with `{x} ∈ (toPoly u)` derives `y ⪯ u`! -/
private lemma eta_derives_evenWalk {Ax : Set (SemiringTerm × SemiringTerm)} (hη : idEta ∈ Ax)
    {u : SemiringTerm} {x y k : ℕ} (hx : ({x} : Mon) ∈ (toPoly u)) (hw : Walk (toPoly u) x y (2 * k)) :
    EqDerives Ax (.add (.var y) u) u := by
  induction k generalizing y with
  | zero =>
    cases hw
    exact eqDerives_abs_of_subset Ax (by simpa [toPoly] using hx)
  | succ k ih =>
    have hsplit : ∀ {n : ℕ} {a c : ℕ}, Walk (toPoly u) a c (n + 2) →
        ∃ d e, Walk (toPoly u) a d n ∧ quadAdj (toPoly u) d e ∧ quadAdj (toPoly u) e c := by
      intro n a c h
      induction n generalizing a with
      | zero =>
        cases h with
        | @step _ e _ _ hae hec =>
          cases hec with
          | @step _ c' _ _ hec' hc' =>
            cases hc'; exact ⟨a, e, Walk.zero a, hae, hec'⟩
      | succ n ihn =>
        cases h with
        | @step _ b _ _ hab hbc =>
          obtain ⟨d, e, hbd, hde, hec⟩ := ihn hbc
          exact ⟨d, e, Walk.step hab hbd, hde, hec⟩
    obtain ⟨a, b, hxa, hab, hby⟩ := hsplit hw
    have ha_abs : EqDerives Ax (.add (.var a) u) u := ih hxa
    let σ : ℕ → SemiringTerm := fun i => match i with | 0 => .var a | 1 => .var b | _ => .var y
    have hinst := EqDerives.subst σ (EqDerives.ax hη)
    have hsub : (toPoly ((SemiringTerm.add (.var 0) (pathTerm 1)).subst σ)) ⊆
        (toPoly (SemiringTerm.add (.var a) u)) := by
      simp only [pathTerm, SemiringTerm.subst, σ, toPoly, Finset.union_subset_iff]
      refine ⟨?_, ?_, ?_⟩
      · intro m hm; exact Finset.mem_union_left _ hm
      · intro m hm; exact Finset.mem_union_right _ ((by simpa [mulPoly] using hm : m = {a, b}) ▸ hab.2)
      · intro m hm; exact Finset.mem_union_right _ ((by simpa [mulPoly] using hm : m = {b, y}) ▸ hby.2)
    have hstep : EqDerives Ax (.add (.var y) (.add (.var a) u)) (.add (.var a) u) :=
      eqDerives_abs_context Ax hinst hsub
    exact eqDerives_abs_cut Ax hstep ha_abs

/-- From `Sigma0 ∪ {idXi}`, a double-marked edge `x + y + xy ⊆ u` makes `u` absorb any term `m`! -/
private lemma xi_derives_of_doubleMarked {Ax : Set (SemiringTerm × SemiringTerm)}
    (hSig : Sigma0 ⊆ Ax) (hξ : idXi ∈ Ax) {u : SemiringTerm} {x y : ℕ}
    (hx : ({x} : Mon) ∈ (toPoly u)) (hy : ({y} : Mon) ∈ (toPoly u)) (hxy : ({x, y} : Mon) ∈ (toPoly u))
    (m : SemiringTerm) : EqDerives Ax (.add m u) u := by
  let σ : ℕ → SemiringTerm := fun i => if i = 0 then .var x else .var y
  have hD_eq : EqDerives Ax (.mul (.var x) (.var x)) (.add (.add (.var x) (.var y)) (.mul (.var x) (.var y))) :=
    EqDerives.subst σ (EqDerives.ax hξ)
  have hsq : EqDerives Ax (.add m (.mul (.var x) (.var x))) (.mul (.var x) (.var x)) := by
    have h0 : EqDerives Ax (.add (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 1) (.var 1)) :=
      EqDerives.ax (hSig (Or.inl (Or.inl rfl)))
    simpa [SemiringTerm.subst] using EqDerives.subst (fun k => if k = 0 then m else .var x) h0
  have hD_abs : EqDerives Ax (.add m (.add (.add (.var x) (.var y)) (.mul (.var x) (.var y))))
      (.add (.add (.var x) (.var y)) (.mul (.var x) (.var y))) :=
    EqDerives.trans (EqDerives.add_cong (EqDerives.refl m) (EqDerives.symm hD_eq))
      (EqDerives.trans hsq hD_eq)
  have hsub : (toPoly (SemiringTerm.add (.add (.var x) (.var y)) (.mul (.var x) (.var y)))) ⊆ (toPoly u) := by
    simp only [toPoly, Finset.union_subset_iff]
    exact ⟨⟨by simpa using hx, by simpa using hy⟩, by simpa [mulPoly] using hxy⟩
  exact eqDerives_abs_context Ax hD_abs hsub

/-- Completeness of all four infinite bases `basis01`, `basis02`, `basis11`, `basis12` (Theorem 4.1). -/
private lemma basis01_complete : ∀ s t : SemiringTerm, SatisfiesId 0 1 s t → EqDerives basis01 s t := by
  have hAbs : ∀ s t : SemiringTerm, (∀ v, addR 0 1 (s.eval 0 1 v) (t.eval 0 1 v) = t.eval 0 1 v) →
      EqDerives basis01 (.add s t) t := by
    intro s t hst
    refine eqDerives_abs_of_monomials basis01 fun m hm => ?_
    have hm_pos : 1 ≤ m.card := toPoly_card_pos s hm
    have hm_abs : ∀ v, addR 0 1 (evalMon v m) (evalPoly 0 1 v (toPoly t)) = evalPoly 0 1 v (toPoly t) := fun v => by
      have h1 := hst v
      rw [eval_eq_evalPoly, eval_eq_evalPoly] at h1
      have h2 := leR_of_mem_evalPoly 0 1 v hm
      calc addR 0 1 (evalMon v m) (evalPoly 0 1 v (toPoly t))
          = addR 0 1 (evalMon v m) (addR 0 1 (evalPoly 0 1 v (toPoly s)) (evalPoly 0 1 v (toPoly t))) := by rw [h1]
        _ = addR 0 1 (addR 0 1 (evalMon v m) (evalPoly 0 1 v (toPoly s))) (evalPoly 0 1 v (toPoly t)) := (addR_assoc' ..).symm
        _ = addR 0 1 (evalPoly 0 1 v (toPoly s)) (evalPoly 0 1 v (toPoly t)) := by rw [h2]
        _ = evalPoly 0 1 v (toPoly t) := h1
    by_cases hbz : IsBasicZero (toPoly t)
    · exact sigma0_derives_basicZero (fun _ h => Or.inl h) hbz (termOfMon m)
    · by_cases hedge : ∃ a b, quadAdj (toPoly t) a b
      · rcases (necessary_criteria (fun _ h => toPoly_card_pos t h) hbz hedge hm_pos).1 hm_abs with
          hmem | ⟨w₁, w₂, k, hm1, hm2, hwalk⟩ | ⟨x, y, rfl, hxy, hmx, w, k, hmw, hwalk⟩
        · exact eqDerives_abs_of_subset basis01 (by rw [toPoly_termOfMon hm_pos, Finset.singleton_subset_iff]; exact hmem)
        · -- Odd walk between marks `w₁` and `w₂`: `alpha` gives `w₁*w₂ ⪯ t`, then `xi` on `w₁ + w₂ + w₁*w₂` kills `t`!
          have h1 : EqDerives basis01 (.add (.mul (.var w₁) (.var w₂)) t) t :=
            alpha_derives_oddWalk (Or.inr (Or.inr (Or.inl rfl))) hm1.1 hwalk
          have hmw12 : ({w₁, w₂} : Mon) ∈ toPoly (.add (.mul (.var w₁) (.var w₂)) t) :=
            Finset.mem_union_left _ (mem_mulPoly.mpr ⟨{w₁}, Finset.mem_singleton_self _, {w₂}, Finset.mem_singleton_self _, Multiset.singleton_add w₁ {w₂}⟩)
          have h2 : EqDerives basis01 (.add (termOfMon m) (.add (.mul (.var w₁) (.var w₂)) t))
              (.add (.mul (.var w₁) (.var w₂)) t) :=
            xi_derives_of_doubleMarked (Ax := basis01) (fun _ h => Or.inl h) (Or.inr (Or.inl rfl))
              (Finset.mem_union_right _ hm1.1) (Finset.mem_union_right _ hm2.1) hmw12 (termOfMon m)
          exact eqDerives_abs_cut basis01 h2 h1
        · -- `m = {x, y}`, `x` marked, odd walk from mark `w` to `y`: `alpha` gives `w*y ⪯ t`, then `beta` gives `x*y ⪯ t`!
          have hwy : EqDerives basis01 (.add (.mul (.var w) (.var y)) t) t :=
            alpha_derives_oddWalk (Or.inr (Or.inr (Or.inl rfl))) hmw.1 hwalk
          obtain ⟨z, hxz⟩ := hmx.2
          let σ : ℕ → SemiringTerm := fun i => match i with | 0 => .var x | 1 => .var z | 2 => .var y | _ => .var w
          have hinst := EqDerives.subst σ
            (EqDerives.ax (show (idBeta.1, idBeta.2) ∈ basis01 from Or.inr (Or.inr (Or.inr rfl))))
          have hsub : (toPoly ((SemiringTerm.add (.add (.var 0) (.mul (.var 0) (.var 1)))
              (.add (.var 3) (.mul (.var 3) (.var 2)))).subst σ)) ⊆
              (toPoly (SemiringTerm.add (.mul (.var w) (.var y)) t)) := by
            simp only [SemiringTerm.subst, σ, toPoly, Finset.union_subset_iff]
            exact ⟨⟨fun _ h => Finset.mem_union_right _ ((Finset.mem_singleton.mp h) ▸ hmx.1),
                    fun _ h => Finset.mem_union_right _ ((by simpa [mulPoly] using h : _ = ({x, z} : Mon)) ▸ hxz.2)⟩,
                   ⟨fun _ h => Finset.mem_union_right _ ((Finset.mem_singleton.mp h) ▸ hmw.1),
                    fun _ h => Finset.mem_union_left _ h⟩⟩
          have hstep := eqDerives_abs_context basis01 hinst hsub
          have hxy_t := eqDerives_abs_cut basis01 hstep hwy
          have heq_m : EqDerives basis01 (termOfMon ({x, y} : Mon)) (.mul (.var x) (.var y)) :=
            eqDerives_of_toPoly_eq basis01 (by rw [toPoly_termOfMon (by simp)]; simp [toPoly, mulPoly])
          exact EqDerives.trans (EqDerives.add_cong heq_m (EqDerives.refl t)) hxy_t
      · push Not at hedge
        have hmem := linear_poly_abs_only_mem 0 1 (toPoly_nonempty t) (fun _ h => toPoly_card_pos t h) hbz hedge hm_pos hm_abs
        exact eqDerives_abs_of_subset basis01 (by rw [toPoly_termOfMon hm_pos, Finset.singleton_subset_iff]; exact hmem)
  intro s t hst
  exact eqDerives_of_abs_both basis01
    (hAbs s t fun v => by rw [hst v, addR_idem'])
    (hAbs t s fun v => by rw [hst v, addR_idem'])

private lemma basis02_complete : ∀ s t : SemiringTerm, SatisfiesId 0 2 s t → EqDerives basis02 s t := by
  have hAbs : ∀ s t : SemiringTerm, (∀ v, addR 0 2 (s.eval 0 2 v) (t.eval 0 2 v) = t.eval 0 2 v) →
      EqDerives basis02 (.add s t) t := by
    intro s t hst
    refine eqDerives_abs_of_monomials basis02 fun m hm => ?_
    have hm_pos : 1 ≤ m.card := toPoly_card_pos s hm
    have hm_abs : ∀ v, addR 0 2 (evalMon v m) (evalPoly 0 2 v (toPoly t)) = evalPoly 0 2 v (toPoly t) := fun v => by
      have h1 := hst v; rw [eval_eq_evalPoly, eval_eq_evalPoly] at h1
      have h2 := leR_of_mem_evalPoly 0 2 v hm
      calc addR 0 2 (evalMon v m) (evalPoly 0 2 v (toPoly t))
          = addR 0 2 (evalMon v m) (addR 0 2 (evalPoly 0 2 v (toPoly s)) (evalPoly 0 2 v (toPoly t))) := by rw [h1]
        _ = addR 0 2 (addR 0 2 (evalMon v m) (evalPoly 0 2 v (toPoly s))) (evalPoly 0 2 v (toPoly t)) := (addR_assoc' ..).symm
        _ = addR 0 2 (evalPoly 0 2 v (toPoly s)) (evalPoly 0 2 v (toPoly t)) := by rw [h2]
        _ = evalPoly 0 2 v (toPoly t) := h1
    by_cases hbz : IsBasicZero (toPoly t)
    · exact sigma0_derives_basicZero (fun _ h => Or.inl h) hbz (termOfMon m)
    · by_cases hedge : ∃ a b, quadAdj (toPoly t) a b
      · rcases (necessary_criteria (fun _ h => toPoly_card_pos t h) hbz hedge hm_pos).2.1 hm_abs with
          hmem | ⟨w₁, w₂, k, hm1, hm2, hwalk⟩ | ⟨x, rfl, w, k, hmw, hwalk⟩
        · exact eqDerives_abs_of_subset basis02 (by rw [toPoly_termOfMon hm_pos, Finset.singleton_subset_iff]; exact hmem)
        · -- Odd walk `w₁ -> ... -> z - w₂`: `eta` marks `z` (even distance from `w₁`), then `xi` on `z + w₂ + z*w₂` kills `t`!
          have hsplit1 : ∀ {n : ℕ} {a c : ℕ}, Walk (toPoly t) a c (n + 1) →
              ∃ z, Walk (toPoly t) a z n ∧ quadAdj (toPoly t) z c := by
            intro n a c h
            induction n generalizing a with
            | zero => cases h with | @step _ c' _ _ hac hc => cases hc; exact ⟨a, Walk.zero a, hac⟩
            | succ n ihn =>
              cases h with | @step _ b _ _ hab hbc =>
                obtain ⟨z, hbz, hzc⟩ := ihn hbc
                exact ⟨z, Walk.step hab hbz, hzc⟩
          obtain ⟨z, hw1z, hzw2⟩ := hsplit1 hwalk
          have hz_t : EqDerives basis02 (.add (.var z) t) t :=
            eta_derives_evenWalk (Or.inr (Or.inr rfl)) hm1.1 hw1z
          have h2 : EqDerives basis02 (.add (termOfMon m) (.add (.var z) t)) (.add (.var z) t) :=
            xi_derives_of_doubleMarked (Ax := basis02) (fun _ h => Or.inl h) (Or.inr (Or.inl rfl))
              (Finset.mem_union_left _ (Finset.mem_singleton_self {z}))
              (Finset.mem_union_right _ hm2.1)
              (Finset.mem_union_right _ hzw2.2) (termOfMon m)
          exact eqDerives_abs_cut basis02 h2 hz_t
        · have hx_t : EqDerives basis02 (.add (.var x) t) t :=
            eta_derives_evenWalk (Or.inr (Or.inr rfl)) hmw.1 hwalk
          have heq_m : EqDerives basis02 (termOfMon ({x} : Mon)) (.var x) :=
            eqDerives_of_toPoly_eq basis02 (by rw [toPoly_termOfMon (by simp)]; rfl)
          exact EqDerives.trans (EqDerives.add_cong heq_m (EqDerives.refl t)) hx_t
      · push Not at hedge
        have hmem := linear_poly_abs_only_mem 0 2 (toPoly_nonempty t) (fun _ h => toPoly_card_pos t h) hbz hedge hm_pos hm_abs
        exact eqDerives_abs_of_subset basis02 (by rw [toPoly_termOfMon hm_pos, Finset.singleton_subset_iff]; exact hmem)
  intro s t hst
  exact eqDerives_of_abs_both basis02
    (hAbs s t fun v => by rw [hst v, addR_idem'])
    (hAbs t s fun v => by rw [hst v, addR_idem'])

private lemma basis11_complete : ∀ s t : SemiringTerm, SatisfiesId 1 1 s t → EqDerives basis11 s t := by
  have hAbs : ∀ s t : SemiringTerm, (∀ v, addR 1 1 (s.eval 1 1 v) (t.eval 1 1 v) = t.eval 1 1 v) →
      EqDerives basis11 (.add s t) t := by
    intro s t hst
    refine eqDerives_abs_of_monomials basis11 fun m hm => ?_
    have hm_pos : 1 ≤ m.card := toPoly_card_pos s hm
    have hm_abs : ∀ v, addR 1 1 (evalMon v m) (evalPoly 1 1 v (toPoly t)) = evalPoly 1 1 v (toPoly t) := fun v => by
      have h1 := hst v; rw [eval_eq_evalPoly, eval_eq_evalPoly] at h1
      have h2 := leR_of_mem_evalPoly 1 1 v hm
      calc addR 1 1 (evalMon v m) (evalPoly 1 1 v (toPoly t))
          = addR 1 1 (evalMon v m) (addR 1 1 (evalPoly 1 1 v (toPoly s)) (evalPoly 1 1 v (toPoly t))) := by rw [h1]
        _ = addR 1 1 (addR 1 1 (evalMon v m) (evalPoly 1 1 v (toPoly s))) (evalPoly 1 1 v (toPoly t)) := (addR_assoc' ..).symm
        _ = addR 1 1 (evalPoly 1 1 v (toPoly s)) (evalPoly 1 1 v (toPoly t)) := by rw [h2]
        _ = evalPoly 1 1 v (toPoly t) := h1
    by_cases hbz : IsBasicZero (toPoly t)
    · exact sigma0_derives_basicZero (fun _ h => Or.inl h) hbz (termOfMon m)
    · by_cases hedge : ∃ a b, quadAdj (toPoly t) a b
      · rcases (necessary_criteria (fun _ h => toPoly_card_pos t h) hbz hedge hm_pos).2.2.1 hm_abs with
          hmem | ⟨x, y, k, rfl, _, hmk, hwalk⟩
        · exact eqDerives_abs_of_subset basis11 (by rw [toPoly_termOfMon hm_pos, Finset.singleton_subset_iff]; exact hmem)
        · have heq_m : EqDerives basis11 (termOfMon ({x, y} : Mon)) (.mul (.var x) (.var y)) :=
            eqDerives_of_toPoly_eq basis11 (by rw [toPoly_termOfMon (by simp)]; simp [toPoly, mulPoly])
          rcases hmk with hmx | hmy
          · exact EqDerives.trans (EqDerives.add_cong heq_m (EqDerives.refl t))
              (alpha_derives_oddWalk (Or.inr rfl) hmx.1 hwalk)
          · have heq_m' : EqDerives basis11 (termOfMon ({x, y} : Mon)) (.mul (.var y) (.var x)) :=
              EqDerives.trans heq_m (EqDerives.mul_comm _ _)
            exact EqDerives.trans (EqDerives.add_cong heq_m' (EqDerives.refl t))
              (alpha_derives_oddWalk (Or.inr rfl) hmy.1 (walk_symm hwalk))
      · push Not at hedge
        have hmem := linear_poly_abs_only_mem 1 1 (toPoly_nonempty t) (fun _ h => toPoly_card_pos t h) hbz hedge hm_pos hm_abs
        exact eqDerives_abs_of_subset basis11 (by rw [toPoly_termOfMon hm_pos, Finset.singleton_subset_iff]; exact hmem)
  intro s t hst
  exact eqDerives_of_abs_both basis11
    (hAbs s t fun v => by rw [hst v, addR_idem'])
    (hAbs t s fun v => by rw [hst v, addR_idem'])

private lemma basis12_complete : ∀ s t : SemiringTerm, SatisfiesId 1 2 s t → EqDerives basis12 s t := by
  have hAbs : ∀ s t : SemiringTerm, (∀ v, addR 1 2 (s.eval 1 2 v) (t.eval 1 2 v) = t.eval 1 2 v) →
      EqDerives basis12 (.add s t) t := by
    intro s t hst
    refine eqDerives_abs_of_monomials basis12 fun m hm => ?_
    have hm_pos : 1 ≤ m.card := toPoly_card_pos s hm
    have hm_abs : ∀ v, addR 1 2 (evalMon v m) (evalPoly 1 2 v (toPoly t)) = evalPoly 1 2 v (toPoly t) := fun v => by
      have h1 := hst v; rw [eval_eq_evalPoly, eval_eq_evalPoly] at h1
      have h2 := leR_of_mem_evalPoly 1 2 v hm
      calc addR 1 2 (evalMon v m) (evalPoly 1 2 v (toPoly t))
          = addR 1 2 (evalMon v m) (addR 1 2 (evalPoly 1 2 v (toPoly s)) (evalPoly 1 2 v (toPoly t))) := by rw [h1]
        _ = addR 1 2 (addR 1 2 (evalMon v m) (evalPoly 1 2 v (toPoly s))) (evalPoly 1 2 v (toPoly t)) := (addR_assoc' ..).symm
        _ = addR 1 2 (evalPoly 1 2 v (toPoly s)) (evalPoly 1 2 v (toPoly t)) := by rw [h2]
        _ = evalPoly 1 2 v (toPoly t) := h1
    by_cases hbz : IsBasicZero (toPoly t)
    · exact sigma0_derives_basicZero (fun _ h => Or.inl h) hbz (termOfMon m)
    · by_cases hedge : ∃ a b, quadAdj (toPoly t) a b
      · rcases (necessary_criteria (fun _ h => toPoly_card_pos t h) hbz hedge hm_pos).2.2.2 hm_abs with
          hmem | ⟨x, y, k, rfl, _, hmx, hmy, hwalk⟩
        · exact eqDerives_abs_of_subset basis12 (by rw [toPoly_termOfMon hm_pos, Finset.singleton_subset_iff]; exact hmem)
        · cases k with
          | zero =>
            cases hwalk with
            | @step _ y' _ _ hxy' hy' =>
              cases hy'
              exact eqDerives_abs_of_subset basis12
                (by rw [toPoly_termOfMon (by simp), Finset.singleton_subset_iff]; exact hxy'.2)
          | succ k =>
            let n := k + 1
            have hex_seq : ∀ {a b len : ℕ}, Walk (toPoly t) a b len →
                ∃ f : ℕ → ℕ, f 0 = a ∧ f len = b ∧ ∀ r < len, ({f r, f (r + 1)} : Mon) ∈ (toPoly t) := by
              intro a b len hw
              induction hw with
              | zero a => exact ⟨fun _ => a, rfl, rfl, fun r hr => absurd hr (Nat.not_lt_zero r)⟩
              | @step a b c len hab _ ih =>
                obtain ⟨f, hf0, hfl, hf⟩ := ih
                refine ⟨fun r => match r with | 0 => a | r + 1 => f r, rfl, hfl, fun r hr => ?_⟩
                cases r with
                | zero => simpa [hf0] using hab.2
                | succ r => exact hf r (by omega)
            obtain ⟨f, hf0, hfl, hf⟩ := hex_seq hwalk
            let σ : ℕ → SemiringTerm := fun i => .var (f i)
            have hinst := EqDerives.subst σ
              (EqDerives.ax (show ((idTheta n).1, (idTheta n).2) ∈ basis12 from Or.inr ⟨n, by omega, rfl⟩))
            have hsub : (toPoly ((SemiringTerm.add (.add (.var 0) (.var (2 * n + 1))) (pathTerm (2 * n))).subst σ)) ⊆ (toPoly t) := by
              have hpath_sub : ∀ r ≤ 2 * n, (toPoly ((pathTerm r).subst σ)) ⊆ (toPoly t) := by
                intro r; induction r with
                | zero =>
                  intro _; simp only [pathTerm, SemiringTerm.subst, σ, toPoly, mulPoly]
                  simpa using hf 0 (by omega)
                | succ r ih =>
                  intro hr
                  simp only [pathTerm, SemiringTerm.subst, toPoly, Finset.union_subset_iff]
                  refine ⟨ih (by omega), ?_⟩
                  simp only [σ, toPoly, mulPoly]
                  simpa using hf (r + 1) (by omega)
              simp only [SemiringTerm.subst, toPoly, Finset.union_subset_iff]
              exact ⟨⟨Finset.singleton_subset_iff.mpr (by simpa [σ, hf0] using hmx.1),
                      Finset.singleton_subset_iff.mpr (by rw [hfl]; exact hmy.1)⟩, hpath_sub (2 * n) le_rfl⟩
            have hstep := eqDerives_abs_context basis12 hinst hsub
            simp only [SemiringTerm.subst, σ, hf0] at hstep
            rw [hfl] at hstep
            have heq_m : EqDerives basis12 (termOfMon ({x, y} : Mon)) (.mul (.var x) (.var y)) :=
              eqDerives_of_toPoly_eq basis12 (by rw [toPoly_termOfMon (by simp)]; simp [toPoly, mulPoly])
            exact EqDerives.trans (EqDerives.add_cong heq_m (EqDerives.refl t)) hstep
      · push Not at hedge
        have hmem := linear_poly_abs_only_mem 1 2 (toPoly_nonempty t) (fun _ h => toPoly_card_pos t h) hbz hedge hm_pos hm_abs
        exact eqDerives_abs_of_subset basis12 (by rw [toPoly_termOfMon hm_pos, Finset.singleton_subset_iff]; exact hmem)
  intro s t hst
  exact eqDerives_of_abs_both basis12
    (hAbs s t fun v => by rw [hst v, addR_idem'])
    (hAbs t s fun v => by rw [hst v, addR_idem'])

/-! ### Section 7: Rigidity (Lemma 4.1) & Nonfinite Basability (Theorem 4.2) -/

/-- Lemma 4.1 (`lem:rigidity`): If `s` is unmarked and non-basic-zero, and `R_{ij} ⊨ s ≈ t`
for any `(i, j) ∈ {(0,1), (0,2), (1,1), (1,2)}`, then `(toPoly s) = (toPoly t)`! -/
private lemma rigidity {i j : Fin 3} (hij : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 1) ∨ (i = 1 ∧ j = 2))
    {s t : SemiringTerm} (hnbz : ¬ IsBasicZero (toPoly s)) (hunm : ∀ x, ¬ marked (toPoly s) x)
    (hid : SatisfiesId i j s t) : (toPoly s) = (toPoly t) := by
  -- First show `(toPoly t) ⊆ (toPoly s)`!
  have hsub : ∀ {a b : SemiringTerm}, ¬ IsBasicZero (toPoly a) → (∀ x, ¬ marked (toPoly a) x) →
      SatisfiesId i j a b → (toPoly b) ⊆ (toPoly a) := by
    intro a b ha_nbz ha_unm hab m hm
    have hm_pos : 1 ≤ m.card := toPoly_card_pos b hm
    have hm_abs : ∀ v, addR i j (evalMon v m) (evalPoly i j v (toPoly a)) = evalPoly i j v (toPoly a) := fun v => by
      have h1 := hab v
      rw [eval_eq_evalPoly, eval_eq_evalPoly] at h1
      have h2 := leR_of_mem_evalPoly i j v hm
      rw [← h1] at h2; exact h2
    by_cases hedge : ∃ x y, quadAdj (toPoly a) x y
    · have hcrit := necessary_criteria (fun _ h => toPoly_card_pos a h) ha_nbz hedge hm_pos
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases hcrit.1 hm_abs with h | ⟨w₁, _, _, hm1, _, _⟩ | ⟨_, _, _, _, hmx, _⟩
        · exact h
        · exact absurd hm1 (ha_unm w₁)
        · exact absurd hmx (ha_unm _)
      · rcases hcrit.2.1 hm_abs with h | ⟨w₁, _, _, hm1, _, _⟩ | ⟨_, _, w, _, hmw, _⟩
        · exact h
        · exact absurd hm1 (ha_unm w₁)
        · exact absurd hmw (ha_unm w)
      · rcases hcrit.2.2.1 hm_abs with h | ⟨x, y, _, _, _, hmx | hmy, _⟩
        · exact h
        · exact absurd hmx (ha_unm x)
        · exact absurd hmy (ha_unm y)
      · rcases hcrit.2.2.2 hm_abs with h | ⟨x, _, _, _, _, hmx, _, _⟩
        · exact h
        · exact absurd hmx (ha_unm x)
    · push Not at hedge
      exact linear_poly_abs_only_mem i j (toPoly_nonempty a) (fun _ h => toPoly_card_pos a h) ha_nbz hedge hm_pos hm_abs
  have hts : (toPoly t) ⊆ (toPoly s) := hsub hnbz hunm hid
  -- Therefore `t` is ALSO non-basic-zero and unmarked!
  have ht_nbz : ¬ IsBasicZero (toPoly t) := by
    rintro (⟨m, hm, h3⟩ | ⟨x, hx⟩ | ⟨x, k, hwalk⟩)
    · exact hnbz (Or.inl ⟨m, hts hm, h3⟩)
    · exact hnbz (Or.inr (Or.inl ⟨x, hts hx⟩))
    · have hlift : ∀ {u w len}, Walk (toPoly t) u w len → Walk (toPoly s) u w len := by
        intro u w len hw
        induction hw with
        | zero _ => exact Walk.zero _
        | step hab _ ih => exact Walk.step ⟨hab.1, hts hab.2⟩ ih
      exact hnbz (Or.inr (Or.inr ⟨x, k, hlift hwalk⟩))
  have ht_unm : ∀ x, ¬ marked (toPoly t) x := fun x ⟨hx, y, hxy⟩ =>
    hunm x ⟨hts hx, y, hxy.1, hts hxy.2⟩
  have hst : (toPoly s) ⊆ (toPoly t) := hsub ht_nbz ht_unm (fun v => (hid v).symm)
  exact Finset.Subset.antisymm hst hts

/-- Variables occurring in a `SemiringTerm`. -/
private def termVars : SemiringTerm → Finset ℕ
  | .var n => {n}
  | .add s t => (termVars s) ∪ (termVars t)
  | .mul s t => (termVars s) ∪ (termVars t)

private lemma mem_vars_of_mem_toPoly (s : SemiringTerm) {m : Mon} (hm : m ∈ (toPoly s)) {x : ℕ} (hx : x ∈ m) :
    x ∈ (termVars s) := by
  induction s generalizing m with
  | var n =>
    simp only [toPoly, Finset.mem_singleton] at hm
    subst hm; simp only [Multiset.mem_singleton] at hx; simp [termVars, hx]
  | add s t ihs iht =>
    rcases Finset.mem_union.mp hm with h | h
    · exact Finset.mem_union_left _ (ihs h hx)
    · exact Finset.mem_union_right _ (iht h hx)
  | mul s t ihs iht =>
    obtain ⟨m₁, h1, m₂, h2, rfl⟩ := mem_mulPoly.mp hm
    rcases Multiset.mem_add.mp hx with h | h
    · exact Finset.mem_union_left _ (ihs h1 h)
    · exact Finset.mem_union_right _ (iht h2 h)

/-- An odd cycle `C_L` (`L = 2 * K + 1 ≥ 3`) has NO odd closed walk of length `< L`! -/
private lemma no_short_odd_closed_walk_cycle (K : ℕ) (_hK : 1 ≤ K) :
    let L := 2 * K + 1
    let cadj : ℕ → ℕ → Prop := fun a b =>
      a < L ∧ b < L ∧ ((a + 1) % L = b ∨ (b + 1) % L = a)
    ∀ (f : ℕ → ℕ) (r : ℕ), r < L → r % 2 = 1 →
      (∀ t < r, cadj (f t) (f (t + 1))) → f r ≠ f 0 := by
  intro L cadj f r hrL hrodd hadj hclose
  -- Lift `f t` to an integer walk `z t : ℤ` with `z 0 = 0`, `|z (t+1) - z t| = 1`, and `(z t + f 0) % L = f t`!
  have hstep : ∀ t < r, ((f t + 1) % L = f (t + 1)) ∨ ((f (t + 1) + 1) % L = f t) := fun t ht => (hadj t ht).2.2
  -- Build `z : ℕ → ℤ` recursively:
  let stepZ : ℕ → ℤ := fun t => if (f t + 1) % L = f (t + 1) then 1 else -1
  let z : ℕ → ℤ := fun t => (Finset.range t).sum stepZ
  have hz_prop : ∀ t ≤ r, (z t).natAbs ≤ t ∧ z t % 2 = (t % 2 : ℕ) ∧
      ((f 0 : ℤ) + z t) % (L : ℤ) = (f t : ℤ) := by
    intro t; induction t with
    | zero =>
      intro _
      have hf0 : f 0 < L := (hadj 0 (by omega)).1
      refine ⟨by simp [z], by simp [z], ?_⟩
      simp only [z, Finset.range_zero, Finset.sum_empty, add_zero]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    | succ t ih =>
      intro ht
      obtain ⟨habs, hpar, hmod⟩ := ih (by omega)
      have hz_succ : z (t + 1) = z t + stepZ t := by simp [z, Finset.sum_range_succ]
      have hft1 : f (t + 1) < L := (hadj t (by omega)).2.1
      have hft : f t < L := (hadj t (by omega)).1
      by_cases hs : (f t + 1) % L = f (t + 1)
      · have hst : stepZ t = 1 := if_pos hs
        rw [hz_succ, hst]
        refine ⟨by omega, by omega, ?_⟩
        rw [← add_assoc, Int.add_emod, hmod]
        have h1 : ((f t : ℤ) + 1) % (L : ℤ) = (f (t + 1) : ℤ) := by
          have := congrArg (Nat.cast (R := ℤ)) hs
          push_cast at this; exact this
        have h2 : (((f t : ℤ) + 1 % (L : ℤ)) % (L : ℤ)) = ((f t : ℤ) + 1) % (L : ℤ) := by
          rw [Int.add_emod (f t : ℤ) (1 % (L : ℤ)), Int.emod_emod, ← Int.add_emod]
        rw [h2, h1]
      · have hs' : (f (t + 1) + 1) % L = f t := (hstep t (by omega)).resolve_left hs
        have hst : stepZ t = -1 := if_neg hs
        rw [hz_succ, hst]
        refine ⟨by omega, by omega, ?_⟩
        have h1 : ((f (t + 1) : ℤ) + 1) % (L : ℤ) = (f t : ℤ) := by
          have := congrArg (Nat.cast (R := ℤ)) hs'
          push_cast at this; exact this
        -- Show `((f 0 + z t) + (-1)) % L = f (t + 1)`:
        have h2 : ((f 0 : ℤ) + z t + -1) % (L : ℤ) = ((f t : ℤ) + -1) % (L : ℤ) := by
          conv_lhs =>
            rw [Int.add_emod, hmod]
            rw [← Int.emod_eq_of_lt (a := (f t : ℤ)) (b := (L : ℤ)) (by omega) (by omega), ← Int.add_emod]
        rw [← add_assoc, h2, ← h1]
        have h3 : (((f (t + 1) : ℤ) + 1) % (L : ℤ) + -1) % (L : ℤ) = ((f (t + 1) : ℤ) + 1 + -1) % (L : ℤ) := by
          rw [Int.add_emod, Int.emod_emod, ← Int.add_emod]
        rw [h3, add_assoc]
        simp only [add_neg_cancel, add_zero]
        exact Int.emod_eq_of_lt (by omega) (by omega)
  obtain ⟨habs, hpar, hmod⟩ := hz_prop r le_rfl
  rw [hclose] at hmod
  -- From `((f 0 : ℤ) + z r) % L = f 0`, we get `z r % L = 0`, so `L ∣ z r`!
  have hdvd : (L : ℤ) ∣ z r := by
    have h1 : ((f 0 : ℤ) + z r) % (L : ℤ) = ((f 0 : ℤ) + 0) % (L : ℤ) := by
      have hf0 : f 0 < L := (hadj 0 (by omega)).1
      rw [hmod, add_zero, Int.emod_eq_of_lt (by omega) (by omega)]
    have h2 : (L : ℤ) ∣ ((f 0 : ℤ) + z r) - ((f 0 : ℤ) + 0) :=
      Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h1)
    simpa using h2
  -- Yet `(z r).natAbs ≤ r < L`, so `z r = 0`!
  have hz0 : z r = 0 := by
    by_contra hne
    have hle : L ≤ (z r).natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (Int.natAbs_dvd_natAbs.mpr hdvd)
    omega
  rw [hz0] at hpar
  simp [hrodd] at hpar

/-- Theorem 4.2 (`thm:nfb`): None of `R_{01}, R_{02}, R_{11}, R_{12}` is finitely based! -/
private lemma not_finitely_based {i j : Fin 3}
    (hij : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 1) ∨ (i = 1 ∧ j = 2)) :
    ¬ IsFinitelyBased i j := by
  rintro ⟨F, hsound, hcomp⟩
  -- Pick `m` bounding `|(termVars s)|` and `|(termVars t)|` for all `(s, t) ∈ F`, and set `K := max m 2`, `L := 2 * K + 1`.
  let m : ℕ := F.sup fun p => max (termVars p.1).card (termVars p.2).card
  let K : ℕ := max m 2
  let L : ℕ := 2 * K + 1
  have hK1 : 1 ≤ K := by omega
  have hmL : m < L := by omega
  let w : SemiringTerm := oddCycleTerm K
  let z : SemiringTerm := .var (2 * K + 1)
  have hwid : SatisfiesId i j w (.add w z) := by
    have h0 := sigma0_sound i j (absId z w) (Or.inr ⟨K, hK1, rfl⟩)
    intro v
    have hv := h0 v
    simp only [absId, SemiringTerm.eval] at hv ⊢
    rw [addR_comm']; exact hv.symm
  have hder : EqDerives (F : Set (SemiringTerm × SemiringTerm)) w (.add w z) := hcomp w (.add w z) hwid
  -- Characterize `(toPoly w)`: every monomial is `{r, (r + 1) % L}` with `r < L`!
  have hw_poly : ∀ mon ∈ (toPoly w), ∃ a b : ℕ, mon = {a, b} ∧ a < L ∧ b < L ∧
      ((a + 1) % L = b ∨ (b + 1) % L = a) := by
    have hpath : ∀ n < 2 * K, ∀ mon ∈ (toPoly (pathTerm n)), ∃ r ≤ n, mon = {r, r + 1} := by
      intro n; induction n with
      | zero => intro _ mon hm; simp only [pathTerm, toPoly, mulPoly] at hm; exact ⟨0, le_rfl, by simpa using hm⟩
      | succ n ih =>
        intro hn mon hm
        simp only [pathTerm, toPoly, Finset.mem_union] at hm
        rcases hm with h | h
        · obtain ⟨r, hr, rfl⟩ := ih (by omega) mon h; exact ⟨r, by omega, rfl⟩
        · simp only [mulPoly] at h; exact ⟨n + 1, le_rfl, by simpa using h⟩
    intro mon hm
    simp only [w, oddCycleTerm, toPoly, Finset.mem_union] at hm
    rcases hm with h | h
    · obtain ⟨r, hr, rfl⟩ := hpath (2 * K - 1) (by omega) mon h
      exact ⟨r, r + 1, rfl, by omega, by omega, Or.inl (Nat.mod_eq_of_lt (by omega))⟩
    · simp only [mulPoly] at h
      have hmon : mon = {2 * K, 0} := by simpa using h
      refine ⟨2 * K, 0, hmon, by omega, by omega, Or.inl ?_⟩
      show (2 * K + 1) % (2 * K + 1) = 0
      exact Nat.mod_self _
  -- Key lemma: if `R_{ij} ⊨ s ≈ t` with `(termVars s).card ≤ m` and either `(toPoly (s.subst σ)) ⊆ (toPoly w)`
  -- or `mulPoly P (toPoly (s.subst σ)) ⊆ (toPoly w)` (`P.Nonempty`), then `(toPoly s) = (toPoly t)` (by Rigidity!).
  have hax_rigid : ∀ {s t : SemiringTerm}, SatisfiesId i j s t → (termVars s).card ≤ m →
      ((∀ σ : ℕ → SemiringTerm, (toPoly (s.subst σ)) ⊆ (toPoly w) → (toPoly s) = (toPoly t)) ∧
       (∀ (σ : ℕ → SemiringTerm) (P : Poly), P.Nonempty → (∀ q ∈ P, 1 ≤ q.card) →
          mulPoly P (toPoly (s.subst σ)) ⊆ (toPoly w) → (toPoly s) = (toPoly t))) := by
    intro s t hsat hvars_le
    constructor
    · -- Case 1: `(toPoly (s.subst σ)) ⊆ (toPoly w)`. Show `s` is non-basic-zero and unmarked!
      intro σ hsub
      have hmon_sub : ∀ mon ∈ (toPoly s), substMon σ mon ⊆ (toPoly w) := fun mon hmon => by
        intro q hq; apply hsub; rw [toPoly_subst_eq]; exact Finset.mem_biUnion.mpr ⟨mon, hmon, hq⟩
      have hsubst_card_list : ∀ l : List ℕ, 1 ≤ l.length → ∃ q ∈ substMonPoly σ l, l.length ≤ q.card := by
        intro l
        induction l with
        | nil => intro hl; simp at hl
        | cons x xs ih =>
          intro _
          cases xs with
          | nil =>
            obtain ⟨q, hq⟩ := toPoly_nonempty (σ x)
            exact ⟨q, hq, toPoly_card_pos (σ x) hq⟩
          | cons y ys =>
            obtain ⟨q₁, hq1⟩ := toPoly_nonempty (σ x)
            obtain ⟨q₂, hq2, hc2⟩ := ih (by simp)
            have h1 := toPoly_card_pos (σ x) hq1
            refine ⟨q₁ + q₂, ?_, ?_⟩
            · exact mem_mulPoly.mpr ⟨q₁, hq1, q₂, hq2, rfl⟩
            · rw [Multiset.card_add]; simp only [List.length_cons] at hc2 ⊢; omega
      have hsubst_card : ∀ mon : Mon, 1 ≤ mon.card → ∃ q ∈ substMon σ mon, mon.card ≤ q.card := fun mon hl => by
        obtain ⟨q, hq, hc⟩ := hsubst_card_list mon.toList (by rwa [Multiset.length_toList])
        refine ⟨q, ?_, by rwa [Multiset.length_toList] at hc⟩
        have hcoe : (mon.toList : Mon) = mon := Multiset.coe_toList mon
        rw [← hcoe]; exact hq
      have hno3 : ¬ ∃ mon ∈ (toPoly s), 3 ≤ mon.card := by
        rintro ⟨mon, hmon, h3⟩
        obtain ⟨q, hq, hqc⟩ := hsubst_card mon (by omega)
        obtain ⟨a, b, rfl, _⟩ := hw_poly q (hmon_sub mon hmon hq)
        simp at hqc; omega
      have hno_sq : ¬ ∃ x, ({x, x} : Mon) ∈ (toPoly s) := by
        rintro ⟨x, hx⟩
        obtain ⟨q, hq⟩ := toPoly_nonempty (σ x)
        have hqq : q + q ∈ substMon σ ({x, x} : Mon) :=
          mem_mulPoly.mpr ⟨q, hq, q, hq, rfl⟩
        obtain ⟨a, b, hab, haL, hbL, hadj⟩ := hw_poly (q + q) (hmon_sub {x, x} hx hqq)
        have hq1 : q.card = 1 := by
          have := toPoly_card_pos (σ x) hq
          have h2 : (q + q).card = 2 := by rw [hab]; simp
          simp at h2; omega
        obtain ⟨v, rfl⟩ := Multiset.card_eq_one.mp hq1
        -- `{v, v} = {a, b}` => `a = b`, contradicting `hadj` (`(a + 1) % L = a` with `L ≥ 5`)!
        have hab_eq : a = b := by
          have ha : a ∈ ({v} + {v} : Mon) := by rw [hab]; simp
          have hb : b ∈ ({v} + {v} : Mon) := by rw [hab]; simp
          simp at ha hb; omega
        subst hab_eq
        rcases hadj with h | h <;> {
          by_cases ha1 : a + 1 < L
          · rw [Nat.mod_eq_of_lt ha1] at h; omega
          · have : a + 1 = L := by omega
            rw [this, Nat.mod_self] at h; omega }
      have hunm : ∀ x, ¬ marked (toPoly s) x := by
        rintro x ⟨hx, y, hxy⟩
        -- Since `{x} ∈ (toPoly s)`, every `q ∈ (toPoly (σ x))` has `q ∈ (toPoly w)`, so `q.card = 2`!
        obtain ⟨qx, hqx⟩ := toPoly_nonempty (σ x)
        obtain ⟨a, b, hqx_eq, _⟩ := hw_poly qx (hmon_sub {x} hx hqx)
        obtain ⟨qy, hqy⟩ := toPoly_nonempty (σ y)
        have hqxy : qx + qy ∈ substMon σ ({x, y} : Mon) :=
          mem_mulPoly.mpr ⟨qx, hqx, qy, hqy, rfl⟩
        obtain ⟨c, d, hcd, _⟩ := hw_poly (qx + qy) (hmon_sub {x, y} hxy.2 hqxy)
        have h1 := toPoly_card_pos (σ y) hqy
        have hcard : (qx + qy).card = 2 := by rw [hcd]; simp
        have hqx2 : qx.card = 2 := by rw [hqx_eq]; simp
        rw [Multiset.card_add, hqx2] at hcard; omega
      have hno_odd : ¬ HasOddCycle (toPoly s) := by
        rintro ⟨x₀, k, hwalk⟩
        -- Every vertex `x` with `quadVert (toPoly s) x` has some singleton `{v_x} ∈ (toPoly (σ x))`!
        have hv_ex : ∀ x, quadVert (toPoly s) x → ∃ vx : ℕ, ({vx} : Mon) ∈ (toPoly (σ x)) := fun x ⟨y, hxy⟩ => by
          obtain ⟨qx, hqx⟩ := toPoly_nonempty (σ x)
          obtain ⟨qy, hqy⟩ := toPoly_nonempty (σ y)
          have hqxy : qx + qy ∈ substMon σ ({x, y} : Mon) := mem_mulPoly.mpr ⟨qx, hqx, qy, hqy, rfl⟩
          obtain ⟨a, b, hab, _⟩ := hw_poly (qx + qy) (hmon_sub {x, y} hxy.2 hqxy)
          have hcx : qx.card = 1 := by
            have := toPoly_card_pos (σ x) hqx; have := toPoly_card_pos (σ y) hqy
            have hc : (qx + qy).card = 2 := by rw [hab]; simp
            rw [Multiset.card_add] at hc; omega
          obtain ⟨vx, rfl⟩ := Multiset.card_eq_one.mp hcx
          exact ⟨vx, hqx⟩
        classical
        let φ : ℕ → ℕ := fun x => if h : quadVert (toPoly s) x then Classical.choose (hv_ex x h) else 0
        have hφ_adj : ∀ a b, quadAdj (toPoly s) a b →
            φ a < L ∧ φ b < L ∧ ((φ a + 1) % L = φ b ∨ (φ b + 1) % L = φ a) := fun a b hab => by
          have hqa : quadVert (toPoly s) a := ⟨b, hab⟩
          have hqb : quadVert (toPoly s) b := ⟨a, quadAdj_symm hab⟩
          have ha_mem : ({φ a} : Mon) ∈ (toPoly (σ a)) := by simp only [φ, dif_pos hqa]; exact Classical.choose_spec (hv_ex a hqa)
          have hb_mem : ({φ b} : Mon) ∈ (toPoly (σ b)) := by simp only [φ, dif_pos hqb]; exact Classical.choose_spec (hv_ex b hqb)
          have hpair : ({φ a, φ b} : Mon) ∈ substMon σ ({a, b} : Mon) :=
            mem_mulPoly.mpr ⟨{φ a}, ha_mem, {φ b}, hb_mem, rfl⟩
          obtain ⟨c, d, hcd, hcL, hdL, hcd_adj⟩ := hw_poly _ (hmon_sub {a, b} hab.2 hpair)
          have hmem_c : c = φ a ∨ c = φ b := by
            have h : c ∈ ({φ a, φ b} : Mon) := by rw [hcd]; simp
            simpa using h
          have hmem_d : d = φ a ∨ d = φ b := by
            have h : d ∈ ({φ a, φ b} : Mon) := by rw [hcd]; simp
            simpa using h
          have hcd_ne : c ≠ d := by
            rintro rfl; rcases hcd_adj with h | h <;> {
              by_cases h1 : c + 1 < L
              · rw [Nat.mod_eq_of_lt h1] at h; omega
              · have hL : c + 1 = L := by omega
                rw [hL, Nat.mod_self] at h; omega }
          rcases hmem_c with rfl | rfl <;> rcases hmem_d with h | h
          · exact absurd h.symm hcd_ne
          · subst h; exact ⟨hcL, hdL, hcd_adj⟩
          · subst h; exact ⟨hdL, hcL, hcd_adj.symm⟩
          · exact absurd h.symm hcd_ne
        -- Take a SHORTEST odd closed walk in `G((toPoly s))` -> its length `r` satisfies `r ≤ (termVars s).card ≤ m < L`!
        -- (Any repeated vertex splits an odd closed walk into an even + an odd closed walk, strictly shorter!)
        have hex_short : ∃ (x : ℕ) (r : ℕ), r ≤ (termVars s).card ∧ r % 2 = 1 ∧ Walk (toPoly s) x x r := by
          have hex : ∃ r : ℕ, r % 2 = 1 ∧ ∃ x, Walk (toPoly s) x x r := ⟨2 * k + 1, by omega, x₀, hwalk⟩
          let r := Nat.find hex
          have hr_spec := Nat.find_spec hex
          obtain ⟨hrodd, x, hwx⟩ := hr_spec
          refine ⟨x, r, ?_, hrodd, hwx⟩
          by_contra hgt
          -- Extract the vertex sequence `g : Fin (r + 1) → ℕ` of `hwx`:
          -- First `r` vertices `g 0, ..., g (r - 1)` all lie in `(termVars s)`, and `r > (termVars s).card`, so two coincide (`a < b < r` with `g a = g b`)!
          have hex_g : ∀ {u v len : ℕ}, Walk (toPoly s) u v len →
              ∃ g : ℕ → ℕ, g 0 = u ∧ g len = v ∧
                (∀ t < len, quadAdj (toPoly s) (g t) (g (t + 1))) ∧
                (∀ a b, a ≤ b → b ≤ len → Walk (toPoly s) (g a) (g b) (b - a)) := by
            intro u v len hw
            induction hw with
            | zero u =>
              refine ⟨fun _ => u, rfl, rfl, fun t ht => absurd ht (Nat.not_lt_zero t), fun a b hab hb => ?_⟩
              have : b - a = 0 := by omega
              rw [this]; exact Walk.zero u
            | @step u v w len huv _ ih =>
              obtain ⟨g, hg0, hgl, hg_adj, hg_walk⟩ := ih
              refine ⟨fun t => match t with | 0 => u | t + 1 => g t, rfl, hgl, fun t ht => ?_, fun a b hab hb => ?_⟩
              · cases t with
                | zero => simpa [hg0] using huv
                | succ t => exact hg_adj t (by omega)
              · cases a with
                | zero =>
                  cases b with
                  | zero => exact Walk.zero u
                  | succ b =>
                    have h1 := hg_walk 0 b (Nat.zero_le b) (by omega)
                    rw [hg0, Nat.sub_zero] at h1
                    have h2 : b + 1 - 0 = b + 1 := rfl
                    rw [h2]
                    exact Walk.step huv h1
                | succ a =>
                  cases b with
                  | zero => omega
                  | succ b =>
                    change Walk (toPoly s) (g a) (g b) (b + 1 - (a + 1))
                    rw [show b + 1 - (a + 1) = b - a by omega]
                    exact hg_walk a b (by omega) (by omega)
          obtain ⟨g, hg0, hgr, hg_adj, hg_walk⟩ := hex_g hwx
          have hmaps : Set.MapsTo g (Finset.range r : Set ℕ) ((termVars s) : Set ℕ) := by
            intro t ht
            have htr : t < r := Finset.mem_range.mp ht
            exact mem_vars_of_mem_toPoly s (hg_adj t htr).2 (Multiset.mem_cons_self _ _)
          have hlt_card : (termVars s).card < (Finset.range r).card := by rw [Finset.card_range]; omega
          obtain ⟨a, ha, b, hb, hab_ne, hgab⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt_card hmaps
          have har : a < r := Finset.mem_range.mp ha
          have hbr : b < r := Finset.mem_range.mp hb
          wlog hab : a < b generalizing a b
          · exact this b hb a ha hab_ne.symm hgab.symm hbr har (by omega)
          -- Split `hwx` into two closed walks of lengths `b - a` and `r - (b - a)` (both `< r`, summing to `r` odd)!
          have hw_mid : Walk (toPoly s) (g a) (g a) (b - a) := hgab ▸ hg_walk a b (by omega) (by omega)
          have hw_out : Walk (toPoly s) (g a) (g a) (r - (b - a)) := by
            have h1 := hg_walk b r (by omega) le_rfl
            have h2 := hg_walk 0 a (Nat.zero_le a) (by omega)
            rw [hgr, ← hg0] at h1
            have h3 := walk_trans h1 h2
            rw [← hgab] at h3
            rwa [show r - b + (a - 0) = r - (b - a) by omega] at h3
          rcases Nat.mod_two_eq_zero_or_one (b - a) with h0 | h1
          · exact Nat.find_min hex (show r - (b - a) < r by omega) ⟨by omega, g a, hw_out⟩
          · exact Nat.find_min hex (show b - a < r by omega) ⟨h1, g a, hw_mid⟩
        obtain ⟨x, r, hr_le, hrodd, hwx⟩ := hex_short
        have hex_g : ∀ {u v len : ℕ}, Walk (toPoly s) u v len →
            ∃ g : ℕ → ℕ, g 0 = u ∧ g len = v ∧ ∀ t < len, quadAdj (toPoly s) (g t) (g (t + 1)) := by
          intro u v len hw
          induction hw with
          | zero u => exact ⟨fun _ => u, rfl, rfl, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
          | @step u v w len huv _ ih =>
            obtain ⟨g, hg0, hgl, hg⟩ := ih
            refine ⟨fun t => match t with | 0 => u | t + 1 => g t, rfl, hgl, fun t ht => ?_⟩
            cases t with
            | zero => simpa [hg0] using huv
            | succ t => exact hg t (by omega)
        obtain ⟨g, hg0, hgr, hg_adj⟩ := hex_g hwx
        exact no_short_odd_closed_walk_cycle K hK1 (fun t => φ (g t)) r (by omega) hrodd
          (fun t ht => hφ_adj (g t) (g (t + 1)) (hg_adj t ht)) (by rw [hgr, hg0])
      exact rigidity hij (fun h => h.elim hno3 (fun h' => h'.elim hno_sq hno_odd)) hunm hsat
    · -- Case 2: `mulPoly P (toPoly (s.subst σ)) ⊆ (toPoly w)` with `P.Nonempty` -> `s` is purely linear!
      intro σ P hP hPpos hsub
      obtain ⟨p₀, hp₀⟩ := hP
      have hp1 : 1 ≤ p₀.card := hPpos p₀ hp₀
      have hlin : ∀ mon ∈ (toPoly s), mon.card = 1 := by
        intro mon hmon
        have hsubst_card : ∀ l : List ℕ, l ≠ [] → ∃ q ∈ substMonPoly σ l, l.length ≤ q.card := by
          intro l; induction l with
          | nil => intro h; exact absurd rfl h
          | cons x xs ih =>
            intro _
            cases xs with
            | nil => obtain ⟨q, hq⟩ := toPoly_nonempty (σ x); exact ⟨q, hq, toPoly_card_pos (σ x) hq⟩
            | cons y ys =>
              obtain ⟨q₁, hq1⟩ := toPoly_nonempty (σ x)
              obtain ⟨q₂, hq2, hc2⟩ := ih (by simp)
              have h1 := toPoly_card_pos (σ x) hq1
              refine ⟨q₁ + q₂, mem_mulPoly.mpr ⟨q₁, hq1, q₂, hq2, rfl⟩, ?_⟩
              rw [Multiset.card_add]
              simp only [List.length_cons] at hc2 ⊢
              omega
        have hpos := toPoly_card_pos s hmon
        obtain ⟨q, hq, hqc⟩ : ∃ q ∈ substMon σ mon, mon.card ≤ q.card := by
          induction mon using Quot.inductionOn with | _ l =>
          exact hsubst_card l (by intro h; subst h; simp at hpos)
        have hq_sub : q ∈ (toPoly (s.subst σ)) := by rw [toPoly_subst_eq]; exact Finset.mem_biUnion.mpr ⟨mon, hmon, hq⟩
        have hpq : p₀ + q ∈ mulPoly P (toPoly (s.subst σ)) := mem_mulPoly.mpr ⟨p₀, hp₀, q, hq_sub, rfl⟩
        obtain ⟨a, b, hab, _⟩ := hw_poly (p₀ + q) (hsub hpq)
        have hc : (p₀ + q).card = 2 := by rw [hab]; simp
        rw [Multiset.card_add] at hc; omega
      have hnbz : ¬ IsBasicZero (toPoly s) := by
        rintro (⟨mon, hmon, h3⟩ | ⟨x, hx⟩ | ⟨x, k, hwalk⟩)
        · have := hlin mon hmon; omega
        · have := hlin {x, x} hx; simp at this
        · cases hwalk with | @step _ y _ _ hxy _ => have := hlin {x, y} hxy.2; simp at this
      have hunm : ∀ x, ¬ marked (toPoly s) x := fun x ⟨_, y, hxy⟩ => by
        have := hlin {x, y} hxy.2; simp at this
      exact rigidity hij hnbz hunm hsat
  -- Structural induction on `EqDerives F a b`: preserves `.toPoly` under any substitution/multiplicative context inside `(toPoly w)`!
  have hinv : ∀ {a b : SemiringTerm}, EqDerives (F : Set (SemiringTerm × SemiringTerm)) a b →
      (∀ σ : ℕ → SemiringTerm,
        ((toPoly (a.subst σ)) ⊆ (toPoly w) ∨ (toPoly (b.subst σ)) ⊆ (toPoly w)) →
        (toPoly (a.subst σ)) = (toPoly (b.subst σ))) ∧
      (∀ (σ : ℕ → SemiringTerm) (P : Poly), P.Nonempty → (∀ q ∈ P, 1 ≤ q.card) →
        (mulPoly P (toPoly (a.subst σ)) ⊆ (toPoly w) ∨ mulPoly P (toPoly (b.subst σ)) ⊆ (toPoly w)) →
        (toPoly (a.subst σ)) = (toPoly (b.subst σ))) := by
    intro a b hab
    induction hab with
    | @ax s t hmem =>
      have hF : (s, t) ∈ F := hmem
      have hsat_st : SatisfiesId i j s t := hsound (s, t) hF
      have hsat_ts : SatisfiesId i j t s := fun v => (hsat_st v).symm
      have hs_vars : (termVars s).card ≤ m :=
        le_trans (le_max_left _ _) (Finset.le_sup (f := fun p : SemiringTerm × SemiringTerm => max (termVars p.1).card (termVars p.2).card) hF)
      have ht_vars : (termVars t).card ≤ m :=
        le_trans (le_max_right _ _) (Finset.le_sup (f := fun p : SemiringTerm × SemiringTerm => max (termVars p.1).card (termVars p.2).card) hF)
      have hrigid_s := hax_rigid hsat_st hs_vars
      have hrigid_t := hax_rigid hsat_ts ht_vars
      constructor
      · intro σ h
        have hst_eq : (toPoly s) = (toPoly t) := h.elim (hrigid_s.1 σ) (fun ht => (hrigid_t.1 σ ht).symm)
        rw [toPoly_subst_eq, toPoly_subst_eq, hst_eq]
      · intro σ P hP hPpos h
        have hst_eq : (toPoly s) = (toPoly t) := h.elim (hrigid_s.2 σ P hP hPpos) (fun ht => (hrigid_t.2 σ P hP hPpos ht).symm)
        rw [toPoly_subst_eq, toPoly_subst_eq, hst_eq]
    | add_assoc a b c =>
      exact ⟨fun σ _ => by simp [SemiringTerm.subst, toPoly, Finset.union_assoc],
             fun σ _ _ _ _ => by simp [SemiringTerm.subst, toPoly, Finset.union_assoc]⟩
    | add_comm a b =>
      exact ⟨fun σ _ => by simp [SemiringTerm.subst, toPoly, Finset.union_comm],
             fun σ _ _ _ _ => by simp [SemiringTerm.subst, toPoly, Finset.union_comm]⟩
    | add_idem a =>
      exact ⟨fun σ _ => by simp [SemiringTerm.subst, toPoly],
             fun σ _ _ _ _ => by simp [SemiringTerm.subst, toPoly]⟩
    | mul_assoc a b c =>
      exact ⟨fun σ _ => by simp [SemiringTerm.subst, toPoly, mulPoly_assoc],
             fun σ _ _ _ _ => by simp [SemiringTerm.subst, toPoly, mulPoly_assoc]⟩
    | mul_comm a b =>
      exact ⟨fun σ _ => by simp [SemiringTerm.subst, toPoly, mulPoly_comm],
             fun σ _ _ _ _ => by simp [SemiringTerm.subst, toPoly, mulPoly_comm]⟩
    | left_distrib a b c =>
      exact ⟨fun σ _ => by simp [SemiringTerm.subst, toPoly, mulPoly_union_right],
             fun σ _ _ _ _ => by simp [SemiringTerm.subst, toPoly, mulPoly_union_right]⟩
    | right_distrib a b c =>
      exact ⟨fun σ _ => by simp [SemiringTerm.subst, toPoly, mulPoly_union_left],
             fun σ _ _ _ _ => by simp [SemiringTerm.subst, toPoly, mulPoly_union_left]⟩
    | refl a => exact ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
    | symm _ ih =>
      exact ⟨fun σ h => (ih.1 σ h.symm).symm, fun σ P hP hPp h => (ih.2 σ P hP hPp h.symm).symm⟩
    | trans _ _ ih1 ih2 =>
      constructor
      · intro σ h
        rcases h with ha | hc
        · have hab := ih1.1 σ (Or.inl ha)
          exact hab.trans (ih2.1 σ (Or.inl (hab ▸ ha)))
        · have hbc := ih2.1 σ (Or.inr hc)
          exact (ih1.1 σ (Or.inr (hbc.symm ▸ hc))).trans hbc
      · intro σ P hP hPp h
        rcases h with ha | hc
        · have hab := ih1.2 σ P hP hPp (Or.inl ha)
          exact hab.trans (ih2.2 σ P hP hPp (Or.inl (hab ▸ ha)))
        · have hbc := ih2.2 σ P hP hPp (Or.inr hc)
          exact (ih1.2 σ P hP hPp (Or.inr (hbc.symm ▸ hc))).trans hbc
    | add_cong _ _ ih1 ih2 =>
      constructor
      · intro σ h
        simp only [SemiringTerm.subst, toPoly, Finset.union_subset_iff] at h ⊢
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [ih1.1 σ (Or.inl h1), ih2.1 σ (Or.inl h2)]
        · rw [ih1.1 σ (Or.inr h1), ih2.1 σ (Or.inr h2)]
      · intro σ P hP hPp h
        simp only [SemiringTerm.subst, toPoly, mulPoly_union_right, Finset.union_subset_iff] at h ⊢
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [ih1.2 σ P hP hPp (Or.inl h1), ih2.2 σ P hP hPp (Or.inl h2)]
        · rw [ih1.2 σ P hP hPp (Or.inr h1), ih2.2 σ P hP hPp (Or.inr h2)]
    | @mul_cong a₁ a₂ b₁ b₂ _ _ ih1 ih2 =>
      constructor
      · intro σ h
        simp only [SemiringTerm.subst, toPoly] at h ⊢
        rcases h with h1 | h2
        · have ha : (toPoly (a₁.subst σ)) = (toPoly (a₂.subst σ)) :=
            ih1.2 σ (toPoly (b₁.subst σ)) (toPoly_nonempty _) (fun _ h => toPoly_card_pos _ h)
              (Or.inl (by rwa [mulPoly_comm]))
          have hb : (toPoly (b₁.subst σ)) = (toPoly (b₂.subst σ)) :=
            ih2.2 σ (toPoly (a₁.subst σ)) (toPoly_nonempty _) (fun _ h => toPoly_card_pos _ h) (Or.inl h1)
          rw [ha, hb]
        · have ha : (toPoly (a₁.subst σ)) = (toPoly (a₂.subst σ)) :=
            ih1.2 σ (toPoly (b₂.subst σ)) (toPoly_nonempty _) (fun _ h => toPoly_card_pos _ h)
              (Or.inr (by rwa [mulPoly_comm]))
          have hb : (toPoly (b₁.subst σ)) = (toPoly (b₂.subst σ)) :=
            ih2.2 σ (toPoly (a₂.subst σ)) (toPoly_nonempty _) (fun _ h => toPoly_card_pos _ h) (Or.inr h2)
          rw [ha, hb]
      · intro σ P hP hPp h
        simp only [SemiringTerm.subst, toPoly] at h ⊢
        have hpos_mul : ∀ {A B : Poly}, (∀ q ∈ A, 1 ≤ q.card) → (∀ q ∈ B, 1 ≤ q.card) →
            ∀ q ∈ mulPoly A B, 1 ≤ q.card := fun hA hB q hq => by
          obtain ⟨q1, h1, q2, h2, rfl⟩ := mem_mulPoly.mp hq
          have := hA q1 h1; have := hB q2 h2; simp; omega
        rcases h with h1 | h2
        · have ha : (toPoly (a₁.subst σ)) = (toPoly (a₂.subst σ)) :=
            ih1.2 σ (mulPoly P (toPoly (b₁.subst σ)))
              (mulPoly_nonempty hP (toPoly_nonempty _))
              (hpos_mul hPp (fun _ h => toPoly_card_pos _ h))
              (Or.inl (by rw [mulPoly_assoc, mulPoly_comm (toPoly (b₁.subst σ))]; exact h1))
          have hb : (toPoly (b₁.subst σ)) = (toPoly (b₂.subst σ)) :=
            ih2.2 σ (mulPoly P (toPoly (a₁.subst σ)))
              (mulPoly_nonempty hP (toPoly_nonempty _))
              (hpos_mul hPp (fun _ h => toPoly_card_pos _ h))
              (Or.inl (by rw [mulPoly_assoc]; exact h1))
          rw [ha, hb]
        · have ha : (toPoly (a₁.subst σ)) = (toPoly (a₂.subst σ)) :=
            ih1.2 σ (mulPoly P (toPoly (b₂.subst σ)))
              (mulPoly_nonempty hP (toPoly_nonempty _))
              (hpos_mul hPp (fun _ h => toPoly_card_pos _ h))
              (Or.inr (by rw [mulPoly_assoc, mulPoly_comm (toPoly (b₂.subst σ))]; exact h2))
          have hb : (toPoly (b₁.subst σ)) = (toPoly (b₂.subst σ)) :=
            ih2.2 σ (mulPoly P (toPoly (a₂.subst σ)))
              (mulPoly_nonempty hP (toPoly_nonempty _))
              (hpos_mul hPp (fun _ h => toPoly_card_pos _ h))
              (Or.inr (by rw [mulPoly_assoc]; exact h2))
          rw [ha, hb]
    | @subst a b τ _ ih =>
      have hcomp_subst : ∀ (t : SemiringTerm) (σ : ℕ → SemiringTerm),
          (t.subst τ).subst σ = t.subst (fun x => (τ x).subst σ) := fun t σ => by
        induction t with
        | var _ => rfl
        | add _ _ ih1 ih2 => simp [SemiringTerm.subst, ih1, ih2]
        | mul _ _ ih1 ih2 => simp [SemiringTerm.subst, ih1, ih2]
      exact ⟨fun σ h => by rw [hcomp_subst, hcomp_subst] at h ⊢; exact ih.1 _ h,
             fun σ P hP hPp h => by rw [hcomp_subst, hcomp_subst] at h ⊢; exact ih.2 _ P hP hPp h⟩
  -- Apply `hinv hder` with `σ = SemiringTerm.var`: gives `(toPoly w) = (toPoly (w + z))`, contradiction!
  have hid_subst : ∀ t : SemiringTerm, t.subst SemiringTerm.var = t := fun t => by
    induction t with
    | var _ => rfl
    | add _ _ ih1 ih2 => simp [SemiringTerm.subst, ih1, ih2]
    | mul _ _ ih1 ih2 => simp [SemiringTerm.subst, ih1, ih2]
  have heq := (hinv hder).1 SemiringTerm.var (Or.inl (by rw [hid_subst]))
  rw [hid_subst, hid_subst] at heq
  have hz_mem : ({2 * K + 1} : Mon) ∈ (toPoly w) := by
    rw [heq]; simp [z, toPoly]
  obtain ⟨a, b, hab, _⟩ := hw_poly _ hz_mem
  have := congrArg Multiset.card hab
  simp at this

private theorem main_proof :
    (∀ add : Elem6 → Elem6 → Elem6, IsCompatAdd add ↔ ∃ i j : Fin 3, add = addR i j) ∧
    (Function.Injective fun p : Fin 3 × Fin 3 => addR p.1 p.2) ∧
    (∀ i j i' j' : Fin 3, AddIso (addR i j) (addR i' j') ↔ (i = i' ∧ j = j') ∨ (i = j' ∧ j = i')) ∧
    IsEquationalBasis 0 1 basis01 ∧
    IsEquationalBasis 0 2 basis02 ∧
    IsEquationalBasis 1 1 basis11 ∧
    IsEquationalBasis 1 2 basis12 ∧
    ¬ IsFinitelyBased 0 1 ∧
    ¬ IsFinitelyBased 0 2 ∧
    ¬ IsFinitelyBased 1 1 ∧
    ¬ IsFinitelyBased 1 2 :=
  ⟨fun add => ⟨compat_eq_addR, by rintro ⟨i, j, rfl⟩; exact addR_compat i j⟩,
   addR_injective,
   addIso_iff,
   ⟨basis01_sound, basis01_complete⟩,
   ⟨basis02_sound, basis02_complete⟩,
   ⟨basis11_sound, basis11_complete⟩,
   ⟨basis12_sound, basis12_complete⟩,
   not_finitely_based (Or.inl ⟨rfl, rfl⟩),
   not_finitely_based (Or.inr (Or.inl ⟨rfl, rfl⟩)),
   not_finitely_based (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))),
   not_finitely_based (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩

end OMA.P_arxiv_2609_22667

theorem OMA.solution : type_of% @OMA.S_arxiv_2609_22667.main :=
  OMA.P_arxiv_2609_22667.main_proof
