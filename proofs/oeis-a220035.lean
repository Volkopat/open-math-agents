import OMAStatements.S_oeis_a220035

/-!
# Proof of OEIS A220035

We prove the generating function and linear recurrence for `OMA.S_oeis_a220035.a n`, the number of
distinct 5 x n 0-1 arrays obtained as horizontal-and-main-diagonal neighbor minima of sorted 5 x n
0-1 arrays.

Outline:
1. A 5 x n 0-1 array `A` is `IsSorted` iff there exists a monotone threshold tuple
   `t : Fin 5 → ℕ` with `t i ≤ n` such that `A i j = decide (j.val < t i)`.
2. On such a threshold array `gridOf n t`, the neighbor minimum `minArray (gridOf n t)` is again
   a threshold array `gridOf n (sOf n t)`, where
   `sOf n t i = min (shrink n (t i)) (min n (t (i - 1) + 1))` (with `shrink n x = if x = n then n else x - 1`,
   and no previous-row constraint at `i = 0`).
3. Since `gridOf n` is injective on tuples bounded by `n`, `a n` equals the cardinality of the
   image `S 5 n` of `sOf n` over monotone 5-tuples in `{0, ..., n}`.
4. Introducing auxiliary k-row image sets `H k n`, `G k n`, `F k n`, and `S0 k n`, we establish
   exact shift-bijection recurrences in `k` and `n`, solve them in closed form to obtain
   `24 * a n + 2 * n^3 + 3168 = n^4 + 95 * n^2 + 578 * n` for all `n ≥ 7` along with the exact
   values for `1 ≤ n ≤ 11`, and deduce both the generating function identity and the 5th-order
   linear recurrence for `n > 11`.
-/

namespace OMA.P_oeis_a220035

open OMA.S_oeis_a220035
open PowerSeries

/-! ## Section 1: Threshold characterization of `IsSorted` and `minArray` -/

private def gridOf (n : ℕ) (t : Fin 5 → ℕ) : Grid n :=
  fun i j => decide (j.val < t i)

private def shrink (n x : ℕ) : ℕ :=
  if x = n then n else x - 1

private def sOf {k : ℕ} (n : ℕ) (t : Fin k → ℕ) : Fin k → ℕ :=
  fun i =>
    if h : i.val = 0 then shrink n (t i)
    else min (shrink n (t i)) (min n (t ⟨i.val - 1, by omega⟩ + 1))

private def sOfPrev {k : ℕ} (n : ℕ) (t0 : ℕ) (t : Fin k → ℕ) : Fin k → ℕ :=
  fun i =>
    min (shrink n (t i))
      (min n ((if h : i.val = 0 then t0 else t ⟨i.val - 1, by omega⟩) + 1))

private lemma shrink_le (n x : ℕ) (hx : x ≤ n) : shrink n x ≤ n := by
  unfold shrink; split_ifs <;> omega

private lemma shrink_le_self (n x : ℕ) : shrink n x ≤ x := by
  unfold shrink; split_ifs <;> omega

private lemma sOf_le {k : ℕ} (n : ℕ) (t : Fin k → ℕ) (ht : ∀ i, t i ≤ n) (i : Fin k) :
    sOf n t i ≤ n := by
  unfold sOf
  split_ifs
  · exact shrink_le n (t i) (ht i)
  · exact le_trans (min_le_left _ _) (shrink_le n (t i) (ht i))

private lemma ofFn_le_of_pointwise {m : ℕ} {f g : Fin m → Bool} (hfg : ∀ i, f i ≤ g i) :
    List.ofFn f ≤ List.ofFn g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.ofFn_succ, ← not_lt]
    intro hlt
    have h0 := hfg 0
    cases hf : f 0 <;> cases hg : g 0
    · rw [hf, hg] at hlt
      cases hlt with
      | rel h => exact absurd h (by decide)
      | cons htail =>
        have hih := ih (fun i => hfg i.succ)
        rw [← not_lt] at hih
        exact hih htail
    · rw [hf, hg] at hlt
      cases hlt with
      | rel h => exact absurd h (by decide)
    · rw [hf, hg] at h0
      exact absurd h0 (by decide)
    · rw [hf, hg] at hlt
      cases hlt with
      | rel h => exact absurd h (by decide)
      | cons htail =>
        have hih := ih (fun i => hfg i.succ)
        rw [← not_lt] at hih
        exact hih htail

private lemma ofFn_le_exists_lt {m : ℕ} {f g : Fin m → Bool} (h : List.ofFn f ≤ List.ofFn g)
    {k : Fin m} (hf : f k = true) (hg : g k = false) :
    ∃ p : Fin m, p < k ∧ f p = false ∧ g p = true := by
  induction m with
  | zero => exact Fin.elim0 k
  | succ m ih =>
    rw [List.ofFn_succ, List.ofFn_succ, ← not_lt] at h
    refine Fin.cases ?_ ?_ k hf hg
    · intro hf0 hg0
      exfalso
      apply h
      rw [hf0, hg0]
      exact List.Lex.rel (by decide)
    · intro k' hfk hgk
      cases hf0 : f 0 <;> cases hg0 : g 0
      · have htail : List.ofFn (f ∘ Fin.succ) ≤ List.ofFn (g ∘ Fin.succ) := by
          rw [← not_lt]
          intro hlt
          apply h
          rw [hf0, hg0]
          exact List.Lex.cons hlt
        obtain ⟨p, hpk, hfp, hgp⟩ := ih htail hfk hgk
        exact ⟨p.succ, Fin.succ_lt_succ_iff.mpr hpk, hfp, hgp⟩
      · exact ⟨0, Fin.succ_pos k', hf0, hg0⟩
      · exfalso
        apply h
        rw [hf0, hg0]
        exact List.Lex.rel (by decide)
      · have htail : List.ofFn (f ∘ Fin.succ) ≤ List.ofFn (g ∘ Fin.succ) := by
          rw [← not_lt]
          intro hlt
          apply h
          rw [hf0, hg0]
          exact List.Lex.cons hlt
        obtain ⟨p, hpk, hfp, hgp⟩ := ih htail hfk hgk
        exact ⟨p.succ, Fin.succ_lt_succ_iff.mpr hpk, hfp, hgp⟩

private lemma isSorted_aux {n : ℕ} {A : Grid n} (hA : IsSorted A) :
    ∀ i : ℕ, ∀ hi : i < 5,
      (∀ i' : Fin 5, i'.val < i → ∀ j : Fin n, A i' j = true → A ⟨i, hi⟩ j = true) ∧
      (∀ j₁ j₂ : Fin n, j₁ ≤ j₂ → A ⟨i, hi⟩ j₂ = true → A ⟨i, hi⟩ j₁ = true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    have hdom : ∀ i' : Fin 5, i'.val < i → ∀ j : Fin n, A i' j = true → A ⟨i, hi⟩ j = true := by
      intro i' hi' j h1
      by_contra h2
      have h2f : A ⟨i, hi⟩ j = false := by
        cases hval : A ⟨i, hi⟩ j <;> simp_all
      have hrow : row A i' ≤ row A ⟨i, hi⟩ := hA.1 i' ⟨i, hi⟩ (Fin.mk_le_mk.mpr (le_of_lt hi'))
      obtain ⟨p, hpj, hp1, _⟩ := ofFn_le_exists_lt hrow h1 h2f
      have hanti := (ih i'.val hi' i'.isLt).2 p j (le_of_lt hpj) h1
      simp [hp1] at hanti
    refine ⟨hdom, ?_⟩
    intro j₁ j₂ hj h2
    by_contra h1
    have h1f : A ⟨i, hi⟩ j₁ = false := by
      cases hval : A ⟨i, hi⟩ j₁ <;> simp_all
    have hcol : col A j₂ ≤ col A j₁ := hA.2 j₁ j₂ hj
    obtain ⟨i', hi'i, _, hi'1⟩ := ofFn_le_exists_lt hcol h2 h1f
    have := hdom i' hi'i j₁ hi'1
    simp [h1f] at this

private lemma antitone_bool_eq_decide_lt {n : ℕ} (f : Fin n → Bool)
    (hanti : ∀ j₁ j₂ : Fin n, j₁ ≤ j₂ → f j₂ = true → f j₁ = true) :
    ∃ t : ℕ, t ≤ n ∧ ∀ j : Fin n, f j = decide (j.val < t) := by
  let S := Finset.univ.filter (fun j : Fin n => f j = true)
  refine ⟨S.card, le_trans (Finset.card_filter_le _ _) (by simp), ?_⟩
  have hmem : ∀ j : Fin n, f j = true ↔ j.val < S.card := by
    intro j
    constructor
    · intro hj
      have hsub : Finset.univ.filter (fun k : Fin n => k.val ≤ j.val) ⊆ S := by
        intro k hk
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        exact hanti k j (Fin.mk_le_mk.mpr hk) hj
      have hcard_le := Finset.card_le_card hsub
      have hcard_eq : (Finset.univ.filter (fun k : Fin n => k.val ≤ j.val)).card = j.val + 1 := by
        have hbij : Finset.univ.filter (fun k : Fin n => k.val ≤ j.val) =
            (Finset.range (j.val + 1)).attach.image (fun x => ⟨x.1, by
              have hx := Finset.mem_range.mp x.2; omega⟩) := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
            Finset.mem_attach, Subtype.exists, Finset.mem_range]
          constructor
          · intro hk; exact ⟨k.val, by omega, rfl⟩
          · rintro ⟨x, hx, rfl⟩; dsimp; omega
        rw [hbij, Finset.card_image_of_injective]
        · simp
        · intro x y hxy
          exact Subtype.ext (congrArg Fin.val hxy)
      omega
    · intro hj
      by_contra hf
      have hff : f j = false := by cases hv : f j <;> simp_all
      have hsub : S ⊆ Finset.univ.filter (fun k : Fin n => k.val < j.val) := by
        intro k hk
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        by_contra hge
        have hle : j ≤ k := Fin.mk_le_mk.mpr (Nat.le_of_not_lt hge)
        have := hanti j k hle hk
        simp [hff] at this
      have hcard_le := Finset.card_le_card hsub
      have hcard_eq : (Finset.univ.filter (fun k : Fin n => k.val < j.val)).card = j.val := by
        have hbij : Finset.univ.filter (fun k : Fin n => k.val < j.val) =
            (Finset.range j.val).attach.image (fun x => ⟨x.1, by
              have hx := Finset.mem_range.mp x.2; omega⟩) := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
            Finset.mem_attach, Subtype.exists, Finset.mem_range]
          constructor
          · intro hk; exact ⟨k.val, hk, rfl⟩
          · rintro ⟨x, hx, rfl⟩; exact hx
        rw [hbij, Finset.card_image_of_injective]
        · simp
        · intro x y hxy
          exact Subtype.ext (congrArg Fin.val hxy)
      omega
  intro j
  cases hv : f j
  · symm
    simp only [decide_eq_false_iff_not]
    intro hlt
    have := (hmem j).mpr hlt
    simp [hv] at this
  · symm
    simp only [decide_eq_true_eq]
    exact (hmem j).mp hv

private lemma isSorted_iff {n : ℕ} (A : Grid n) :
    IsSorted A ↔ ∃ t : Fin 5 → ℕ, (∀ i, t i ≤ n) ∧ Monotone t ∧ A = gridOf n t := by
  constructor
  · intro hA
    have haux := isSorted_aux hA
    have hex : ∀ i : Fin 5, ∃ t : ℕ, t ≤ n ∧ ∀ j : Fin n, A i j = decide (j.val < t) :=
      fun i => antitone_bool_eq_decide_lt (A i) (haux i.val i.isLt).2
    choose t ht_le ht_eq using hex
    refine ⟨t, ht_le, ?_, ?_⟩
    · intro i₁ i₂ hi
      by_cases heq : i₁ = i₂
      · subst heq; exact le_rfl
      · have hlt : i₁.val < i₂.val := lt_of_le_of_ne hi (fun h => heq (Fin.ext h))
        by_contra hgt
        have hlt2 : t i₂ < t i₁ := Nat.lt_of_not_le hgt
        let j : Fin n := ⟨t i₂, lt_of_lt_of_le hlt2 (ht_le i₁)⟩
        have h1 : A i₁ j = true := by rw [ht_eq i₁ j]; simp [j, hlt2]
        have h2 : A i₂ j = true := (haux i₂.val i₂.isLt).1 i₁ hlt j h1
        rw [ht_eq i₂ j] at h2
        simp [j] at h2
    · funext i j
      exact ht_eq i j
  · rintro ⟨t, _, hmono, rfl⟩
    constructor
    · intro i₁ i₂ hi
      apply ofFn_le_of_pointwise
      intro j
      simp only [gridOf]
      by_cases h1 : j.val < t i₁
      · have h2 : j.val < t i₂ := lt_of_lt_of_le h1 (hmono hi)
        simp [h1, h2]
      · simp [h1]
    · intro j₁ j₂ hj
      apply ofFn_le_of_pointwise
      intro i
      simp only [gridOf]
      by_cases h2 : j₂.val < t i
      · have h1 : j₁.val < t i := lt_of_le_of_lt hj h2
        simp [h1, h2]
      · simp [h2]

private lemma minArray_gridOf {n : ℕ} (t : Fin 5 → ℕ) (ht : ∀ i, t i ≤ n) (hmono : Monotone t) :
    minArray (gridOf n t) = gridOf n (sOf n t) := by
  funext i j
  simp only [minArray, gridOf, decide_eq_true_eq, decide_eq_decide]
  constructor
  · intro hall
    have hself : j.val < t i := hall i j (Or.inl ⟨rfl, Or.inl rfl⟩)
    have hshrink : j.val < shrink n (t i) := by
      unfold shrink
      split_ifs with htn
      · omega
      · by_cases hjn : j.val + 1 < n
        · have hr := hall i ⟨j.val + 1, hjn⟩ (Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩)
          dsimp only at hr; omega
        · have := ht i; omega
    unfold sOf
    split_ifs with hi0
    · exact hshrink
    · refine lt_min hshrink (lt_min j.isLt ?_)
      by_cases hj0 : j.val = 0
      · omega
      · have hdiag := hall ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩
          (Or.inr (Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩))
        dsimp only at hdiag; omega
  · intro hs i' j' hnear
    have hshrink : j.val < shrink n (t i) := by
      unfold sOf at hs
      split_ifs at hs
      · exact hs
      · exact lt_of_lt_of_le hs (min_le_left _ _)
    have hj_ti : j.val < t i := lt_of_lt_of_le hshrink (shrink_le_self n (t i))
    rcases hnear with ⟨rfl, rfl | hjl | hjr⟩ | ⟨hi', hj'⟩ | ⟨hi', hj'⟩
    · exact hj_ti
    · omega
    · unfold shrink at hshrink
      split_ifs at hshrink with htn
      · omega
      · omega
    · unfold sOf at hs
      have hi0 : ¬ i.val = 0 := by omega
      rw [dif_neg hi0] at hs
      have hprev : j.val < t ⟨i.val - 1, by omega⟩ + 1 :=
        lt_of_lt_of_le (lt_of_lt_of_le hs (min_le_right _ _)) (min_le_right _ _)
      have heq : i' = ⟨i.val - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
      rw [heq]; omega
    · have hjr : j'.val < t i := by
        unfold shrink at hshrink
        split_ifs at hshrink with htn
        · omega
        · omega
      have hle : i ≤ i' := Fin.mk_le_mk.mpr (by omega)
      exact lt_of_lt_of_le hjr (hmono hle)

private lemma gridOf_injOn (n : ℕ) :
    Set.InjOn (gridOf n) {s : Fin 5 → ℕ | ∀ i, s i ≤ n} := by
  intro s₁ hs₁ s₂ hs₂ hgrid
  funext i
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · let j : Fin n := ⟨s₁ i, lt_of_lt_of_le hlt (hs₂ i)⟩
    have h := congrFun (congrFun hgrid i) j
    simp [gridOf, j, hlt] at h
  · let j : Fin n := ⟨s₂ i, lt_of_lt_of_le hgt (hs₁ i)⟩
    have h := congrFun (congrFun hgrid i) j
    simp [gridOf, j, hgt] at h

/-! ## Section 2: Auxiliary image sets `S`, `F`, `H`, `G`, `S0` and shift lemmas -/

private def liftFin {k n : ℕ} (t : Fin k → Fin (n + 1)) : Fin k → ℕ :=
  fun i => (t i).val

private def S (k n : ℕ) : Finset (Fin k → ℕ) :=
  (Finset.univ.filter fun t : Fin k → Fin (n + 1) => Monotone t).image
    (fun t => sOf n (liftFin t))

private def F (k n : ℕ) : Finset (Fin k → ℕ) :=
  (Finset.univ.filter fun t : Fin k → Fin (n + 1) => Monotone t ∧ ∀ i, 2 ≤ (t i).val).image
    (fun t => sOf n (liftFin t))

private def H (k n : ℕ) : Finset (Fin k → ℕ) :=
  if 2 ≤ n then
    (Finset.univ.filter fun t : Fin k → Fin (n + 1) => Monotone t ∧ ∀ i, 2 ≤ (t i).val).image
      (fun t => sOfPrev n 2 (liftFin t))
  else ∅

private def G (k n : ℕ) : Finset (Fin k → ℕ) :=
  (Finset.univ.filter fun p : Fin (n + 1) × (Fin k → Fin (n + 1)) =>
    2 ≤ p.1.val ∧ Monotone p.2 ∧ ∀ i, p.1 ≤ p.2 i).image
    (fun p => sOfPrev n p.1.val (liftFin p.2))

private def S0 (k n : ℕ) : Finset (Fin (k + 1) → ℕ) :=
  (S (k + 1) n).filter (fun s => s 0 = 0)

private def shift {k : ℕ} (d : ℕ) (s : Fin k → ℕ) : Fin k → ℕ :=
  fun i => s i + d

private def vcons {k : ℕ} (c : ℕ) (r : Fin k → ℕ) : Fin (k + 1) → ℕ :=
  Fin.cons c r

@[simp] private lemma vcons_zero {k : ℕ} (c : ℕ) (r : Fin k → ℕ) : vcons c r 0 = c :=
  rfl

@[simp] private lemma vcons_succ {k : ℕ} (c : ℕ) (r : Fin k → ℕ) (i : Fin k) :
    vcons c r i.succ = r i :=
  Fin.cons_succ (α := fun _ => ℕ) c r i

@[simp] private lemma vcons_one {k : ℕ} (c : ℕ) (r : Fin (k + 1) → ℕ) :
    vcons c r 1 = r 0 := by
  change vcons c r (Fin.succ 0) = r 0
  exact vcons_succ c r 0

private lemma vcons_self_tail {k : ℕ} (t : Fin (k + 1) → ℕ) :
    vcons (t 0) (Fin.tail t) = t :=
  Fin.cons_self_tail t

private lemma shift_injective {k : ℕ} (d : ℕ) : Function.Injective (@shift k d) := by
  intro s₁ s₂ h
  funext i
  have := congrFun h i
  simp only [shift] at this
  omega

private lemma vcons_injective {k : ℕ} (c : ℕ) : Function.Injective (@vcons k c) := by
  intro r₁ r₂ h
  funext i
  have := congrFun h i.succ
  simpa using this

private lemma mem_S {k n : ℕ} {s : Fin k → ℕ} :
    s ∈ S k n ↔ ∃ t : Fin k → ℕ, (∀ i, t i ≤ n) ∧ Monotone t ∧ s = sOf n t := by
  simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, hmono, rfl⟩
    exact ⟨liftFin t, fun i => Nat.lt_succ_iff.mp (t i).isLt, fun i j hij => hmono hij, rfl⟩
  · rintro ⟨t, hle, hmono, rfl⟩
    refine ⟨fun i => ⟨t i, Nat.lt_succ_of_le (hle i)⟩, fun i j hij => hmono hij, rfl⟩

private lemma mem_F {k n : ℕ} {s : Fin k → ℕ} :
    s ∈ F k n ↔
      ∃ t : Fin k → ℕ, (∀ i, 2 ≤ t i ∧ t i ≤ n) ∧ Monotone t ∧ s = sOf n t := by
  simp only [F, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ⟨hmono, h2⟩, rfl⟩
    exact ⟨liftFin t, fun i => ⟨h2 i, Nat.lt_succ_iff.mp (t i).isLt⟩, fun i j hij => hmono hij, rfl⟩
  · rintro ⟨t, hbd, hmono, rfl⟩
    refine ⟨fun i => ⟨t i, Nat.lt_succ_of_le (hbd i).2⟩,
      ⟨fun i j hij => hmono hij, fun i => (hbd i).1⟩, rfl⟩

private lemma mem_H {k n : ℕ} {s : Fin k → ℕ} :
    s ∈ H k n ↔
      2 ≤ n ∧ ∃ t : Fin k → ℕ, (∀ i, 2 ≤ t i ∧ t i ≤ n) ∧ Monotone t ∧ s = sOfPrev n 2 t := by
  unfold H
  split_ifs with hn
  · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, hn, true_and]
    constructor
    · rintro ⟨t, ⟨hmono, h2⟩, rfl⟩
      exact ⟨liftFin t, fun i => ⟨h2 i, Nat.lt_succ_iff.mp (t i).isLt⟩,
        fun i j hij => hmono hij, rfl⟩
    · rintro ⟨t, hbd, hmono, rfl⟩
      refine ⟨fun i => ⟨t i, Nat.lt_succ_of_le (hbd i).2⟩,
        ⟨fun i j hij => hmono hij, fun i => (hbd i).1⟩, rfl⟩
  · simp [hn]

private lemma mem_G {k n : ℕ} {s : Fin k → ℕ} :
    s ∈ G k n ↔
      ∃ t0 : ℕ, 2 ≤ t0 ∧ t0 ≤ n ∧
        ∃ t : Fin k → ℕ, (∀ i, t0 ≤ t i ∧ t i ≤ n) ∧ Monotone t ∧ s = sOfPrev n t0 t := by
  simp only [G, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨t0, t⟩, ⟨ht0, hmono, hle⟩, rfl⟩
    exact ⟨t0.val, ht0, Nat.lt_succ_iff.mp t0.isLt, liftFin t,
      fun i => ⟨hle i, Nat.lt_succ_iff.mp (t i).isLt⟩, fun i j hij => hmono hij, rfl⟩
  · rintro ⟨t0, ht0, ht0n, t, hbd, hmono, rfl⟩
    refine ⟨(⟨t0, Nat.lt_succ_of_le ht0n⟩, fun i => ⟨t i, Nat.lt_succ_of_le (hbd i).2⟩),
      ⟨ht0, fun i j hij => hmono hij, fun i => (hbd i).1⟩, rfl⟩

private lemma mem_S0 {k n : ℕ} {s : Fin (k + 1) → ℕ} :
    s ∈ S0 k n ↔ s ∈ S (k + 1) n ∧ s 0 = 0 := by
  simp [S0]

private lemma a_eq_card_S (n : ℕ) : a n = (S 5 n).card := by
  unfold a
  have hImg : (Finset.univ.filter fun A : Grid n => IsSorted A).image minArray =
      (S 5 n).image (gridOf n) := by
    ext B
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, mem_S]
    constructor
    · rintro ⟨A, hA, rfl⟩
      obtain ⟨t, ht_le, hmono, rfl⟩ := (isSorted_iff A).mp hA
      exact ⟨sOf n t, ⟨t, ht_le, hmono, rfl⟩, (minArray_gridOf t ht_le hmono).symm⟩
    · rintro ⟨s, ⟨t, ht_le, hmono, rfl⟩, rfl⟩
      refine ⟨gridOf n t, (isSorted_iff _).mpr ⟨t, ht_le, hmono, rfl⟩,
        minArray_gridOf t ht_le hmono⟩
  rw [hImg, Finset.card_image_of_injOn]
  intro s₁ hs₁ s₂ hs₂ h
  obtain ⟨t₁, ht₁, _, rfl⟩ := mem_S.mp hs₁
  obtain ⟨t₂, ht₂, _, rfl⟩ := mem_S.mp hs₂
  exact gridOf_injOn n (sOf_le n t₁ ht₁) (sOf_le n t₂ ht₂) h

private lemma shrink_shift (n d x : ℕ) (hx : 2 ≤ x) :
    shrink (n + d) (x + d) = shrink n x + d := by
  unfold shrink
  split_ifs <;> omega

private lemma sOf_shift {k : ℕ} (n d : ℕ) (t : Fin k → ℕ) (ht : ∀ i, 2 ≤ t i) :
    sOf (n + d) (shift d t) = shift d (sOf n t) := by
  funext i
  simp only [sOf, shift]
  split_ifs
  · exact shrink_shift n d (t i) (ht i)
  · rw [shrink_shift n d (t i) (ht i)]
    omega

private lemma sOfPrev_shift {k : ℕ} (n d t0 : ℕ) (t : Fin k → ℕ) (ht : ∀ i, 2 ≤ t i) :
    sOfPrev (n + d) (t0 + d) (shift d t) = shift d (sOfPrev n t0 t) := by
  funext i
  simp only [sOfPrev, shift]
  rw [shrink_shift n d (t i) (ht i)]
  split_ifs <;> omega

private lemma sOf_vcons {k : ℕ} (n : ℕ) (t0 : ℕ) (t : Fin k → ℕ) :
    sOf n (vcons t0 t) = vcons (shrink n t0) (sOfPrev n t0 t) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [sOf]
  · intro j
    simp only [sOf, sOfPrev, vcons_succ]
    have hj0 : ¬ (j.succ).val = 0 := by simp
    rw [dif_neg hj0]
    by_cases h : j.val = 0
    · rw [dif_pos h]
      have hidx : (⟨j.succ.val - 1, by omega⟩ : Fin (k + 1)) = 0 := Fin.ext (by simp [h])
      rw [hidx, vcons_zero]
    · rw [dif_neg h]
      have hidx : (⟨j.succ.val - 1, by omega⟩ : Fin (k + 1)) = (⟨j.val - 1, by omega⟩ : Fin k).succ :=
        Fin.ext (by simp; omega)
      rw [hidx, vcons_succ]

private lemma sOfPrev_vcons {k : ℕ} (n t0 t1 : ℕ) (t : Fin k → ℕ) :
    sOfPrev n t0 (vcons t1 t) =
      vcons (min (shrink n t1) (min n (t0 + 1))) (sOfPrev n t1 t) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [sOfPrev]
  · intro j
    simp only [sOfPrev, vcons_succ]
    have hj0 : ¬ (j.succ).val = 0 := by simp
    rw [dif_neg hj0]
    by_cases h : j.val = 0
    · rw [dif_pos h]
      have hidx : (⟨j.succ.val - 1, by omega⟩ : Fin (k + 1)) = 0 := Fin.ext (by simp [h])
      rw [hidx, vcons_zero]
    · rw [dif_neg h]
      have hidx : (⟨j.succ.val - 1, by omega⟩ : Fin (k + 1)) = (⟨j.val - 1, by omega⟩ : Fin k).succ :=
        Fin.ext (by simp; omega)
      rw [hidx, vcons_succ]

private lemma mono_vcons_iff {k : ℕ} {a : ℕ} {t : Fin k → ℕ} :
    Monotone (vcons a t) ↔ (∀ i, a ≤ t i) ∧ Monotone t := by
  constructor
  · intro h
    exact ⟨fun i => h (Fin.zero_le i.succ), fun i j hij => h (Fin.succ_le_succ_iff.mpr hij)⟩
  · rintro ⟨ha, ht⟩ i j hij
    refine Fin.cases ?_ ?_ i hij
    · intro _
      refine Fin.cases (by simp) (fun j' => by simp [ha j']) j
    · intro i' hi
      refine Fin.cases ?_ ?_ j hi
      · intro h0
        exfalso
        have := Fin.le_iff_val_le_val.mp h0
        simp at this
      · intro j' hij'
        exact ht (Fin.succ_le_succ_iff.mp hij')

/-! ## Section 3: Exact cardinality recurrences and base cases -/

private lemma card_H_zero (n : ℕ) (hn : 2 ≤ n) : (H 0 n).card = 1 := by
  have heq : H 0 n = {Fin.elim0} := by
    ext s
    rw [mem_H, Finset.mem_singleton]
    constructor
    · intro _; funext i; exact Fin.elim0 i
    · rintro rfl
      refine ⟨hn, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
      funext i; exact Fin.elim0 i
  rw [heq, Finset.card_singleton]

private lemma card_G_zero (n : ℕ) (hn : 2 ≤ n) : (G 0 n).card = 1 := by
  have heq : G 0 n = {Fin.elim0} := by
    ext s
    rw [mem_G, Finset.mem_singleton]
    constructor
    · intro _; funext i; exact Fin.elim0 i
    · rintro rfl
      refine ⟨2, le_rfl, hn, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
      funext i; exact Fin.elim0 i
  rw [heq, Finset.card_singleton]

private lemma card_G_two (k : ℕ) : (G k 2).card = 1 := by
  have heq : G k 2 = {fun _ => 2} := by
    ext s
    rw [mem_G, Finset.mem_singleton]
    constructor
    · rintro ⟨t0, ht0, ht0n, t, hbd, _, rfl⟩
      have ht02 : t0 = 2 := by omega
      funext i
      have hti : t i = 2 := by have := hbd i; omega
      simp only [sOfPrev, hti, ht02, shrink, ↓reduceIte]
      split_ifs with h
      · omega
      · have hprev : t ⟨i.val - 1, by omega⟩ = 2 := by have := hbd ⟨i.val - 1, by omega⟩; omega
        omega
    · rintro rfl
      refine ⟨2, le_rfl, le_rfl, fun _ => 2, fun _ => ⟨le_rfl, le_rfl⟩, fun _ _ _ => le_rfl, ?_⟩
      funext i
      simp only [sOfPrev, shrink, ↓reduceIte]
      split_ifs <;> omega
  rw [heq, Finset.card_singleton]

private lemma card_F_two (k : ℕ) : (F k 2).card = 1 := by
  have heq : F k 2 = {fun _ => 2} := by
    ext s
    rw [mem_F, Finset.mem_singleton]
    constructor
    · rintro ⟨t, hbd, _, rfl⟩
      funext i
      have hti : t i = 2 := by have := hbd i; omega
      simp only [sOf, hti, shrink, ↓reduceIte]
      split_ifs with h
      · rfl
      · have hprev : t ⟨i.val - 1, by omega⟩ = 2 := by have := hbd ⟨i.val - 1, by omega⟩; omega
        omega
    · rintro rfl
      refine ⟨fun _ => 2, fun _ => ⟨le_rfl, le_rfl⟩, fun _ _ _ => le_rfl, ?_⟩
      funext i
      simp only [sOf, shrink, ↓reduceIte]
      split_ifs <;> omega
  rw [heq, Finset.card_singleton]

private lemma G_three_eq_H_three (k : ℕ) : G k 3 = H k 3 := by
  ext s
  rw [mem_G, mem_H]
  constructor
  · rintro ⟨t0, ht0, ht0n, t, hbd, hmono, rfl⟩
    refine ⟨by omega, t, fun i => ⟨by have := hbd i; omega, (hbd i).2⟩, hmono, ?_⟩
    funext i
    simp only [sOfPrev]
    split_ifs with hi0
    · have h1 := hbd i
      unfold shrink
      split_ifs <;> omega
    · rfl
  · rintro ⟨_, t, hbd, hmono, rfl⟩
    exact ⟨2, le_rfl, by omega, t, hbd, hmono, rfl⟩

private lemma card_H_three (k : ℕ) : (H k 3).card = k + 1 := by
  induction k with
  | zero => exact card_H_zero 3 (by omega)
  | succ k ih =>
    have hsplit : H (k + 1) 3 = (H k 3).image (vcons 1) ∪ {fun _ => 3} := by
      ext s
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, mem_H]
      constructor
      · rintro ⟨_, t, hbd, hmono, rfl⟩
        have ht0 := hbd 0
        have hcases : t 0 = 2 ∨ t 0 = 3 := by omega
        rcases hcases with h2 | h3
        · left
          refine ⟨sOfPrev 3 2 (Fin.tail t), ⟨by omega, Fin.tail t, fun i => hbd i.succ,
            fun i j hij => hmono (Fin.succ_le_succ_iff.mpr hij), rfl⟩, ?_⟩
          have hcons : t = vcons (t 0) (Fin.tail t) := (vcons_self_tail t).symm
          conv_rhs => rw [hcons, sOfPrev_vcons, h2]
          simp [shrink]
        · right
          funext i
          have hti : t i = 3 := by
            have := hmono (Fin.zero_le i)
            have := hbd i
            omega
          simp only [sOfPrev, hti, shrink, ↓reduceIte]
          split_ifs with h
          · omega
          · have hprev : t ⟨i.val - 1, by omega⟩ = 3 := by
              have := hmono (Fin.zero_le ⟨i.val - 1, by omega⟩)
              have := hbd ⟨i.val - 1, by omega⟩
              omega
            omega
      · rintro (⟨r, ⟨_, t, hbd, hmono, rfl⟩, rfl⟩ | rfl)
        · refine ⟨by omega, vcons 2 t, ?_, mono_vcons_iff.mpr ⟨fun i => (hbd i).1, hmono⟩, ?_⟩
          · intro i; refine Fin.cases (by simp) (fun j => hbd j) i
          · rw [sOfPrev_vcons]; simp [shrink]
        · refine ⟨by omega, fun _ => 3, fun _ => by dsimp; omega, fun _ _ _ => le_rfl, ?_⟩
          funext i
          simp only [sOfPrev, shrink, ↓reduceIte]
          split_ifs <;> omega
    have hdisj : Disjoint ((H k 3).image (vcons 1)) {fun _ => 3} := by
      rw [Finset.disjoint_singleton_right]
      simp only [Finset.mem_image]
      rintro ⟨r, _, h⟩
      have := congrFun h 0
      simp at this
    rw [hsplit, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (vcons_injective 1), Finset.card_singleton, ih]

private lemma card_G_three (k : ℕ) : (G k 3).card = k + 1 := by
  rw [G_three_eq_H_three, card_H_three]

private lemma card_H_succ (k n : ℕ) (hn : 4 ≤ n) :
    (H (k + 1) n).card = (H k n).card + (H k (n - 1)).card + (G k (n - 2)).card := by
  let A1 := (H k n).image (vcons 1)
  let A2 := ((H k (n - 1)).image (shift 1)).image (vcons 2)
  let A3 := ((G k (n - 2)).image (shift 2)).image (vcons 3)
  have hsplit : H (k + 1) n = (A1 ∪ A2) ∪ A3 := by
    ext s
    simp only [A1, A2, A3, Finset.mem_union, Finset.mem_image, mem_H, mem_G]
    constructor
    · rintro ⟨_, t, hbd, hmono, rfl⟩
      have hcons : t = vcons (t 0) (Fin.tail t) := (vcons_self_tail t).symm
      have ht0 := hbd 0
      by_cases h2 : t 0 = 2
      · left; left
        refine ⟨sOfPrev n 2 (Fin.tail t), ⟨by omega, Fin.tail t, fun i => hbd i.succ,
          fun i j hij => hmono (Fin.succ_le_succ_iff.mpr hij), rfl⟩, ?_⟩
        conv_rhs => rw [hcons, sOfPrev_vcons, h2]
        have hs : shrink n 2 = 1 := by unfold shrink; split_ifs <;> omega
        have hm : min (shrink n 2) (min n (2 + 1)) = 1 := by omega
        rw [hm]
      · by_cases h3 : t 0 = 3
        · left; right
          refine ⟨shift 1 (sOfPrev (n - 1) 2 (fun i => t i.succ - 1)), ?_, ?_⟩
          · refine ⟨sOfPrev (n - 1) 2 (fun i => t i.succ - 1), ⟨by omega, fun i => t i.succ - 1,
              fun i => by dsimp; have := hmono (Fin.zero_le i.succ); have := hbd i.succ; omega,
              fun i j hij => Nat.sub_le_sub_right (hmono (Fin.succ_le_succ_iff.mpr hij)) 1,
              rfl⟩, rfl⟩
          · conv_rhs => rw [hcons, sOfPrev_vcons, h3]
            have hs : shrink n 3 = 2 := by unfold shrink; split_ifs <;> omega
            have hm : min (shrink n 3) (min n (2 + 1)) = 2 := by omega
            rw [hm]
            congr 1
            have hn1 : n - 1 + 1 = n := by omega
            have hsh := sOfPrev_shift (n - 1) 1 2 (fun i => t i.succ - 1) (fun i => by
              have := hmono (Fin.zero_le i.succ); omega)
            rw [hn1] at hsh
            have hteq : shift 1 (fun i => t i.succ - 1) = Fin.tail t := by
              funext i; simp only [shift, Fin.tail]
              have := hmono (Fin.zero_le i.succ); omega
            rw [← hsh, hteq]
        · right
          have ht04 : 4 ≤ t 0 := by omega
          refine ⟨shift 2 (sOfPrev (n - 2) (t 0 - 2) (fun i => t i.succ - 2)), ?_, ?_⟩
          · refine ⟨sOfPrev (n - 2) (t 0 - 2) (fun i => t i.succ - 2),
              ⟨t 0 - 2, by omega, by omega, fun i => t i.succ - 2,
                fun i => by dsimp; have := hmono (Fin.zero_le i.succ); have := hbd i.succ; omega,
                fun i j hij => Nat.sub_le_sub_right (hmono (Fin.succ_le_succ_iff.mpr hij)) 2,
                rfl⟩, rfl⟩
          · conv_rhs => rw [hcons, sOfPrev_vcons]
            have hs : 3 ≤ shrink n (t 0) := by unfold shrink; split_ifs <;> omega
            have hm : min (shrink n (t 0)) (min n (2 + 1)) = 3 := by omega
            rw [hm]
            congr 1
            have hn2 : n - 2 + 2 = n := by omega
            have hsh := sOfPrev_shift (n - 2) 2 (t 0 - 2) (fun i => t i.succ - 2) (fun i => by
              have := hmono (Fin.zero_le i.succ); omega)
            have ht02 : t 0 - 2 + 2 = t 0 := by omega
            rw [hn2, ht02] at hsh
            have hteq : shift 2 (fun i => t i.succ - 2) = Fin.tail t := by
              funext i; simp only [shift, Fin.tail]
              have := hmono (Fin.zero_le i.succ); omega
            rw [← hsh, hteq]
    · rintro ((⟨r, ⟨_, t, hbd, hmono, rfl⟩, rfl⟩ |
        ⟨_, ⟨r, ⟨_, t, hbd, hmono, rfl⟩, rfl⟩, rfl⟩) |
        ⟨_, ⟨r, ⟨t0, ht0, ht0n, t, hbd, hmono, rfl⟩, rfl⟩, rfl⟩)
      · refine ⟨by omega, vcons 2 t, ?_, mono_vcons_iff.mpr ⟨fun i => (hbd i).1, hmono⟩, ?_⟩
        · intro i; refine Fin.cases (by simp; omega) (fun j => hbd j) i
        · rw [sOfPrev_vcons]
          have hs : shrink n 2 = 1 := by unfold shrink; split_ifs <;> omega
          have hm : min (shrink n 2) (min n (2 + 1)) = 1 := by omega
          rw [hm]
      · refine ⟨by omega, vcons 3 (shift 1 t), ?_,
          mono_vcons_iff.mpr ⟨fun i => by simp only [shift]; have := (hbd i).1; omega,
            fun i j hij => Nat.add_le_add_right (hmono hij) 1⟩, ?_⟩
        · intro i
          refine Fin.cases (by simp; omega)
            (fun j => by simp only [vcons_succ, shift]; have := hbd j; omega) i
        · rw [sOfPrev_vcons]
          have hs : shrink n 3 = 2 := by unfold shrink; split_ifs <;> omega
          have hm : min (shrink n 3) (min n (2 + 1)) = 2 := by omega
          rw [hm]
          congr 1
          have hn1 : n - 1 + 1 = n := by omega
          have hsh := sOfPrev_shift (n - 1) 1 2 t (fun i => (hbd i).1)
          rw [hn1] at hsh
          exact hsh.symm
      · refine ⟨by omega, vcons (t0 + 2) (shift 2 t), ?_,
          mono_vcons_iff.mpr ⟨fun i => by simp only [shift]; have := (hbd i).1; omega,
            fun i j hij => Nat.add_le_add_right (hmono hij) 2⟩, ?_⟩
        · intro i
          refine Fin.cases (by simp; omega)
            (fun j => by simp only [vcons_succ, shift]; have := hbd j; omega) i
        · rw [sOfPrev_vcons]
          have hs : 3 ≤ shrink n (t0 + 2) := by unfold shrink; split_ifs <;> omega
          have hm : min (shrink n (t0 + 2)) (min n (2 + 1)) = 3 := by omega
          rw [hm]
          congr 1
          have hn2 : n - 2 + 2 = n := by omega
          have hsh := sOfPrev_shift (n - 2) 2 t0 t (fun i => by have := (hbd i).1; omega)
          rw [hn2] at hsh
          exact hsh.symm
  have hd12 : Disjoint A1 A2 := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    simp only [A1, A2, Finset.mem_image] at hs1 hs2
    rcases hs1 with ⟨_, _, rfl⟩
    rcases hs2 with ⟨_, _, h⟩
    have := congrFun h 0; simp at this
  have hd123 : Disjoint (A1 ∪ A2) A3 := by
    rw [Finset.disjoint_left]
    intro s hs12 hs3
    simp only [A1, A2, A3, Finset.mem_union, Finset.mem_image] at hs12 hs3
    rcases hs3 with ⟨_, _, rfl⟩
    rcases hs12 with ⟨_, _, h⟩ | ⟨_, _, h⟩
    · have := congrFun h 0; simp at this
    · have := congrFun h 0; simp at this
  rw [hsplit, Finset.card_union_of_disjoint hd123, Finset.card_union_of_disjoint hd12]
  simp only [A1, A2, A3]
  rw [Finset.card_image_of_injective _ (vcons_injective 1),
      Finset.card_image_of_injective _ (vcons_injective 2),
      Finset.card_image_of_injective _ (shift_injective 1),
      Finset.card_image_of_injective _ (vcons_injective 3),
      Finset.card_image_of_injective _ (shift_injective 2)]

private lemma G_filter_le_three (k n : ℕ) (hn : 4 ≤ n) :
    (G (k + 1) n).filter (fun s => s 0 ≤ 3) = H (k + 1) n := by
  ext s
  simp only [Finset.mem_filter, mem_G, mem_H]
  constructor
  · rintro ⟨⟨t0, ht0, ht0n, t, hbd, hmono, rfl⟩, hs0⟩
    refine ⟨by omega, t, fun i => ⟨by have := hbd i; omega, (hbd i).2⟩, hmono, ?_⟩
    funext i
    refine Fin.cases ?_ ?_ i
    · simp only [sOfPrev, Fin.val_zero, ↓reduceDIte] at hs0 ⊢
      omega
    · intro j
      simp [sOfPrev]
  · rintro ⟨_, t, hbd, hmono, rfl⟩
    refine ⟨⟨2, le_rfl, by omega, t, hbd, hmono, rfl⟩, ?_⟩
    simp only [sOfPrev, Fin.val_zero, ↓reduceDIte]
    omega

private lemma card_G_four (k : ℕ) : (G (k + 1) 4).card = (H (k + 1) 4).card + 1 := by
  have hsplit : G (k + 1) 4 = H (k + 1) 4 ∪ {fun _ => 4} := by
    ext s
    simp only [Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro hs
      by_cases hle : s 0 ≤ 3
      · left
        rw [← G_filter_le_three k 4 (le_rfl)]
        exact Finset.mem_filter.mpr ⟨hs, hle⟩
      · right
        obtain ⟨t0, ht0, ht0n, t, hbd, hmono, rfl⟩ := mem_G.mp hs
        have h0 : 4 ≤ min (shrink 4 (t 0)) (min 4 (t0 + 1)) := by
          simp only [sOfPrev, Fin.val_zero, ↓reduceDIte] at hle; omega
        have ht0_eq : t 0 = 4 := by
          have := hbd 0; unfold shrink at h0; split_ifs at h0 <;> omega
        funext i
        have hti : t i = 4 := by
          have := hmono (Fin.zero_le i); have := hbd i; omega
        simp only [sOfPrev, hti, shrink, ↓reduceIte]
        split_ifs with hi0
        · omega
        · have hprev : t ⟨i.val - 1, by omega⟩ = 4 := by
            have := hmono (Fin.zero_le ⟨i.val - 1, by omega⟩)
            have := hbd ⟨i.val - 1, by omega⟩
            omega
          omega
    · rintro (hs | rfl)
      · rw [← G_filter_le_three k 4 (le_rfl)] at hs
        exact (Finset.mem_filter.mp hs).1
      · rw [mem_G]
        refine ⟨4, by omega, le_rfl, fun _ => 4, fun _ => ⟨le_rfl, le_rfl⟩, fun _ _ _ => le_rfl, ?_⟩
        funext i
        simp only [sOfPrev, shrink, ↓reduceIte]
        split_ifs <;> omega
  have hdisj : Disjoint (H (k + 1) 4) {fun _ => 4} := by
    rw [Finset.disjoint_singleton_right]
    intro h
    rw [← G_filter_le_three k 4 (le_rfl)] at h
    have := (Finset.mem_filter.mp h).2
    dsimp at this
    omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]

private lemma card_G_succ (k n : ℕ) (hn : 5 ≤ n) :
    (G (k + 1) n).card + (H k (n - 2)).card =
      (G (k + 1) (n - 1)).card + (H k n).card + (G k (n - 2)).card := by
  have h1 : (G (k + 1) n).card =
      ((G (k + 1) n).filter (fun s => s 0 ≤ 3)).card +
        ((G (k + 1) n).filter (fun s => ¬ s 0 ≤ 3)).card :=
    (Finset.card_filter_add_card_filter_not (s := G (k + 1) n) (fun s => s 0 ≤ 3)).symm
  rw [G_filter_le_three k n (by omega)] at h1
  have hge4 : (G (k + 1) n).filter (fun s => ¬ s 0 ≤ 3) =
      ((G (k + 1) (n - 1)).filter (fun r => ¬ r 0 ≤ 2)).image (shift 1) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_image, mem_G]
    constructor
    · rintro ⟨⟨t0, ht0, ht0n, t, hbd, hmono, rfl⟩, hs0⟩
      have hs0' : 4 ≤ min (shrink n (t 0)) (min n (t0 + 1)) := by
        simp only [sOfPrev, Fin.val_zero, ↓reduceDIte] at hs0; omega
      have ht03 : 3 ≤ t0 := by omega
      refine ⟨sOfPrev (n - 1) (t0 - 1) (fun i => t i - 1), ?_, ?_⟩
      · refine ⟨⟨t0 - 1, by omega, by omega, fun i => t i - 1,
          fun i => by dsimp; have := hbd i; omega,
          fun i j hij => Nat.sub_le_sub_right (hmono hij) 1, rfl⟩, ?_⟩
        simp only [sOfPrev, Fin.val_zero, ↓reduceDIte]
        have hsh := shrink_shift (n - 1) 1 (t 0 - 1) (by have := hbd 0; omega)
        have hn1 : n - 1 + 1 = n := by omega
        have ht00 : t 0 - 1 + 1 = t 0 := by have := hbd 0; omega
        rw [hn1, ht00] at hsh
        omega
      · have hn1 : n - 1 + 1 = n := by omega
        have ht01 : t0 - 1 + 1 = t0 := by omega
        have hsh := sOfPrev_shift (n - 1) 1 (t0 - 1) (fun i => t i - 1) (fun i => by
          have := hbd i; omega)
        rw [hn1, ht01] at hsh
        have hteq : shift 1 (fun i => t i - 1) = t := by
          funext i; simp only [shift]; have := hbd i; omega
        rw [← hsh, hteq]
    · rintro ⟨r, ⟨⟨t0, ht0, ht0n, t, hbd, hmono, rfl⟩, hr0⟩, rfl⟩
      have hn1 : n - 1 + 1 = n := by omega
      have hsh := sOfPrev_shift (n - 1) 1 t0 t (fun i => by have := hbd i; omega)
      rw [hn1] at hsh
      refine ⟨⟨t0 + 1, by omega, by omega, shift 1 t,
        fun i => by simp only [shift]; have := hbd i; omega,
        fun i j hij => Nat.add_le_add_right (hmono hij) 1, hsh.symm⟩, ?_⟩
      simp only [shift]
      omega
  have h2 : (G (k + 1) (n - 1)).card =
      ((G (k + 1) (n - 1)).filter (fun r => r 0 ≤ 2)).card +
        ((G (k + 1) (n - 1)).filter (fun r => ¬ r 0 ≤ 2)).card :=
    (Finset.card_filter_add_card_filter_not (s := G (k + 1) (n - 1)) (fun r => r 0 ≤ 2)).symm
  have hle2 : (G (k + 1) (n - 1)).filter (fun r => r 0 ≤ 2) =
      (H k (n - 1)).image (vcons 1) ∪ ((H k (n - 2)).image (shift 1)).image (vcons 2) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image, mem_G, mem_H]
    constructor
    · rintro ⟨⟨t0, ht0, ht0n, t, hbd, hmono, rfl⟩, hr0⟩
      have hr0' : min (shrink (n - 1) (t 0)) (min (n - 1) (t0 + 1)) ≤ 2 := by
        simp only [sOfPrev, Fin.val_zero, ↓reduceDIte] at hr0; exact hr0
      have hcons : t = vcons (t 0) (Fin.tail t) := (vcons_self_tail t).symm
      have hsh_le : shrink (n - 1) (t 0) ≤ 2 := by omega
      have ht0_le3 : t 0 ≤ 3 := by
        have := hbd 0; unfold shrink at hsh_le; split_ifs at hsh_le <;> omega
      have hcases : t 0 = 2 ∨ t 0 = 3 := by have := hbd 0; omega
      rcases hcases with h2 | h3
      · left
        refine ⟨sOfPrev (n - 1) 2 (Fin.tail t), ⟨by omega, Fin.tail t,
          fun i => ⟨by simp only [Fin.tail]; have := hbd i.succ; omega, (hbd i.succ).2⟩,
          fun i j hij => hmono (Fin.succ_le_succ_iff.mpr hij), rfl⟩, ?_⟩
        conv_rhs => rw [hcons, sOfPrev_vcons, h2]
        have hs : shrink (n - 1) 2 = 1 := by unfold shrink; split_ifs <;> omega
        have hm : min (shrink (n - 1) 2) (min (n - 1) (t0 + 1)) = 1 := by omega
        rw [hm]
      · right
        refine ⟨shift 1 (sOfPrev (n - 2) 2 (fun i => t i.succ - 1)), ?_, ?_⟩
        · refine ⟨sOfPrev (n - 2) 2 (fun i => t i.succ - 1), ⟨by omega, fun i => t i.succ - 1,
            fun i => by dsimp; have := hmono (Fin.zero_le i.succ); have := hbd i.succ; omega,
            fun i j hij => Nat.sub_le_sub_right (hmono (Fin.succ_le_succ_iff.mpr hij)) 1,
            rfl⟩, rfl⟩
        · conv_rhs => rw [hcons, sOfPrev_vcons, h3]
          have hs : shrink (n - 1) 3 = 2 := by unfold shrink; split_ifs <;> omega
          have hm : min (shrink (n - 1) 3) (min (n - 1) (t0 + 1)) = 2 := by omega
          rw [hm]
          congr 1
          have hn2 : n - 2 + 1 = n - 1 := by omega
          have hsh := sOfPrev_shift (n - 2) 1 2 (fun i => t i.succ - 1) (fun i => by
            have := hmono (Fin.zero_le i.succ); omega)
          rw [hn2] at hsh
          have hteq : shift 1 (fun i => t i.succ - 1) = Fin.tail t := by
            funext i; simp only [shift, Fin.tail]; have := hmono (Fin.zero_le i.succ); omega
          rw [← hsh, hteq]
    · rintro (⟨s, ⟨_, t, hbd, hmono, rfl⟩, rfl⟩ | ⟨_, ⟨s, ⟨_, t, hbd, hmono, rfl⟩, rfl⟩, rfl⟩)
      · refine ⟨⟨2, le_rfl, by omega, vcons 2 t, ?_,
          mono_vcons_iff.mpr ⟨fun i => (hbd i).1, hmono⟩, ?_⟩, by simp⟩
        · intro i; refine Fin.cases (by simp; omega) (fun j => hbd j) i
        · rw [sOfPrev_vcons]
          have hs : shrink (n - 1) 2 = 1 := by unfold shrink; split_ifs <;> omega
          have hm : min (shrink (n - 1) 2) (min (n - 1) (2 + 1)) = 1 := by omega
          rw [hm]
      · refine ⟨⟨2, le_rfl, by omega, vcons 3 (shift 1 t), ?_,
          mono_vcons_iff.mpr ⟨fun i => by simp only [shift]; have := (hbd i).1; omega,
            fun i j hij => Nat.add_le_add_right (hmono hij) 1⟩, ?_⟩, by simp⟩
        · intro i
          refine Fin.cases (by simp; omega)
            (fun j => by simp only [vcons_succ, shift]; have := hbd j; omega) i
        · rw [sOfPrev_vcons]
          have hs : shrink (n - 1) 3 = 2 := by unfold shrink; split_ifs <;> omega
          have hm : min (shrink (n - 1) 3) (min (n - 1) (2 + 1)) = 2 := by omega
          rw [hm]
          congr 1
          have hn2 : n - 2 + 1 = n - 1 := by omega
          have hsh := sOfPrev_shift (n - 2) 1 2 t (fun i => (hbd i).1)
          rw [hn2] at hsh
          exact hsh.symm
  have hdisj : Disjoint ((H k (n - 1)).image (vcons 1))
      (((H k (n - 2)).image (shift 1)).image (vcons 2)) := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    simp only [Finset.mem_image] at hr1 hr2
    rcases hr1 with ⟨_, _, rfl⟩
    rcases hr2 with ⟨_, _, h⟩
    have := congrFun h 0; simp at this
  have hcard_le2 : ((G (k + 1) (n - 1)).filter (fun r => r 0 ≤ 2)).card =
      (H k (n - 1)).card + (H k (n - 2)).card := by
    rw [hle2, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (vcons_injective 1),
      Finset.card_image_of_injective _ (vcons_injective 2),
      Finset.card_image_of_injective _ (shift_injective 1)]
  have hcard_ge4 : ((G (k + 1) n).filter (fun s => ¬ s 0 ≤ 3)).card =
      ((G (k + 1) (n - 1)).filter (fun r => ¬ r 0 ≤ 2)).card := by
    rw [hge4, Finset.card_image_of_injective _ (shift_injective 1)]
  have hH := card_H_succ k n (by omega)
  omega

private lemma card_F_succ (k n : ℕ) (hn : 3 ≤ n) :
    (F (k + 1) n).card = (H k n).card + (F (k + 1) (n - 1)).card := by
  let A1 := (H k n).image (vcons 1)
  let A2 := (F (k + 1) (n - 1)).image (shift 1)
  have hsplit : F (k + 1) n = A1 ∪ A2 := by
    ext s
    simp only [A1, A2, Finset.mem_union, Finset.mem_image, mem_F, mem_H]
    constructor
    · rintro ⟨t, hbd, hmono, rfl⟩
      by_cases h2 : t 0 = 2
      · left
        have hcons : t = vcons (t 0) (Fin.tail t) := (vcons_self_tail t).symm
        refine ⟨sOfPrev n 2 (Fin.tail t), ⟨by omega, Fin.tail t, fun i => hbd i.succ,
          fun i j hij => hmono (Fin.succ_le_succ_iff.mpr hij), rfl⟩, ?_⟩
        conv_rhs => rw [hcons, sOf_vcons, h2]
        have hs : shrink n 2 = 1 := by unfold shrink; split_ifs <;> omega
        rw [hs]
      · right
        have ht03 : 3 ≤ t 0 := by have := (hbd 0).1; omega
        refine ⟨sOf (n - 1) (fun i => t i - 1), ⟨fun i => t i - 1,
          fun i => by dsimp; have := hmono (Fin.zero_le i); have := hbd i; omega,
          fun i j hij => Nat.sub_le_sub_right (hmono hij) 1, rfl⟩, ?_⟩
        have hn1 : n - 1 + 1 = n := by omega
        have hsh := sOf_shift (n - 1) 1 (fun i => t i - 1) (fun i => by
          have := hmono (Fin.zero_le i); omega)
        rw [hn1] at hsh
        have hteq : shift 1 (fun i => t i - 1) = t := by
          funext i; simp only [shift]; have := hmono (Fin.zero_le i); omega
        rw [← hsh, hteq]
    · rintro (⟨r, ⟨_, t, hbd, hmono, rfl⟩, rfl⟩ | ⟨r, ⟨t, hbd, hmono, rfl⟩, rfl⟩)
      · refine ⟨vcons 2 t, ?_, mono_vcons_iff.mpr ⟨fun i => (hbd i).1, hmono⟩, ?_⟩
        · intro i; refine Fin.cases (by simp; omega) (fun j => hbd j) i
        · rw [sOf_vcons]
          have hs : shrink n 2 = 1 := by unfold shrink; split_ifs <;> omega
          rw [hs]
      · refine ⟨shift 1 t, fun i => by simp only [shift]; have := hbd i; omega,
          fun i j hij => Nat.add_le_add_right (hmono hij) 1, ?_⟩
        have hn1 : n - 1 + 1 = n := by omega
        have hsh := sOf_shift (n - 1) 1 t (fun i => (hbd i).1)
        rw [hn1] at hsh
        exact hsh.symm
  have hdisj : Disjoint A1 A2 := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    simp only [A1, A2, Finset.mem_image, mem_F] at hs1 hs2
    rcases hs1 with ⟨_, _, rfl⟩
    rcases hs2 with ⟨_, ⟨t, hbd, _, rfl⟩, h⟩
    have h0 := congrFun h 0
    simp only [shift, sOf, Fin.val_zero, ↓reduceDIte, vcons_zero] at h0
    have hge1 : 1 ≤ shrink (n - 1) (t 0) := by
      have := hbd 0; unfold shrink; split_ifs <;> omega
    omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  simp only [A1, A2]
  rw [Finset.card_image_of_injective _ (vcons_injective 1),
      Finset.card_image_of_injective _ (shift_injective 1)]

private lemma card_S0_zero (n : ℕ) (hn : 1 ≤ n) : (S0 0 n).card = 1 := by
  have heq : S0 0 n = {fun _ => 0} := by
    ext s
    rw [mem_S0, mem_S, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hs0⟩
      funext i
      have hi : i = 0 := Fin.ext (by omega)
      rw [hi, hs0]
    · rintro rfl
      refine ⟨⟨fun _ => 0, fun _ => by dsimp; omega, fun _ _ _ => le_rfl, ?_⟩, rfl⟩
      funext i
      have hi : i = 0 := Fin.ext (by omega)
      rw [hi]
      simp only [sOf, Fin.val_zero, ↓reduceDIte, shrink]
      split_ifs <;> omega
  rw [heq, Finset.card_singleton]

private lemma card_S0_succ (k n : ℕ) (hn : 3 ≤ n) :
    (S0 (k + 1) n).card = (S0 k n).card + (G k n).card + (G k (n - 1)).card := by
  let A0 := (S0 k n).image (vcons 0)
  let A1 := (G k n).image (fun r => vcons 0 (vcons 1 r))
  let A2 := ((G k (n - 1)).image (shift 1)).image (fun r => vcons 0 (vcons 2 r))
  have hsplit : S0 (k + 1) n = (A0 ∪ A1) ∪ A2 := by
    ext s
    simp only [A0, A1, A2, Finset.mem_union, Finset.mem_image, mem_S0, mem_S, mem_G]
    constructor
    · rintro ⟨⟨t, hle, hmono, rfl⟩, hs0⟩
      have ht01 : t 0 ≤ 1 := by
        simp only [sOf, Fin.val_zero, ↓reduceDIte, shrink] at hs0
        split_ifs at hs0 <;> omega
      have hcons1 : t = vcons (t 0) (Fin.tail t) := (vcons_self_tail t).symm
      have ht1_eq : Fin.tail t = vcons (t 1) (Fin.tail (Fin.tail t)) :=
        (vcons_self_tail (Fin.tail t)).symm
      have hs0_val : shrink n (t 0) = 0 := by
        simp only [sOf, Fin.val_zero, ↓reduceDIte] at hs0; exact hs0
      by_cases ht1_le1 : t 1 ≤ 1
      · left; left
        refine ⟨sOf n (Fin.tail t), ⟨⟨Fin.tail t, fun i => hle i.succ,
          fun i j hij => hmono (Fin.succ_le_succ_iff.mpr hij), rfl⟩, ?_⟩, ?_⟩
        · have ht10 : Fin.tail t 0 = t 1 := by simp [Fin.tail]
          simp only [sOf, Fin.val_zero, ↓reduceDIte, ht10]
          unfold shrink; split_ifs <;> omega
        · conv_rhs => rw [hcons1, sOf_vcons, hs0_val, ht1_eq, sOfPrev_vcons]
          conv_lhs => rw [ht1_eq, sOf_vcons]
          have hs1 : shrink n (t 1) = 0 := by unfold shrink; split_ifs <;> omega
          simp [hs1]
      · have ht1_ge2 : 2 ≤ t 1 := by omega
        by_cases h1 : min (shrink n (t 1)) (min n (t 0 + 1)) = 1
        · left; right
          refine ⟨sOfPrev n (t 1) (Fin.tail (Fin.tail t)),
            ⟨t 1, ht1_ge2, hle 1, Fin.tail (Fin.tail t),
              fun i => ⟨hmono (Fin.mk_le_mk.mpr (by simp)), hle i.succ.succ⟩,
              fun i j hij => hmono (Fin.succ_le_succ_iff.mpr (Fin.succ_le_succ_iff.mpr hij)),
              rfl⟩, ?_⟩
          conv_rhs => rw [hcons1, sOf_vcons, hs0_val, ht1_eq, sOfPrev_vcons, h1]
        · right
          have h2 : min (shrink n (t 1)) (min n (t 0 + 1)) = 2 := by
            have : 1 ≤ shrink n (t 1) := by unfold shrink; split_ifs <;> omega
            omega
          have ht1_ge3 : 3 ≤ t 1 := by
            have hsh2 : 2 ≤ shrink n (t 1) := by omega
            have h1n := hle 1
            unfold shrink at hsh2; split_ifs at hsh2 <;> omega
          refine ⟨shift 1 (sOfPrev (n - 1) (t 1 - 1) (fun i => t i.succ.succ - 1)), ?_, ?_⟩
          · refine ⟨sOfPrev (n - 1) (t 1 - 1) (fun i => t i.succ.succ - 1),
              ⟨t 1 - 1, by omega, by have := hle 1; omega, fun i => t i.succ.succ - 1,
                fun i => by
                  dsimp
                  have hge : t 1 ≤ t i.succ.succ := hmono (Fin.mk_le_mk.mpr (by simp))
                  have := hle i.succ.succ; omega,
                fun i j hij => Nat.sub_le_sub_right
                  (hmono (Fin.succ_le_succ_iff.mpr (Fin.succ_le_succ_iff.mpr hij))) 1,
                rfl⟩, rfl⟩
          · conv_rhs => rw [hcons1, sOf_vcons, hs0_val, ht1_eq, sOfPrev_vcons, h2]
            congr 2
            have hn1 : n - 1 + 1 = n := by omega
            have ht11 : t 1 - 1 + 1 = t 1 := by omega
            have hsh := sOfPrev_shift (n - 1) 1 (t 1 - 1) (fun i => t i.succ.succ - 1) (fun i => by
              have hge : t 1 ≤ t i.succ.succ := hmono (Fin.mk_le_mk.mpr (by simp)); omega)
            rw [hn1, ht11] at hsh
            have hteq : shift 1 (fun i => t i.succ.succ - 1) = Fin.tail (Fin.tail t) := by
              funext i; simp only [shift, Fin.tail]
              have hge : t 1 ≤ t i.succ.succ := hmono (Fin.mk_le_mk.mpr (by simp)); omega
            rw [← hsh, hteq]
    · rintro ((⟨r, ⟨⟨t, hle, hmono, rfl⟩, hr0⟩, rfl⟩ |
        ⟨r, ⟨t1, ht1, ht1n, t, hbd, hmono, rfl⟩, rfl⟩) |
        ⟨_, ⟨r, ⟨t1, ht1, ht1n, t, hbd, hmono, rfl⟩, rfl⟩, rfl⟩)
      · have ht0_le1 : t 0 ≤ 1 := by
          simp only [sOf, Fin.val_zero, ↓reduceDIte, shrink] at hr0
          split_ifs at hr0 <;> omega
        refine ⟨⟨vcons 0 t, ?_, mono_vcons_iff.mpr ⟨fun _ => Nat.zero_le _, hmono⟩, ?_⟩, by simp⟩
        · intro i; refine Fin.cases (by simp) (fun j => hle j) i
        · have hcons : t = vcons (t 0) (Fin.tail t) := (vcons_self_tail t).symm
          rw [sOf_vcons]
          conv_lhs => rw [hcons, sOf_vcons]
          conv_rhs => rw [hcons, sOfPrev_vcons]
          have hs0 : shrink n 0 = 0 := by unfold shrink; split_ifs <;> omega
          have hs1 : shrink n (t 0) = 0 := by unfold shrink; split_ifs <;> omega
          simp [hs0, hs1]
      · refine ⟨⟨vcons 0 (vcons t1 t), ?_,
          mono_vcons_iff.mpr ⟨fun _ => Nat.zero_le _,
            mono_vcons_iff.mpr ⟨fun i => (hbd i).1, hmono⟩⟩, ?_⟩, by simp⟩
        · intro i
          refine Fin.cases (by simp)
            (fun j => Fin.cases (by simp [ht1n]) (fun l => by simp [(hbd l).2]) j) i
        · rw [sOf_vcons, sOfPrev_vcons]
          have hs0 : shrink n 0 = 0 := by unfold shrink; split_ifs <;> omega
          have hs1 : 1 ≤ shrink n t1 := by unfold shrink; split_ifs <;> omega
          have hm : min (shrink n t1) (min n (0 + 1)) = 1 := by omega
          rw [hs0, hm]
      · refine ⟨⟨vcons 1 (vcons (t1 + 1) (shift 1 t)), ?_,
          mono_vcons_iff.mpr ⟨fun i => Fin.cases (by simp)
              (fun j => by simp only [vcons_succ, shift]; have := (hbd j).1; omega) i,
            mono_vcons_iff.mpr ⟨fun i => by simp only [shift]; have := (hbd i).1; omega,
              fun i j hij => Nat.add_le_add_right (hmono hij) 1⟩⟩, ?_⟩, by simp⟩
        · intro i
          refine Fin.cases (by simp; omega)
            (fun j => Fin.cases (by simp; omega)
              (fun l => by simp only [vcons_succ, shift]; have := (hbd l).2; omega) j) i
        · rw [sOf_vcons, sOfPrev_vcons]
          have hs0 : shrink n 1 = 0 := by unfold shrink; split_ifs <;> omega
          have hs1 : 2 ≤ shrink n (t1 + 1) := by unfold shrink; split_ifs <;> omega
          have hm : min (shrink n (t1 + 1)) (min n (1 + 1)) = 2 := by omega
          rw [hs0, hm]
          congr 2
          have hn1 : n - 1 + 1 = n := by omega
          have hsh := sOfPrev_shift (n - 1) 1 t1 t (fun i => by have := (hbd i).1; omega)
          rw [hn1] at hsh
          exact hsh.symm
  have hd01 : Disjoint A0 A1 := by
    rw [Finset.disjoint_left]
    intro s hs0 hs1
    simp only [A0, A1, Finset.mem_image, mem_S0] at hs0 hs1
    rcases hs0 with ⟨r, ⟨_, hr0⟩, rfl⟩
    rcases hs1 with ⟨_, _, h⟩
    have := congrFun h 1
    simp [hr0] at this
  have hd012 : Disjoint (A0 ∪ A1) A2 := by
    rw [Finset.disjoint_left]
    intro s hs01 hs2
    simp only [A0, A1, A2, Finset.mem_union, Finset.mem_image, mem_S0] at hs01 hs2
    rcases hs2 with ⟨_, _, rfl⟩
    rcases hs01 with ⟨r, ⟨_, hr0⟩, h⟩ | ⟨_, _, h⟩
    · have := congrFun h 1; simp [hr0] at this
    · have := congrFun h 1; simp at this
  have hinj1 : Function.Injective (fun r : Fin k → ℕ => vcons 0 (vcons 1 r)) :=
    (vcons_injective 0).comp (vcons_injective 1)
  have hinj2 : Function.Injective (fun r : Fin k → ℕ => vcons 0 (vcons 2 r)) :=
    (vcons_injective 0).comp (vcons_injective 2)
  rw [hsplit, Finset.card_union_of_disjoint hd012, Finset.card_union_of_disjoint hd01]
  simp only [A0, A1, A2]
  rw [Finset.card_image_of_injective _ (vcons_injective 0),
      Finset.card_image_of_injective _ hinj1,
      Finset.card_image_of_injective _ hinj2,
      Finset.card_image_of_injective _ (shift_injective 1)]

private lemma card_S_split (k n : ℕ) (hn : 2 ≤ n) :
    (S (k + 1) n).card = (S0 k n).card + (F (k + 1) n).card := by
  have h1 : (S (k + 1) n).card =
      ((S (k + 1) n).filter (fun s => s 0 = 0)).card +
        ((S (k + 1) n).filter (fun s => ¬ s 0 = 0)).card :=
    (Finset.card_filter_add_card_filter_not (s := S (k + 1) n) (fun s => s 0 = 0)).symm
  have hne0 : (S (k + 1) n).filter (fun s => ¬ s 0 = 0) = F (k + 1) n := by
    ext s
    simp only [Finset.mem_filter, mem_S, mem_F]
    constructor
    · rintro ⟨⟨t, hle, hmono, rfl⟩, hs0⟩
      have ht02 : 2 ≤ t 0 := by
        simp only [sOf, Fin.val_zero, ↓reduceDIte, shrink] at hs0
        split_ifs at hs0 <;> omega
      exact ⟨t, fun i => ⟨le_trans ht02 (hmono (Fin.zero_le i)), hle i⟩, hmono, rfl⟩
    · rintro ⟨t, hbd, hmono, rfl⟩
      refine ⟨⟨t, fun i => (hbd i).2, hmono, rfl⟩, ?_⟩
      simp only [sOf, Fin.val_zero, ↓reduceDIte, shrink]
      have := (hbd 0).1
      split_ifs <;> omega
  rw [hne0] at h1
  exact h1

/-! ## Section 4: Closed-form formulas and exact small values -/

private lemma card_S0_four_eq (n : ℕ) (hn : 3 ≤ n) :
    (S0 4 n).card = 1 + (G 0 n).card + (G 0 (n - 1)).card +
      (G 1 n).card + (G 1 (n - 1)).card +
      (G 2 n).card + (G 2 (n - 1)).card +
      (G 3 n).card + (G 3 (n - 1)).card := by
  have h0 := card_S0_zero n (by omega)
  have h1 := card_S0_succ 0 n hn
  have h2 := card_S0_succ 1 n hn
  have h3 := card_S0_succ 2 n hn
  have h4 := card_S0_succ 3 n hn
  simp only [Nat.reduceAdd] at h1 h2 h3 h4
  omega

private lemma arith_solve
    (h g : ℕ → ℕ → ℕ) (f5 s04 a_fn : ℕ → ℕ)
    (hh0 : ∀ n, 2 ≤ n → h 0 n = 1)
    (hg0 : ∀ n, 2 ≤ n → g 0 n = 1)
    (hg2 : ∀ k, g k 2 = 1)
    (hf2 : f5 2 = 1)
    (hh3 : ∀ k, h k 3 = k + 1)
    (hg3 : ∀ k, g k 3 = k + 1)
    (hhS : ∀ k n, 4 ≤ n → h (k + 1) n = h k n + h k (n - 1) + g k (n - 2))
    (hg4 : ∀ k, g (k + 1) 4 = h (k + 1) 4 + 1)
    (hgS : ∀ k n, 5 ≤ n → g (k + 1) n + h k (n - 2) = g (k + 1) (n - 1) + h k n + g k (n - 2))
    (hfS : ∀ n, 3 ≤ n → f5 n = h 4 n + f5 (n - 1))
    (hs0 : ∀ n, 3 ≤ n → s04 n = 1 + g 0 n + g 0 (n - 1) + g 1 n + g 1 (n - 1) +
      g 2 n + g 2 (n - 1) + g 3 n + g 3 (n - 1))
    (haS : ∀ n, 2 ≤ n → a_fn n = s04 n + f5 n) :
    (a_fn 3 = 21 ∧ a_fn 4 = 55 ∧ a_fn 5 = 111 ∧ a_fn 6 = 192 ∧ a_fn 7 = 302) ∧
    (∀ n, 7 ≤ n → 24 * (a_fn n : ℤ) =
      (n : ℤ) ^ 4 - 2 * (n : ℤ) ^ 3 + 95 * (n : ℤ) ^ 2 + 578 * (n : ℤ) - 3168) := by
  have hh1 : ∀ n, 4 ≤ n → h 1 n = 3 := by
    intro n hn
    have hrec := hhS 0 n hn
    have := hh0 n (by omega)
    have := hh0 (n - 1) (by omega)
    have := hg0 (n - 2) (by omega)
    simp only [Nat.reduceAdd] at hrec
    omega
  have hg1 : ∀ n, 4 ≤ n → g 1 n = n := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      by_cases hm : m = 3
      · subst hm
        have h1 := hg4 0
        have h2 := hh1 4 (le_rfl)
        simp only [Nat.reduceAdd] at h1 ⊢
        omega
      · have hrec := hgS 0 (m + 1) (by omega)
        have := hh0 (m - 1) (by omega)
        have := hh0 (m + 1) (by omega)
        have := hg0 (m - 1) (by omega)
        have := ih (by omega)
        have hm1 : m + 1 - 2 = m - 1 := by omega
        have hm0 : m + 1 - 1 = m := by omega
        simp only [Nat.reduceAdd, hm1, hm0] at hrec
        omega
  have hh2_vals : h 2 4 = 6 ∧ h 2 5 = 8 := by
    have h4 := hhS 1 4 (le_rfl)
    have h5 := hhS 1 5 (by omega)
    simp only [Nat.reduceAdd, Nat.reduceSub] at h4 h5
    have := hh3 1; have := hh1 4 (le_rfl); have := hh1 5 (by omega)
    have := hg2 1; have := hg3 1
    omega
  have hh2_poly : ∀ n, 6 ≤ n → h 2 n = n + 4 := by
    intro n hn
    have hrec := hhS 1 n (by omega)
    simp only [Nat.reduceAdd] at hrec
    have := hh1 n (by omega); have := hh1 (n - 1) (by omega); have := hg1 (n - 2) (by omega)
    omega
  have hg2_poly : ∀ n, 4 ≤ n → 2 * g 2 n + 3 * n = n ^ 2 + 10 := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      by_cases hm : m = 3
      · subst hm
        have h1 := hg4 1
        have h2 := hh2_vals.1
        simp only [Nat.reduceAdd] at h1 ⊢
        omega
      · have hrec := hgS 1 (m + 1) (by omega)
        have hm1 : m + 1 - 2 = m - 1 := by omega
        have hm0 : m + 1 - 1 = m := by omega
        simp only [Nat.reduceAdd, hm1, hm0] at hrec
        have ihm := ih (by omega)
        have h1m := hh1 (m + 1) (by omega)
        have hdiff : g 1 (m - 1) = h 1 (m - 1) + (m - 4) := by
          by_cases hm4 : m = 4
          · subst hm4
            simp only [Nat.reduceSub]
            have := hg3 1; have := hh3 1; omega
          · have := hh1 (m - 1) (by omega); have := hg1 (m - 1) (by omega); omega
        zify [show 4 ≤ m by omega] at hrec ihm h1m hdiff ⊢
        linarith
  have hh3_vals : h 3 4 = 10 ∧ h 3 5 = 17 ∧ h 3 6 = 25 := by
    have h4 := hhS 2 4 (le_rfl); have h5 := hhS 2 5 (by omega); have h6 := hhS 2 6 (by omega)
    simp only [Nat.reduceAdd, Nat.reduceSub] at h4 h5 h6
    have := hh3 2; have := hh2_vals; have := hh2_poly 6 (le_rfl)
    have := hg2 2; have := hg3 2; have := hg2_poly 4 (le_rfl)
    omega
  have hh3_poly : ∀ n, 7 ≤ n → 2 * h 3 n + 3 * n = n ^ 2 + 34 := by
    intro n hn
    have hrec := hhS 2 n (by omega)
    simp only [Nat.reduceAdd] at hrec
    have h2n := hh2_poly n (by omega)
    have h2n1 := hh2_poly (n - 1) (by omega)
    have g2n2 := hg2_poly (n - 2) (by omega)
    zify [show 1 ≤ n by omega, show 2 ≤ n by omega] at hrec h2n h2n1 g2n2 ⊢
    linarith
  have hg3_vals : g 3 4 = 11 ∧ g 3 5 = 19 ∧ g 3 6 = 30 ∧ g 3 7 = 43 := by
    have g4 := hg4 2
    have g5 := hgS 2 5 (le_rfl); have g6 := hgS 2 6 (by omega); have g7 := hgS 2 7 (by omega)
    simp only [Nat.reduceAdd, Nat.reduceSub] at g4 g5 g6 g7
    have := hh3 2; have := hh2_vals; have := hh2_poly 6 (le_rfl); have := hh2_poly 7 (by omega)
    have := hg3 2; have := hg2_poly 4 (le_rfl); have := hg2_poly 5 (by omega)
    have := hh3_vals
    omega
  have hg3_poly : ∀ n, 7 ≤ n → 6 * g 3 n + 9 * n ^ 2 + 78 = n ^ 3 + 62 * n := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      by_cases hm : m = 6
      · subst hm
        simp only [Nat.reduceAdd]
        have := hg3_vals.2.2.2; omega
      · have hrec := hgS 2 (m + 1) (by omega)
        have hm1 : m + 1 - 2 = m - 1 := by omega
        have hm0 : m + 1 - 1 = m := by omega
        simp only [Nat.reduceAdd, hm1, hm0] at hrec
        have ihm := ih (by omega)
        have h2p := hh2_poly (m + 1) (by omega)
        have h2m := hh2_poly (m - 1) (by omega)
        have g2m := hg2_poly (m - 1) (by omega)
        zify [show 1 ≤ m by omega] at hrec ihm h2p h2m g2m ⊢
        linarith
  have hh4_vals : h 4 4 = 15 ∧ h 4 5 = 31 ∧ h 4 6 = 53 ∧ h 4 7 = 75 ∧ h 4 8 = 98 := by
    have h4 := hhS 3 4 (le_rfl); have h5 := hhS 3 5 (by omega); have h6 := hhS 3 6 (by omega)
    have h7 := hhS 3 7 (by omega); have h8 := hhS 3 8 (by omega)
    simp only [Nat.reduceAdd, Nat.reduceSub] at h4 h5 h6 h7 h8
    have := hh3 3; have := hh3_vals; have := hh3_poly 7 (le_rfl); have := hh3_poly 8 (by omega)
    have := hg2 3; have := hg3 3; have := hg3_vals
    omega
  have hh4_poly : ∀ n, 9 ≤ n → 6 * h 4 n + 9 * n ^ 2 + 30 = n ^ 3 + 86 * n := by
    intro n hn
    have hrec := hhS 3 n (by omega)
    simp only [Nat.reduceAdd] at hrec
    have h3n := hh3_poly n (by omega)
    have h3n1 := hh3_poly (n - 1) (by omega)
    have g3n2 := hg3_poly (n - 2) (by omega)
    zify [show 1 ≤ n by omega, show 2 ≤ n by omega] at hrec h3n h3n1 g3n2 ⊢
    linarith
  have hf5_vals : f5 3 = 6 ∧ f5 4 = 21 ∧ f5 5 = 52 ∧ f5 6 = 105 ∧ f5 7 = 180 ∧ f5 8 = 278 := by
    have f3 := hfS 3 (le_rfl); have f4 := hfS 4 (by omega); have f5' := hfS 5 (by omega)
    have f6 := hfS 6 (by omega); have f7 := hfS 7 (by omega); have f8 := hfS 8 (by omega)
    simp only [Nat.reduceSub] at f3 f4 f5' f6 f7 f8
    have := hh3 4; have := hh4_vals
    omega
  have hf5_poly : ∀ n, 8 ≤ n → 24 * f5 n + 10 * n ^ 3 + 2592 = n ^ 4 + 155 * n ^ 2 + 46 * n := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      by_cases hm : m = 7
      · subst hm
        simp only [Nat.reduceAdd]
        have := hf5_vals.2.2.2.2.2; omega
      · have hrec := hfS (m + 1) (by omega)
        have hm0 : m + 1 - 1 = m := by omega
        rw [hm0] at hrec
        have ihm := ih (by omega)
        have h4 := hh4_poly (m + 1) (by omega)
        zify at hrec ihm h4 ⊢
        linarith
  have hs0_poly : ∀ n, 8 ≤ n → 6 * s04 n + 15 * n ^ 2 + 144 = 2 * n ^ 3 + 133 * n := by
    intro n hn
    have hs := hs0 n (by omega)
    have g0n := hg0 n (by omega); have g0n1 := hg0 (n - 1) (by omega)
    have g1n := hg1 n (by omega); have g1n1 := hg1 (n - 1) (by omega)
    have g2n := hg2_poly n (by omega); have g2n1 := hg2_poly (n - 1) (by omega)
    have g3n := hg3_poly n (by omega); have g3n1 := hg3_poly (n - 1) (by omega)
    zify [show 1 ≤ n by omega] at hs g0n g0n1 g1n g1n1 g2n g2n1 g3n g3n1 ⊢
    linarith
  have hsmall : a_fn 3 = 21 ∧ a_fn 4 = 55 ∧ a_fn 5 = 111 ∧ a_fn 6 = 192 ∧ a_fn 7 = 302 := by
    have a3 := haS 3 (by omega); have a4 := haS 4 (by omega); have a5 := haS 5 (by omega)
    have a6 := haS 6 (by omega); have a7 := haS 7 (by omega)
    have s3 := hs0 3 (le_rfl); have s4 := hs0 4 (by omega); have s5 := hs0 5 (by omega)
    have s6 := hs0 6 (by omega); have s7 := hs0 7 (by omega)
    simp only [Nat.reduceSub] at s3 s4 s5 s6 s7
    have := hg0 2 (le_rfl); have := hg0 3 (by omega); have := hg0 4 (by omega)
    have := hg0 5 (by omega); have := hg0 6 (by omega); have := hg0 7 (by omega)
    have := hg2 1; have := hg3 1; have := hg1 4 (le_rfl); have := hg1 5 (by omega)
    have := hg1 6 (by omega); have := hg1 7 (by omega)
    have := hg2 2; have := hg3 2; have := hg2_poly 4 (le_rfl); have := hg2_poly 5 (by omega)
    have := hg2_poly 6 (by omega); have := hg2_poly 7 (by omega)
    have := hg2 3; have := hg3 3; have := hg3_vals
    have := hf5_vals
    omega
  refine ⟨hsmall, ?_⟩
  intro n hn
  by_cases h7 : n = 7
  · subst h7; have := hsmall.2.2.2.2; norm_num [this]
  · have ha := haS n (by omega)
    have hf := hf5_poly n (by omega)
    have hs := hs0_poly n (by omega)
    zify at ha hf hs
    linarith

private lemma a_one : a 1 = 6 := by
  rw [a_eq_card_S]; decide

private lemma a_two : a 2 = 10 := by
  rw [a_eq_card_S]; decide

private lemma a_closed :
    (a 3 = 21 ∧ a 4 = 55 ∧ a 5 = 111 ∧ a 6 = 192 ∧ a 7 = 302) ∧
    (∀ n, 7 ≤ n → 24 * (a n : ℤ) =
      (n : ℤ) ^ 4 - 2 * (n : ℤ) ^ 3 + 95 * (n : ℤ) ^ 2 + 578 * (n : ℤ) - 3168) :=
  arith_solve (fun k n => (H k n).card) (fun k n => (G k n).card)
    (fun n => (F 5 n).card) (fun n => (S0 4 n).card) a
    card_H_zero card_G_zero card_G_two (card_F_two 5)
    card_H_three card_G_three card_H_succ card_G_four card_G_succ
    (fun n hn => card_F_succ 4 n hn) card_S0_four_eq
    (fun n hn => by rw [a_eq_card_S]; exact card_S_split 4 n hn)

private lemma a_small_vals :
    a 3 = 21 ∧ a 4 = 55 ∧ a 5 = 111 ∧ a 6 = 192 ∧ a 7 = 302 :=
  a_closed.1

private lemma a_poly (n : ℕ) (hn : 7 ≤ n) :
    24 * (a n : ℤ) = (n : ℤ) ^ 4 - 2 * (n : ℤ) ^ 3 + 95 * (n : ℤ) ^ 2 + 578 * (n : ℤ) - 3168 :=
  a_closed.2 n hn

private lemma a_recurrence (n : ℕ) (hn : 11 < n) :
    (a n : ℤ) =
      5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  have h0 := a_poly n (by omega)
  have h1 := a_poly (n - 1) (by omega)
  have h2 := a_poly (n - 2) (by omega)
  have h3 := a_poly (n - 3) (by omega)
  have h4 := a_poly (n - 4) (by omega)
  have h5 := a_poly (n - 5) (by omega)
  have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  have hn3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
  have hn4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := by omega
  have hn5 : ((n - 5 : ℕ) : ℤ) = (n : ℤ) - 5 := by omega
  rw [hn1] at h1; rw [hn2] at h2; rw [hn3] at h3; rw [hn4] at h4; rw [hn5] at h5
  linarith

private lemma a_vals_8_11 :
    a 8 = 442 ∧ a 9 = 618 ∧ a 10 = 838 ∧ a 11 = 1111 := by
  have h8 := a_poly 8 (by omega)
  have h9 := a_poly 9 (by omega)
  have h10 := a_poly 10 (by omega)
  have h11 := a_poly 11 (by omega)
  omega

/-! ## Section 5: Generating function identity and main theorem -/

private lemma coeff_mul_X_pow_rat (f : PowerSeries ℚ) (k n : ℕ) :
    PowerSeries.coeff n (f * (X : PowerSeries ℚ) ^ k) =
      if k ≤ n then PowerSeries.coeff (n - k) f else 0 := by
  rw [mul_comm, PowerSeries.coeff_X_pow_mul']

private lemma gf_eq :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (6 - 20 * X + 31 * X ^ 2 - 10 * X ^ 3 - 24 * X ^ 4 + 21 * X ^ 5 - 3 * X ^ 6
        - 4 * X ^ 7 + 8 * X ^ 8 - 3 * X ^ 9 - X ^ 10) := by
  set F : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have hpow : (1 - (X : PowerSeries ℚ)) ^ 5 =
      1 - PowerSeries.C 5 * X ^ 1 + PowerSeries.C 10 * X ^ 2 - PowerSeries.C 10 * X ^ 3 +
        PowerSeries.C 5 * X ^ 4 - X ^ 5 := by
    simp only [map_ofNat]
    ring
  have hrhs :
      (X : PowerSeries ℚ) * (6 - 20 * X + 31 * X ^ 2 - 10 * X ^ 3 - 24 * X ^ 4 + 21 * X ^ 5 -
        3 * X ^ 6 - 4 * X ^ 7 + 8 * X ^ 8 - 3 * X ^ 9 - X ^ 10) =
      PowerSeries.C 6 * X ^ 1 - PowerSeries.C 20 * X ^ 2 + PowerSeries.C 31 * X ^ 3 -
        PowerSeries.C 10 * X ^ 4 - PowerSeries.C 24 * X ^ 5 + PowerSeries.C 21 * X ^ 6 -
        PowerSeries.C 3 * X ^ 7 - PowerSeries.C 4 * X ^ 8 + PowerSeries.C 8 * X ^ 9 -
        PowerSeries.C 3 * X ^ 10 - PowerSeries.C 1 * X ^ 11 := by
    simp only [map_ofNat, map_one]
    ring
  rw [hpow, hrhs]
  have hmul : F * (1 - PowerSeries.C 5 * X ^ 1 + PowerSeries.C 10 * X ^ 2 -
        PowerSeries.C 10 * X ^ 3 + PowerSeries.C 5 * X ^ 4 - X ^ 5) =
      F - PowerSeries.C 5 * (F * X ^ 1) + PowerSeries.C 10 * (F * X ^ 2) -
        PowerSeries.C 10 * (F * X ^ 3) + PowerSeries.C 5 * (F * X ^ 4) - F * X ^ 5 := by ring
  rw [hmul]
  have hF : ∀ m : ℕ, PowerSeries.coeff m F = if m = 0 then (0 : ℚ) else (a m : ℚ) := by
    intro m; simp [F]
  ext n
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
    coeff_mul_X_pow_rat, hF]
  have h1 := a_one
  have h2 := a_two
  have ⟨h3, h4, h5, h6, h7⟩ := a_small_vals
  have ⟨h8, h9, h10, h11⟩ := a_vals_8_11
  by_cases hn : n ≤ 11
  · interval_cases n <;> norm_num [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  · have hn12 : 11 < n := by omega
    have hrec := a_recurrence n hn12
    have hrecQ : (a n : ℚ) =
        5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
      exact_mod_cast hrec
    have hc : ¬ n = 0 ∧ ¬ n - 1 = 0 ∧ ¬ n - 2 = 0 ∧ ¬ n - 3 = 0 ∧ ¬ n - 4 = 0 ∧ ¬ n - 5 = 0 ∧
        1 ≤ n ∧ 2 ≤ n ∧ 3 ≤ n ∧ 4 ≤ n ∧ 5 ≤ n ∧
        n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 5 ∧ n ≠ 6 ∧ n ≠ 7 ∧ n ≠ 8 ∧ n ≠ 9 ∧ n ≠ 10 ∧ n ≠ 11 := by
      omega
    simp only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1,
      hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.1,
      hc.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hc.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, ↓reduceIte]
    linarith

end OMA.P_oeis_a220035

theorem OMA.solution : type_of% @OMA.S_oeis_a220035.main :=
  ⟨OMA.P_oeis_a220035.gf_eq, OMA.P_oeis_a220035.a_recurrence⟩
