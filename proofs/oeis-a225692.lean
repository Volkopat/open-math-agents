import OMAStatements.S_oeis_a225692
import Mathlib

/-!
# Proof of OEIS A225692

Credit: @mbilenko03

A Dyck path of semilength `n ≥ 2` contains `U^(n-1) D^(n-1)` as a subsequence exactly when it is
the mountain `U^n D^n` or it has the shape `U^i D U^(n-1-i) D^(n-1-j) U D^j` for
`1 ≤ i, j ≤ n - 1`. There are `(n - 1) ^ 2 + 1` such paths, so
`a n = catalan n - ((n - 1) ^ 2 + 1)`. Mathar's recurrence is the Catalan recurrence applied to
that closed form, and Kotesovec's asymptotic is Stirling's approximation of the Catalan term.
-/

open OMA.S_oeis_a225692 Filter
open scoped Classical

noncomputable section

private def stepOf (b : Bool) : DyckStep :=
  match b with
  | true => DyckStep.U
  | false => DyckStep.D

private def boolOf (s : DyckStep) : Bool :=
  match s with
  | DyckStep.U => true
  | DyckStep.D => false

private lemma bool_stepOf (b : Bool) : boolOf (stepOf b) = b := by
  cases b <;> rfl

private lemma step_boolOf (s : DyckStep) : stepOf (boolOf s) = s := by
  cases s <;> rfl

private lemma count_step_U (l : List Bool) :
    (l.map stepOf).count DyckStep.U = l.count true := by
  induction l with
  | nil => simp [stepOf]
  | cons a t ih =>
    cases a <;> simp [stepOf, ih]

private lemma count_step_D (l : List Bool) :
    (l.map stepOf).count DyckStep.D = l.count false := by
  induction l with
  | nil => simp [stepOf]
  | cons a t ih =>
    cases a <;> simp [stepOf, ih]

private lemma count_bool_U (l : List DyckStep) :
    (l.map boolOf).count true = l.count DyckStep.U := by
  induction l with
  | nil => simp [boolOf]
  | cons a t ih =>
    cases a <;> simp [boolOf, ih]

private lemma count_bool_D (l : List DyckStep) :
    (l.map boolOf).count false = l.count DyckStep.D := by
  induction l with
  | nil => simp [boolOf]
  | cons a t ih =>
    cases a <;> simp [boolOf, ih]

private lemma step_bool_map (l : List DyckStep) : (l.map boolOf).map stepOf = l := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases a <;> simp [boolOf, stepOf, ih]

private lemma card_filter_succ {n : ℕ} (p : Fin (n + 1) → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card =
      (Finset.univ.filter (fun i : Fin n => p i.succ)).card + if p 0 then 1 else 0 := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ, add_comm]

private lemma count_ofFn {n : ℕ} (w : Fin n → Bool) (b : Bool) :
    (List.ofFn w).count b = (Finset.univ.filter (fun i : Fin n => w i = b)).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, ih (fun i => w i.succ)]
    simp only [beq_iff_eq]
    exact (card_filter_succ (fun i : Fin (n + 1) => w i = b)).symm

private lemma card_filter_lt {n k : ℕ} (hk : k ≤ n) (p : Fin n → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun i : Fin k => p ⟨i.val, by omega⟩)).card =
      (Finset.univ.filter (fun i : Fin n => i.val < k ∧ p i)).card := by
  refine Finset.card_bij
    (fun (i : Fin k) (_ : i ∈ Finset.univ.filter (fun j : Fin k => p ⟨j.val, by omega⟩)) =>
      (⟨i.val, by omega⟩ : Fin n))
    (fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact ⟨i.isLt, hi⟩)
    (fun i _ j _ h => by
      apply Fin.ext
      exact congrArg (fun (t : Fin n) => t.val) h)
    (fun t ht => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      refine ⟨⟨t.val, ht.1⟩, ?_, ?_⟩
      · simp [ht.2]
      · exact Fin.ext rfl)

private lemma count_take {n : ℕ} (w : Fin n → Bool) (b : Bool) (k : ℕ) (hk : k ≤ n) :
    ((List.ofFn w).take k).count b =
      (Finset.univ.filter (fun i : Fin n => i.val < k ∧ w i = b)).card := by
  let w' : Fin k → Bool := fun i => w ⟨i.val, by omega⟩
  have hlist : List.ofFn w' = (List.ofFn w).take k := by
    apply List.ext_getElem
    · simp [List.length_ofFn, List.length_take, hk]
    · intro i hi1 hi2
      simp only [w', List.getElem_ofFn, List.getElem_take]
  rw [← hlist, count_ofFn]
  exact card_filter_lt hk (fun i : Fin n => w i = b)

private lemma card_Ico {n a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) :
    (Finset.univ.filter (fun t : Fin n => a ≤ t.val ∧ t.val < b)).card = b - a := by
  let s := Finset.univ.filter (fun t : Fin n => a ≤ t.val ∧ t.val < b)
  let e : {t : Fin n // a ≤ t.val ∧ t.val < b} ≃ Fin (b - a) :=
    { toFun := fun t => ⟨t.1.val - a, by
        have h1 := t.2.1
        have h2 := t.2.2
        omega⟩
      invFun := fun i =>
        ⟨⟨a + i.val, by
            have hi := i.isLt
            omega⟩, by
          simp only [Fin.val_mk]
          have hi := i.isLt
          omega⟩
      left_inv := by
        rintro ⟨t, ht⟩
        apply Subtype.ext
        apply Fin.ext
        simp only [Fin.val_mk]
        have h1 := ht.1
        have h2 := ht.2
        omega
      right_inv := by
        intro i
        apply Fin.ext
        simp only [Fin.val_mk]
        omega }
  have hsub : Fintype.card {t : Fin n // a ≤ t.val ∧ t.val < b} = s.card :=
    Fintype.card_of_subtype s (fun t => by
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and])
  rw [← hsub, Fintype.card_congr e, Fintype.card_fin]

private lemma card_split_bool {n k : ℕ} (hk : k ≤ n) (w : Fin n → Bool) :
    (Finset.univ.filter (fun t : Fin n => t.val < k ∧ w t = true)).card +
        (Finset.univ.filter (fun t : Fin n => t.val < k ∧ w t = false)).card = k := by
  have hdisj : Disjoint
      (Finset.univ.filter (fun t : Fin n => t.val < k ∧ w t = true))
      (Finset.univ.filter (fun t : Fin n => t.val < k ∧ w t = false)) := by
    rw [Finset.disjoint_filter]
    intro t _ h1 h2
    cases w t <;> simp_all
  have hunion :
      (Finset.univ.filter (fun t : Fin n => t.val < k ∧ w t = true)) ∪
          (Finset.univ.filter (fun t : Fin n => t.val < k ∧ w t = false)) =
        Finset.univ.filter (fun t : Fin n => t.val < k) := by
    ext t
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases w t <;> simp
  have hI : (Finset.univ.filter (fun t : Fin n => t.val < k)).card = k := by
    have heq :
        Finset.univ.filter (fun t : Fin n => 0 ≤ t.val ∧ t.val < k) =
          Finset.univ.filter (fun t : Fin n => t.val < k) := by
      ext t
      simp
    rw [← heq]
    exact card_Ico (by omega) hk
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, hI] at hcard
  exact hcard.symm

private lemma card_cut {n c : ℕ} (hc : c ≤ n) (w : Fin n → Bool) (b : Bool) :
    (Finset.univ.filter (fun t : Fin n => t.val < c ∧ w t = b)).card +
        (Finset.univ.filter (fun t : Fin n => c ≤ t.val ∧ w t = b)).card =
      (Finset.univ.filter (fun t : Fin n => w t = b)).card := by
  have hdisj : Disjoint
      (Finset.univ.filter (fun t : Fin n => t.val < c ∧ w t = b))
      (Finset.univ.filter (fun t : Fin n => c ≤ t.val ∧ w t = b)) := by
    rw [Finset.disjoint_filter]
    intro t _ h1 h2
    omega
  have hunion :
      (Finset.univ.filter (fun t : Fin n => t.val < c ∧ w t = b)) ∪
          (Finset.univ.filter (fun t : Fin n => c ≤ t.val ∧ w t = b)) =
        Finset.univ.filter (fun t : Fin n => w t = b) := by
    ext t
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h)
      · exact h.2
      · exact h.2
    · intro hb
      by_cases hlt : t.val < c
      · exact Or.inl ⟨hlt, hb⟩
      · exact Or.inr ⟨by omega, hb⟩
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion] at hcard
  exact hcard.symm

private lemma false_card_dyck {n : ℕ} {w : Fin (2 * n) → Bool}
    (ht : (Finset.univ.filter (fun t : Fin (2 * n) => w t = true)).card = n) :
    (Finset.univ.filter (fun t : Fin (2 * n) => w t = false)).card = n := by
  have h := card_split_bool (n := 2 * n) (k := 2 * n) le_rfl w
  have ht' :
      Finset.univ.filter (fun t : Fin (2 * n) => t.val < 2 * n ∧ w t = true) =
        Finset.univ.filter (fun t : Fin (2 * n) => w t = true) := by
    ext t
    simp [t.isLt]
  have hf' :
      Finset.univ.filter (fun t : Fin (2 * n) => t.val < 2 * n ∧ w t = false) =
        Finset.univ.filter (fun t : Fin (2 * n) => w t = false) := by
    ext t
    simp [t.isLt]
  rw [ht', hf', ht] at h
  omega

private def wordOfDyck {n : ℕ} (w : Fin (2 * n) → Bool) (hw : IsDyck n w) : DyckWord :=
  DyckWord.mk ((List.ofFn w).map stepOf)
    (by
      rw [count_step_U, count_step_D, count_ofFn, count_ofFn]
      exact hw.1.trans (false_card_dyck hw.1).symm)
    (by
      intro k
      by_cases hk : k ≤ 2 * n
      · rw [← List.map_take, count_step_D, count_step_U, count_take w false k hk,
          count_take w true k hk]
        exact hw.2 k hk
      · have hlen : ((List.ofFn w).map stepOf).length = 2 * n := by
          simp [List.length_ofFn]
        rw [List.take_of_length_le (by omega : ((List.ofFn w).map stepOf).length ≤ k)]
        rw [count_step_D, count_step_U, count_ofFn, count_ofFn]
        exact le_of_eq ((false_card_dyck hw.1).trans hw.1.symm))

private lemma wordOfDyck_semilength {n : ℕ} (w : Fin (2 * n) → Bool) (hw : IsDyck n w) :
    (wordOfDyck w hw).semilength = n := by
  simp only [DyckWord.semilength, wordOfDyck]
  rw [count_step_U, count_ofFn]
  exact hw.1

private def funOfWord {n : ℕ} (p : {q : DyckWord // q.semilength = n}) : Fin (2 * n) → Bool :=
  fun i => boolOf (p.1.toList[i.val]'(by
    have hlen := p.1.two_mul_semilength_eq_length
    rw [p.2] at hlen
    omega))

private lemma ofFn_word {n : ℕ} (p : {q : DyckWord // q.semilength = n}) :
    List.ofFn (funOfWord p) = p.1.toList.map boolOf := by
  have hlen : p.1.toList.length = 2 * n := by
    have h := p.1.two_mul_semilength_eq_length
    rw [p.2] at h
    exact h.symm
  apply List.ext_getElem
  · simp [List.length_ofFn, List.length_map, hlen]
  · intro i hi1 hi2
    simp [funOfWord, List.getElem_ofFn, List.getElem_map]

private lemma funOfWord_isDyck {n : ℕ} (p : {q : DyckWord // q.semilength = n}) :
    IsDyck n (funOfWord p) := by
  have hof := ofFn_word p
  constructor
  · rw [← count_ofFn, hof, count_bool_U]
    simpa [DyckWord.semilength] using p.2
  · intro k hk
    rw [← count_take (funOfWord p) false k hk, ← count_take (funOfWord p) true k hk, hof,
      ← List.map_take, count_bool_D, count_bool_U]
    exact p.1.count_D_le_count_U k

private def dyckEquiv (n : ℕ) :
    {w : Fin (2 * n) → Bool // IsDyck n w} ≃ {p : DyckWord // p.semilength = n} where
  toFun w := ⟨wordOfDyck w.1 w.2, wordOfDyck_semilength w.1 w.2⟩
  invFun p := ⟨funOfWord p, funOfWord_isDyck p⟩
  left_inv w := by
    ext t
    simp only [funOfWord, wordOfDyck]
    rw [List.getElem_map, List.getElem_ofFn, bool_stepOf]
  right_inv p := by
    apply Subtype.ext
    apply DyckWord.ext
    simp only [wordOfDyck]
    rw [ofFn_word p, step_bool_map]

private lemma card_dyck (n : ℕ) :
    Nat.card {w : Fin (2 * n) → Bool // IsDyck n w} = catalan n := by
  rw [Nat.card_congr (dyckEquiv n), Nat.card_eq_fintype_card,
    DyckWord.card_dyckWord_semilength_eq_catalan]

private def mountainFun (n : ℕ) (t : Fin (2 * n)) : Bool :=
  if t.val < n then true else false

private def shapeFun (n i j : ℕ) (t : Fin (2 * n)) : Bool :=
  if t.val < i then true
  else if t.val = i then false
  else if t.val < n then true
  else if t.val < 2 * n - 1 - j then false
  else if t.val = 2 * n - 1 - j then true
  else false

private lemma shape_eq_early {n i j : ℕ} (hi : i ≤ n - 1) (t : Fin (2 * n)) (ht : t.val < n) :
    shapeFun n i j t = true ↔ t.val ≠ i := by
  unfold shapeFun
  by_cases h1 : t.val < i
  · rw [if_pos h1]
    constructor
    · intro _
      omega
    · intro _
      rfl
  · rw [if_neg h1]
    by_cases h2 : t.val = i
    · rw [if_pos h2]
      constructor
      · intro h
        cases h
      · intro h
        omega
    · rw [if_neg h2]
      rw [if_pos ht]
      constructor
      · intro _
        exact h2
      · intro _
        rfl

private lemma shape_eq_late {n i j : ℕ} (hi : i ≤ n - 1) (hj : j ≤ n - 1)
    (t : Fin (2 * n)) (ht : n ≤ t.val) :
    shapeFun n i j t = true ↔ t.val = 2 * n - 1 - j := by
  unfold shapeFun
  rw [if_neg (by omega : ¬ t.val < i), if_neg (by omega : ¬ t.val = i),
    if_neg (by omega : ¬ t.val < n)]
  by_cases h4 : t.val < 2 * n - 1 - j
  · rw [if_pos h4]
    constructor
    · intro h
      cases h
    · intro h
      omega
  · rw [if_neg h4]
    by_cases h5 : t.val = 2 * n - 1 - j
    · rw [if_pos h5]
      constructor
      · intro _
        exact h5
      · intro _
        rfl
    · rw [if_neg h5]
      constructor
      · intro h
        cases h
      · intro h
        omega

private lemma shape_ups {n i j k : ℕ} (hn : 2 ≤ n) (hi : 1 ≤ i ∧ i ≤ n - 1)
    (hj : 1 ≤ j ∧ j ≤ n - 1) (hk : k ≤ 2 * n) :
    (Finset.univ.filter (fun t : Fin (2 * n) => t.val < k ∧ shapeFun n i j t = true)).card =
      if k ≤ i then k
      else if k ≤ n then k - 1
      else if k ≤ 2 * n - 1 - j then n - 1
      else n := by
  have hp4 : n ≤ 2 * n - 1 - j := by omega
  by_cases h1 : k ≤ i
  · have heq :
        Finset.univ.filter (fun t : Fin (2 * n) => t.val < k ∧ shapeFun n i j t = true) =
          Finset.univ.filter (fun t : Fin (2 * n) => 0 ≤ t.val ∧ t.val < k) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact ⟨Nat.zero_le _, h.1⟩
      · intro h
        refine ⟨h.2, ?_⟩
        exact (shape_eq_early hi.2 t (by omega)).mpr (by omega)
    rw [if_pos h1, heq]
    exact card_Ico (by omega) (by omega)
  · by_cases h2 : k ≤ n
    · have hik : i + 1 ≤ k := by omega
      let A := Finset.univ.filter (fun t : Fin (2 * n) => 0 ≤ t.val ∧ t.val < i)
      let B := Finset.univ.filter (fun t : Fin (2 * n) => i + 1 ≤ t.val ∧ t.val < k)
      have hd : Disjoint A B := by
        rw [Finset.disjoint_filter]
        intro t _ hA hB
        omega
      have hunion :
          A ∪ B =
            Finset.univ.filter (fun t : Fin (2 * n) => t.val < k ∧ shapeFun n i j t = true) := by
        ext t
        simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro (h | h)
          · exact ⟨by omega, (shape_eq_early hi.2 t (by omega)).mpr (by omega)⟩
          · exact ⟨h.2, (shape_eq_early hi.2 t (by omega)).mpr (by omega)⟩
        · intro h
          have hne : t.val ≠ i := (shape_eq_early hi.2 t (by omega)).mp h.2
          by_cases hlt : t.val < i
          · exact Or.inl ⟨Nat.zero_le _, hlt⟩
          · exact Or.inr ⟨by omega, h.1⟩
      have hcard := Finset.card_union_of_disjoint hd
      rw [hunion] at hcard
      have hA : A.card = i := card_Ico (by omega) (by omega)
      have hB : B.card = k - (i + 1) := card_Ico hik (by omega)
      rw [hA, hB] at hcard
      rw [if_neg h1, if_pos h2]
      omega
    · by_cases h3 : k ≤ 2 * n - 1 - j
      · let A := Finset.univ.filter (fun t : Fin (2 * n) => 0 ≤ t.val ∧ t.val < i)
        let B := Finset.univ.filter (fun t : Fin (2 * n) => i + 1 ≤ t.val ∧ t.val < n)
        have hd : Disjoint A B := by
          rw [Finset.disjoint_filter]
          intro t _ hA hB
          omega
        have hunion :
            A ∪ B =
              Finset.univ.filter (fun t : Fin (2 * n) => t.val < k ∧ shapeFun n i j t = true) := by
          ext t
          simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro (h | h)
            · exact ⟨by omega, (shape_eq_early hi.2 t (by omega)).mpr (by omega)⟩
            · exact ⟨by omega, (shape_eq_early hi.2 t h.2).mpr (by omega)⟩
          · intro h
            by_cases htn : t.val < n
            · have hne : t.val ≠ i := (shape_eq_early hi.2 t htn).mp h.2
              by_cases hlt : t.val < i
              · exact Or.inl ⟨Nat.zero_le _, hlt⟩
              · exact Or.inr ⟨by omega, htn⟩
            · have hlate := (shape_eq_late hi.2 hj.2 t (by omega)).mp h.2
              omega
        have hcard := Finset.card_union_of_disjoint hd
        rw [hunion] at hcard
        have hA : A.card = i := card_Ico (by omega) (by omega)
        have hB : B.card = n - (i + 1) := card_Ico (by omega) (by omega)
        rw [hA, hB] at hcard
        rw [if_neg h1, if_neg h2, if_pos h3]
        omega
      · let A := Finset.univ.filter (fun t : Fin (2 * n) => 0 ≤ t.val ∧ t.val < i)
        let B := Finset.univ.filter (fun t : Fin (2 * n) => i + 1 ≤ t.val ∧ t.val < n)
        let C := Finset.univ.filter
          (fun t : Fin (2 * n) => 2 * n - 1 - j ≤ t.val ∧ t.val < 2 * n - 1 - j + 1)
        have hdAB : Disjoint A B := by
          rw [Finset.disjoint_filter]
          intro t _ hA hB
          omega
        have hdAC : Disjoint A C := by
          rw [Finset.disjoint_filter]
          intro t _ hA hC
          omega
        have hdBC : Disjoint B C := by
          rw [Finset.disjoint_filter]
          intro t _ hB hC
          omega
        have hd : Disjoint (A ∪ B) C := by
          rw [Finset.disjoint_union_left]
          exact ⟨hdAC, hdBC⟩
        have hunion :
            A ∪ B ∪ C =
              Finset.univ.filter (fun t : Fin (2 * n) => t.val < k ∧ shapeFun n i j t = true) := by
          ext t
          simp only [A, B, C, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ((h | h) | h)
            · exact ⟨by omega, (shape_eq_early hi.2 t (by omega)).mpr (by omega)⟩
            · exact ⟨by omega, (shape_eq_early hi.2 t h.2).mpr (by omega)⟩
            · have ht : t.val = 2 * n - 1 - j := by omega
              exact ⟨by omega, (shape_eq_late hi.2 hj.2 t (by omega)).mpr ht⟩
          · intro h
            by_cases htn : t.val < n
            · have hne : t.val ≠ i := (shape_eq_early hi.2 t htn).mp h.2
              by_cases hlt : t.val < i
              · exact Or.inl (Or.inl ⟨Nat.zero_le _, hlt⟩)
              · exact Or.inl (Or.inr ⟨by omega, htn⟩)
            · have ht := (shape_eq_late hi.2 hj.2 t (by omega)).mp h.2
              exact Or.inr ⟨by omega, by omega⟩
        have hcard := Finset.card_union_of_disjoint hd
        have hAB := Finset.card_union_of_disjoint hdAB
        rw [hunion, hAB] at hcard
        have hA : A.card = i := card_Ico (by omega) (by omega)
        have hB : B.card = n - (i + 1) := card_Ico (by omega) (by omega)
        have hC : C.card = 1 := by
          have hc := card_Ico (n := 2 * n) (a := 2 * n - 1 - j) (b := 2 * n - 1 - j + 1)
            (by omega) (by omega)
          have hsub : (2 * n - 1 - j + 1) - (2 * n - 1 - j) = 1 := by omega
          rw [← hsub]
          simpa only [C] using hc
        rw [hA, hB, hC] at hcard
        rw [if_neg h1, if_neg h2, if_neg h3]
        omega

private lemma shape_isDyck {n i j : ℕ} (hn : 2 ≤ n) (hi : 1 ≤ i ∧ i ≤ n - 1)
    (hj : 1 ≤ j ∧ j ≤ n - 1) : IsDyck n (shapeFun n i j) := by
  constructor
  · have h := shape_ups hn hi hj (k := 2 * n) le_rfl
    have h1 : ¬ 2 * n ≤ i := by omega
    have h2 : ¬ 2 * n ≤ n := by omega
    have h3 : ¬ 2 * n ≤ 2 * n - 1 - j := by omega
    simp only [h1, h2, h3, ite_false] at h
    have hfilt :
        (Finset.univ.filter (fun t : Fin (2 * n) => t.val < 2 * n ∧ shapeFun n i j t = true)) =
          (Finset.univ.filter (fun t : Fin (2 * n) => shapeFun n i j t = true)) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨And.right, fun hp => ⟨t.isLt, hp⟩⟩
    rw [hfilt] at h
    exact h
  · intro k hk
    have hup := shape_ups hn hi hj hk
    have hsplit := card_split_bool hk (shapeFun n i j)
    rw [hup] at hsplit ⊢
    by_cases h1 : k ≤ i
    · rw [if_pos h1] at hsplit ⊢
      omega
    · by_cases h2 : k ≤ n
      · rw [if_neg h1, if_pos h2] at hsplit ⊢
        omega
      · by_cases h3 : k ≤ 2 * n - 1 - j
        · rw [if_neg h1, if_neg h2, if_pos h3] at hsplit ⊢
          omega
        · rw [if_neg h1, if_neg h2, if_neg h3] at hsplit ⊢
          omega

private lemma mountain_ups {n k : ℕ} (hk : k ≤ 2 * n) :
    (Finset.univ.filter (fun t : Fin (2 * n) => t.val < k ∧ mountainFun n t = true)).card =
      min k n := by
  have heq :
      Finset.univ.filter (fun t : Fin (2 * n) => t.val < k ∧ mountainFun n t = true) =
        Finset.univ.filter (fun t : Fin (2 * n) => 0 ≤ t.val ∧ t.val < min k n) := by
    ext t
    constructor
    · intro ht
      have h := (Finset.mem_filter.mp ht).2
      have htn : t.val < n := by
        by_contra hge
        have hb := h.2
        simp only [mountainFun, if_neg hge] at hb
        cases hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨Nat.zero_le _, lt_min h.1 htn⟩⟩
    · intro ht
      have h := (Finset.mem_filter.mp ht).2
      have htn : t.val < n := lt_of_lt_of_le h.2 (min_le_right _ _)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ⟨lt_of_lt_of_le h.2 (min_le_left _ _), by
          simp only [mountainFun, if_pos htn]⟩⟩
  rw [heq]
  exact card_Ico (by omega) (by omega)

private lemma mountain_isDyck {n : ℕ} (hn : 1 ≤ n) : IsDyck n (mountainFun n) := by
  constructor
  · have h := mountain_ups (n := n) (k := 2 * n) le_rfl
    have hfilt :
        (Finset.univ.filter (fun t : Fin (2 * n) => t.val < 2 * n ∧ mountainFun n t = true)) =
          (Finset.univ.filter (fun t : Fin (2 * n) => mountainFun n t = true)) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨And.right, fun hp => ⟨t.isLt, hp⟩⟩
    rw [hfilt, min_eq_right (by omega : n ≤ 2 * n)] at h
    exact h
  · intro k hk
    have hup := mountain_ups hk
    have hsplit := card_split_bool hk (mountainFun n)
    rw [hup] at hsplit
    by_cases hk' : k ≤ n
    · rw [min_eq_left hk'] at hsplit
      omega
    · rw [min_eq_right (by omega : n ≤ k)] at hsplit
      omega

private def shapeSlot (n i j : ℕ) (k : Fin (2 * (n - 1))) : Fin (2 * n) :=
  if hk : k.val < n - 1 then
    if k.val < i then ⟨k.val, by have := k.isLt; omega⟩
    else ⟨k.val + 1, by have := k.isLt; omega⟩
  else
    let s := k.val - (n - 1)
    if s < n - 1 - j then ⟨n + s, by have := k.isLt; omega⟩
    else ⟨n + s + 1, by have := k.isLt; omega⟩

private lemma shapeSlot_val_early {n i j : ℕ} (k : Fin (2 * (n - 1))) (hk : k.val < n - 1) :
    (shapeSlot n i j k).val = if k.val < i then k.val else k.val + 1 := by
  simp only [shapeSlot, hk]
  split_ifs <;> rfl

private lemma shapeSlot_val_late {n i j : ℕ} (k : Fin (2 * (n - 1))) (hk : ¬ k.val < n - 1) :
    (shapeSlot n i j k).val =
      if k.val - (n - 1) < n - 1 - j then n + (k.val - (n - 1))
      else n + (k.val - (n - 1)) + 1 := by
  rw [shapeSlot]
  simp only [dif_neg hk]
  split_ifs <;> rfl

private lemma shapeSlot_strict {n i j : ℕ} (hn : 2 ≤ n) : StrictMono (shapeSlot n i j) := by
  intro a b hab
  rw [Fin.lt_def] at hab ⊢
  by_cases ha : a.val < n - 1 <;> by_cases hb : b.val < n - 1
  · rw [shapeSlot_val_early a ha, shapeSlot_val_early b hb]
    split_ifs <;> omega
  · rw [shapeSlot_val_early a ha, shapeSlot_val_late b hb]
    split_ifs <;> omega
  · omega
  · rw [shapeSlot_val_late a ha, shapeSlot_val_late b hb]
    split_ifs <;> omega

private lemma shapeSlot_up {n i j : ℕ} (hn : 2 ≤ n) (hi : 1 ≤ i ∧ i ≤ n - 1)
    (hj : 1 ≤ j ∧ j ≤ n - 1) (k : Fin (2 * (n - 1))) (hk : k.val < n - 1) :
    shapeFun n i j (shapeSlot n i j k) = true := by
  by_cases hk2 : k.val < i
  · have hval : (shapeSlot n i j k).val = k.val := by
      rw [shapeSlot_val_early k hk, if_pos hk2]
    have htn : (shapeSlot n i j k).val < n := by
      rw [hval]
      omega
    exact (shape_eq_early hi.2 (shapeSlot n i j k) htn).mpr (by rw [hval]; omega)
  · have hval : (shapeSlot n i j k).val = k.val + 1 := by
      rw [shapeSlot_val_early k hk, if_neg hk2]
    have htn : (shapeSlot n i j k).val < n := by
      rw [hval]
      omega
    exact (shape_eq_early hi.2 (shapeSlot n i j k) htn).mpr (by rw [hval]; omega)

private lemma shapeSlot_down {n i j : ℕ} (hn : 2 ≤ n) (hi : 1 ≤ i ∧ i ≤ n - 1)
    (hj : 1 ≤ j ∧ j ≤ n - 1) (k : Fin (2 * (n - 1))) (hk : n - 1 ≤ k.val) :
    shapeFun n i j (shapeSlot n i j k) = false := by
  have hlt : ¬ k.val < n - 1 := by omega
  have hval := shapeSlot_val_late (i := i) (j := j) k hlt
  have hge : n ≤ (shapeSlot n i j k).val := by
    rw [hval]
    split_ifs <;> omega
  have hne : (shapeSlot n i j k).val ≠ 2 * n - 1 - j := by
    rw [hval]
    split_ifs with hs
    · omega
    · omega
  have hnot : ¬ shapeFun n i j (shapeSlot n i j k) = true := by
    intro ht
    exact hne ((shape_eq_late hi.2 hj.2 (shapeSlot n i j k) hge).mp ht)
  cases hv : shapeFun n i j (shapeSlot n i j k)
  · rfl
  · exact absurd hv hnot

private lemma shape_pattern {n i j : ℕ} (hn : 2 ≤ n) (hi : 1 ≤ i ∧ i ≤ n - 1)
    (hj : 1 ≤ j ∧ j ≤ n - 1) : ContainsPattern n (shapeFun n i j) := by
  refine ⟨shapeSlot n i j, shapeSlot_strict (i := i) (j := j) hn, ?_, ?_⟩
  · intro k hk
    exact shapeSlot_up hn hi hj k hk
  · intro k hk
    exact shapeSlot_down hn hi hj k hk

private def mountainSlot (n : ℕ) (k : Fin (2 * (n - 1))) : Fin (2 * n) :=
  if hk : k.val < n - 1 then ⟨k.val, by have := k.isLt; omega⟩
  else ⟨n + (k.val - (n - 1)), by have := k.isLt; omega⟩

private lemma mountainSlot_strict {n : ℕ} (hn : 2 ≤ n) : StrictMono (mountainSlot n) := by
  intro a b hab
  rw [Fin.lt_iff_val_lt_val] at hab ⊢
  by_cases ha : a.val < n - 1 <;> by_cases hb : b.val < n - 1
  · simp [mountainSlot, ha, hb, hab]
  · simp [mountainSlot, ha, hb]
    omega
  · omega
  · simp [mountainSlot, ha, hb]
    omega

private lemma mountain_pattern {n : ℕ} (hn : 2 ≤ n) : ContainsPattern n (mountainFun n) := by
  refine ⟨mountainSlot n, mountainSlot_strict hn, ?_, ?_⟩
  · intro k hk
    simp only [mountainSlot, hk, mountainFun]
    exact if_pos (by omega : k.val < n)
  · intro k hk
    simp only [mountainSlot, show ¬ k.val < n - 1 by omega, mountainFun]
    exact if_neg (by omega : ¬ n + (k.val - (n - 1)) < n)

private def downSet (n : ℕ) (w : Fin (2 * n) → Bool) : Finset (Fin (2 * n)) :=
  Finset.univ.filter (fun t => t.val < n ∧ w t = false)

private def lateUpSet (n : ℕ) (w : Fin (2 * n) → Bool) : Finset (Fin (2 * n)) :=
  Finset.univ.filter (fun t => n ≤ t.val ∧ w t = true)

private lemma card_le_lt {n k : ℕ} (hk : k ≤ n) (p : Fin n → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun t : Fin n => t.val < k ∧ p t)).card ≤ k := by
  have hsub :
      Finset.univ.filter (fun t : Fin n => t.val < k ∧ p t) ⊆
        Finset.univ.filter (fun t : Fin n => 0 ≤ t.val ∧ t.val < k) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ⟨Nat.zero_le _, ht.1⟩
  have hc := card_Ico (n := n) (a := 0) (b := k) (Nat.zero_le _) hk
  rw [Nat.sub_zero] at hc
  exact (Finset.card_le_card hsub).trans (le_of_eq hc)

private lemma card_ge_of_embed {n m : ℕ} {p : Fin n → Prop} [DecidablePred p]
    (f : Fin m → Fin n) (hf : Function.Injective f) (hmem : ∀ i, p (f i)) :
    m ≤ (Finset.univ.filter p).card := by
  let g : Fin m → {t : Fin n // p t} := fun i => ⟨f i, hmem i⟩
  have hg : Function.Injective g := by
    intro a b h
    exact hf (congrArg Subtype.val h)
  have hle := Fintype.card_le_of_injective g hg
  have hcard : Fintype.card {t : Fin n // p t} = (Finset.univ.filter p).card :=
    Fintype.card_of_subtype _ (fun t => by simp)
  rw [Fintype.card_fin] at hle
  rwa [hcard] at hle

private lemma early_down_le_one {n : ℕ} (hn : 2 ≤ n) {w : Fin (2 * n) → Bool}
    (hw : IsDyck n w) (hc : ContainsPattern n w) : (downSet n w).card ≤ 1 := by
  obtain ⟨ι, hmono, hup, hdown⟩ := hc
  let iU : Fin (2 * (n - 1)) := ⟨n - 1, by omega⟩
  set p0 : ℕ := (ι iU).val
  have hp0_le : p0 ≤ 2 * n := by
    have := (ι iU).isLt
    omega
  have hups : n - 1 ≤
      (Finset.univ.filter (fun t : Fin (2 * n) => t.val < p0 ∧ w t = true)).card := by
    refine card_ge_of_embed (fun r : Fin (n - 1) => ι ⟨r.val, by have := r.isLt; omega⟩) ?_ ?_
    · intro a b h
      apply Fin.ext
      exact congrArg (fun (t : Fin (2 * (n - 1))) => t.val) (hmono.injective h)
    · intro r
      refine ⟨?_, hup ⟨r.val, by have := r.isLt; omega⟩ r.isLt⟩
      have hlt : (⟨r.val, by have := r.isLt; omega⟩ : Fin (2 * (n - 1))) < iU := by
        rw [Fin.lt_iff_val_lt_val]
        exact r.isLt
      exact (Fin.lt_iff_val_lt_val).mp (hmono hlt)
  have hdowns : n - 1 ≤
      (Finset.univ.filter (fun t : Fin (2 * n) => p0 ≤ t.val ∧ w t = false)).card := by
    refine card_ge_of_embed
      (fun r : Fin (n - 1) => ι ⟨r.val + (n - 1), by have := r.isLt; omega⟩) ?_ ?_
    · intro a b h
      apply Fin.ext
      have hv := congrArg (fun (t : Fin (2 * (n - 1))) => t.val) (hmono.injective h)
      simp only [Fin.val_mk] at hv
      omega
    · intro r
      have hembed : r.val + (n - 1) < 2 * (n - 1) := by omega
      have hidx : n - 1 ≤ (⟨r.val + (n - 1), hembed⟩ : Fin (2 * (n - 1))).val := by
        simp only [Fin.val_mk]
        omega
      refine ⟨?_, hdown ⟨r.val + (n - 1), hembed⟩ hidx⟩
      have hr : iU ≤ ⟨r.val + (n - 1), hembed⟩ := by
        rw [Fin.le_def]
        simp only [Fin.val_mk, iU]
        omega
      by_cases heq : iU = ⟨r.val + (n - 1), hembed⟩
      · rw [← heq]
      · exact (Fin.lt_def.mp (hmono (lt_of_le_of_ne hr heq))).le
  have hfalse := false_card_dyck hw.1
  have hcut := card_cut (n := 2 * n) (c := p0) hp0_le w false
  rw [hfalse] at hcut
  have hbefore :
      (Finset.univ.filter (fun t : Fin (2 * n) => t.val < p0 ∧ w t = false)).card ≤ 1 := by
    omega
  have hp0_ge : n - 1 ≤ p0 := by
    have hle := card_le_lt (n := 2 * n) (k := p0) (by omega)
      (fun t : Fin (2 * n) => w t = true)
    omega
  by_cases hpn : n ≤ p0
  · have hsub : downSet n w ⊆
        Finset.univ.filter (fun t : Fin (2 * n) => t.val < p0 ∧ w t = false) := by
      intro t ht
      simp only [downSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact ⟨by omega, ht.2⟩
    exact le_trans (Finset.card_le_card hsub) hbefore
  · have hp0 : p0 = n - 1 := by omega
    have hup_eq :
        (Finset.univ.filter (fun t : Fin (2 * n) => t.val < p0 ∧ w t = true)).card = p0 := by
      have hle := card_le_lt (n := 2 * n) (k := p0) (by omega)
        (fun t : Fin (2 * n) => w t = true)
      omega
    have hzero :
        (Finset.univ.filter (fun t : Fin (2 * n) => t.val < p0 ∧ w t = false)).card = 0 := by
      have hsplit := card_split_bool (n := 2 * n) (k := p0) (by omega) w
      omega
    have honly : downSet n w ⊆
        Finset.univ.filter (fun t : Fin (2 * n) => t.val = n - 1 ∧ w t = false) := by
      intro t ht
      simp only [downSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      have hnot : ¬ t.val < p0 := by
        intro hlt
        have hmem : t ∈ Finset.univ.filter (fun u : Fin (2 * n) => u.val < p0 ∧ w u = false) := by
          simp [hlt, ht.2]
        rw [Finset.card_eq_zero.mp hzero] at hmem
        simp at hmem
      exact ⟨by omega, ht.2⟩
    have hcard1 :
        (Finset.univ.filter (fun t : Fin (2 * n) => t.val = n - 1 ∧ w t = false)).card ≤ 1 := by
      have hsub :
          Finset.univ.filter (fun t : Fin (2 * n) => t.val = n - 1 ∧ w t = false) ⊆
            {⟨n - 1, by omega⟩} := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and] at ht ⊢
        exact Fin.ext ht.1
      simpa using Finset.card_le_card hsub
    exact le_trans (Finset.card_le_card honly) hcard1

private def theOne {α : Type*} (s : Finset α) (h : s.card = 1) : α :=
  (Finset.card_eq_one.mp h).choose

private lemma theOne_spec {α : Type*} (s : Finset α) (h : s.card = 1) : s = {theOne s h} :=
  (Finset.card_eq_one.mp h).choose_spec

private lemma theOne_mem {α : Type*} (s : Finset α) (h : s.card = 1) : theOne s h ∈ s := by
  have hself := Finset.mem_singleton_self (theOne s h)
  rwa [← theOne_spec s h] at hself

private lemma theOne_eq_of_singleton {α : Type*} (s : Finset α) (h : s.card = 1) {x : α}
    (hs : s = {x}) : theOne s h = x := by
  exact Finset.mem_singleton.mp
    (Eq.mp (congrArg (fun t : Finset α => theOne s h ∈ t) hs) (theOne_mem s h))

private lemma shape_down_singleton {n i j : ℕ} (hn : 2 ≤ n) (hi : 1 ≤ i ∧ i ≤ n - 1)
    (hj : 1 ≤ j ∧ j ≤ n - 1) :
    downSet n (shapeFun n i j) = {⟨i, by omega⟩} := by
  ext t
  simp only [downSet, Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and]
  constructor
  · intro h
    apply Fin.ext
    simp only [Fin.val_mk]
    have hne : ¬ shapeFun n i j t = true := by rw [h.2]; decide
    have hnot : ¬ t.val ≠ i := by
      intro hval
      exact hne ((shape_eq_early hi.2 t h.1).mpr hval)
    omega
  · intro ht
    have hv : t.val = i := by
      simpa only [Fin.val_mk] using congrArg Fin.val ht
    have htn : t.val < n := by
      have hi' : i < n := by omega
      omega
    refine ⟨htn, ?_⟩
    have hne : ¬ shapeFun n i j t = true := by
      intro hs
      exact ((shape_eq_early hi.2 t htn).mp hs) hv
    cases hshape : shapeFun n i j t
    · rfl
    · exact absurd hshape hne

private lemma shape_late_singleton {n i j : ℕ} (hn : 2 ≤ n) (hi : 1 ≤ i ∧ i ≤ n - 1)
    (hj : 1 ≤ j ∧ j ≤ n - 1) :
    lateUpSet n (shapeFun n i j) = {⟨2 * n - 1 - j, by omega⟩} := by
  ext t
  simp only [lateUpSet, Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and]
  constructor
  · intro h
    have ht := (shape_eq_late hi.2 hj.2 t h.1).mp h.2
    exact Fin.ext ht
  · intro ht
    have hv : t.val = 2 * n - 1 - j := by
      simpa only [Fin.val_mk] using congrArg Fin.val ht
    have hge : n ≤ t.val := by omega
    exact ⟨hge, (shape_eq_late hi.2 hj.2 t hge).mpr hv⟩

private lemma mountain_down_empty {n : ℕ} (hn : 1 ≤ n) : (downSet n (mountainFun n)).card = 0 := by
  rw [Finset.card_eq_zero]
  ext t
  constructor
  · intro ht
    have h := (Finset.mem_filter.mp ht).2
    have hb := h.2
    simp only [mountainFun, if_pos h.1] at hb
    cases hb
  · intro ht
    exact (Finset.notMem_empty t ht).elim

private lemma zero_early_mountain {n : ℕ} (hn : 2 ≤ n) {w : Fin (2 * n) → Bool}
    (hw : IsDyck n w) (h0 : (downSet n w).card = 0) : w = mountainFun n := by
  funext t
  by_cases ht : t.val < n
  · have htrue : w t = true := by
      cases hv : w t
      · have hmem : t ∈ downSet n w := by simp [downSet, ht, hv]
        rw [Finset.card_eq_zero.mp h0] at hmem
        simp at hmem
      · rfl
    simp [mountainFun, ht, htrue]
  · have hearly :
        (Finset.univ.filter (fun u : Fin (2 * n) => u.val < n ∧ w u = true)).card = n := by
      have hsplit := card_split_bool (n := 2 * n) (k := n) (by omega) w
      have hdown :
          (Finset.univ.filter (fun u : Fin (2 * n) => u.val < n ∧ w u = false)).card = 0 := by
        simpa [downSet] using h0
      omega
    have hlate :
        (Finset.univ.filter (fun u : Fin (2 * n) => n ≤ u.val ∧ w u = true)).card = 0 := by
      have hcut := card_cut (n := 2 * n) (c := n) (by omega) w true
      rw [hw.1, hearly] at hcut
      omega
    have hfalse : w t = false := by
      cases hv : w t
      · rfl
      · have hmem : t ∈ Finset.univ.filter (fun u : Fin (2 * n) => n ≤ u.val ∧ w u = true) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨by omega, hv⟩
        rw [Finset.card_eq_zero.mp hlate] at hmem
        simp at hmem
    simp [mountainFun, ht, hfalse]

private lemma late_card_one {n : ℕ} (hn : 2 ≤ n) {w : Fin (2 * n) → Bool}
    (hw : IsDyck n w) (h1 : (downSet n w).card = 1) : (lateUpSet n w).card = 1 := by
  have hsplit := card_split_bool (n := 2 * n) (k := n) (by omega) w
  have hdown :
      (Finset.univ.filter (fun t : Fin (2 * n) => t.val < n ∧ w t = false)).card = 1 := by
    simpa [downSet] using h1
  have hearly :
      (Finset.univ.filter (fun t : Fin (2 * n) => t.val < n ∧ w t = true)).card = n - 1 := by
    omega
  have hcut := card_cut (n := 2 * n) (c := n) (by omega) w true
  rw [hw.1, hearly] at hcut
  simp only [lateUpSet] at hcut ⊢
  omega

private lemma early_index_bounds {n : ℕ} (hn : 2 ≤ n) {w : Fin (2 * n) → Bool}
    (hw : IsDyck n w) (h1 : (downSet n w).card = 1) :
    1 ≤ (theOne (downSet n w) h1).val ∧ (theOne (downSet n w) h1).val ≤ n - 1 := by
  have hmem : theOne (downSet n w) h1 ∈ downSet n w := theOne_mem (downSet n w) h1
  have hprop : (theOne (downSet n w) h1).val < n ∧ w (theOne (downSet n w) h1) = false := by
    simpa [downSet] using hmem
  refine ⟨?_, by omega⟩
  by_contra h0
  have hiz : (theOne (downSet n w) h1).val = 0 := by omega
  have hsplit := card_split_bool (n := 2 * n) (k := 1) (by omega) w
  have hdown :
      (Finset.univ.filter (fun t : Fin (2 * n) => t.val < 1 ∧ w t = false)).card = 1 := by
    have hs :
        Finset.univ.filter (fun t : Fin (2 * n) => t.val < 1 ∧ w t = false) =
          {⟨0, by omega⟩} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and]
      constructor
      · intro h
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      · intro ht
        have hv0 : t.val = 0 := by simpa only [Fin.val_mk] using congrArg Fin.val ht
        have hi0 : theOne (downSet n w) h1 = t := by
          apply Fin.ext
          rw [hiz, hv0]
        refine ⟨by omega, ?_⟩
        simpa [hi0] using hprop.2
    rw [hs]
    simp
  have hbal := hw.2 1 (by omega)
  omega

private lemma late_not_last {n : ℕ} (hn : 2 ≤ n) {w : Fin (2 * n) → Bool}
    (hw : IsDyck n w) (h1 : (downSet n w).card = 1) :
    (theOne (lateUpSet n w) (late_card_one hn hw h1)).val ≠ 2 * n - 1 := by
  intro hlast
  set L : Fin (2 * n) := theOne (lateUpSet n w) (late_card_one hn hw h1)
  have hmem : L ∈ lateUpSet n w := theOne_mem _ _
  have htrue : w L = true := (Finset.mem_filter.mp hmem).2.2
  have hsplit := card_split_bool (n := 2 * n) (k := 2 * n - 1) (by omega) w
  have hsing :
      (Finset.univ.filter (fun t : Fin (2 * n) => 2 * n - 1 ≤ t.val ∧ w t = true)).card = 1 := by
    have hs :
        Finset.univ.filter (fun t : Fin (2 * n) => 2 * n - 1 ≤ t.val ∧ w t = true) =
          {⟨2 * n - 1, by omega⟩} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and]
      constructor
      · intro h
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      · intro ht
        have hvL : t.val = 2 * n - 1 := by
          simpa only [Fin.val_mk] using congrArg Fin.val ht
        have hL : L = t := by
          apply Fin.ext
          rw [hlast, hvL]
        refine ⟨by omega, ?_⟩
        simpa [hL] using htrue
    rw [hs]
    simp
  have hcut := card_cut (n := 2 * n) (c := 2 * n - 1) (by omega) w true
  rw [hw.1, hsing] at hcut
  have hsplit := card_split_bool (n := 2 * n) (k := 2 * n - 1) (by omega) w
  have hbal := hw.2 (2 * n - 1) (by omega)
  omega

private lemma late_j_bounds {n : ℕ} (hn : 2 ≤ n) {w : Fin (2 * n) → Bool}
    (hw : IsDyck n w) (h1 : (downSet n w).card = 1) :
    1 ≤ 2 * n - 1 - (theOne (lateUpSet n w) (late_card_one hn hw h1)).val ∧
      2 * n - 1 - (theOne (lateUpSet n w) (late_card_one hn hw h1)).val ≤ n - 1 := by
  have hmem : theOne (lateUpSet n w) (late_card_one hn hw h1) ∈ lateUpSet n w := theOne_mem _ _
  have hge : n ≤ (theOne (lateUpSet n w) (late_card_one hn hw h1)).val :=
    (Finset.mem_filter.mp hmem).2.1
  have hnot := late_not_last hn hw h1
  omega

private lemma w_eq_shape {n : ℕ} (hn : 2 ≤ n) {w : Fin (2 * n) → Bool}
    (hw : IsDyck n w) (h1 : (downSet n w).card = 1) :
    w = shapeFun n (theOne (downSet n w) h1).val
      (2 * n - 1 - (theOne (lateUpSet n w) (late_card_one hn hw h1)).val) := by
  set i0 : Fin (2 * n) := theOne (downSet n w) h1
  set L : Fin (2 * n) := theOne (lateUpSet n w) (late_card_one hn hw h1)
  have hi := early_index_bounds hn hw h1
  have hj := late_j_bounds hn hw h1
  have hi0_mem : i0 ∈ downSet n w := theOne_mem _ _
  have hi0_prop : i0.val < n ∧ w i0 = false := by
    simpa only [downSet, Finset.mem_filter, Finset.mem_univ, true_and] using hi0_mem
  have hi0_false : w i0 = false := hi0_prop.2
  have hL_mem : L ∈ lateUpSet n w := theOne_mem _ _
  have hL_prop : n ≤ L.val ∧ w L = true := by
    simpa only [lateUpSet, Finset.mem_filter, Finset.mem_univ, true_and] using hL_mem
  have hL_true : w L = true := hL_prop.2
  have hL_back : L.val = 2 * n - 1 - (2 * n - 1 - L.val) := by
    have hle : L.val ≤ 2 * n - 1 := by omega
    exact (Nat.sub_sub_self hle).symm
  have hjle : 2 * n - 1 - L.val ≤ n - 1 := hj.2
  funext t
  by_cases ht : t.val < n
  · have hsame : (w t = true) ↔ (shapeFun n i0.val (2 * n - 1 - L.val) t = true) := by
      constructor
      · intro ht'
        have hne : t ≠ i0 := by
          intro heq
          rw [heq, hi0_false] at ht'
          cases ht'
        exact (shape_eq_early hi.2 t ht).mpr (fun hv => hne (Fin.ext hv))
      · intro hs
        have hne : t.val ≠ i0.val := (shape_eq_early hi.2 t ht).mp hs
        cases hv : w t
        · have hmem : t ∈ downSet n w := by
            simp only [downSet, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨ht, hv⟩
          rw [theOne_spec (downSet n w) h1] at hmem
          exact absurd (congrArg Fin.val (Finset.mem_singleton.mp hmem)) hne
        · rfl
    cases hvw : w t <;> cases hvs : shapeFun n i0.val (2 * n - 1 - L.val) t
    · rfl
    · have hwt : w t = true := hsame.mpr hvs
      rw [hvw] at hwt
      cases hwt
    · have hs : shapeFun n i0.val (2 * n - 1 - L.val) t = true := hsame.mp hvw
      rw [hvs] at hs
      cases hs
    · rfl
  · have hsame : (w t = true) ↔ (shapeFun n i0.val (2 * n - 1 - L.val) t = true) := by
      constructor
      · intro ht'
        have hmem : t ∈ lateUpSet n w := by
          simp only [lateUpSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨by omega, ht'⟩
        rw [theOne_spec (lateUpSet n w) (late_card_one hn hw h1)] at hmem
        have htL : t = L := Finset.mem_singleton.mp hmem
        have hval : t.val = 2 * n - 1 - (2 * n - 1 - L.val) := by
          rw [htL]
          exact hL_back
        exact (shape_eq_late hi.2 hjle t (by omega)).mpr hval
      · intro hs
        have hval := (shape_eq_late hi.2 hjle t (by omega)).mp hs
        have htL : t = L := Fin.ext (hval.trans hL_back.symm)
        rw [htL]
        exact hL_true
    cases hvw : w t <;> cases hvs : shapeFun n i0.val (2 * n - 1 - L.val) t
    · rfl
    · have hwt : w t = true := hsame.mpr hvs
      rw [hvw] at hwt
      cases hwt
    · have hs : shapeFun n i0.val (2 * n - 1 - L.val) t = true := hsame.mp hvw
      rw [hvs] at hs
      cases hs
    · rfl

private lemma down_card_one {n : ℕ} (hn : 2 ≤ n) {w : Fin (2 * n) → Bool}
    (hw : IsDyck n w) (hc : ContainsPattern n w) (h0 : ¬ (downSet n w).card = 0) :
    (downSet n w).card = 1 := by
  have hle := early_down_le_one hn hw hc
  omega

private lemma early_val_shape {n i j : ℕ} (hn : 2 ≤ n) (hi : 1 ≤ i ∧ i ≤ n - 1)
    (hj : 1 ≤ j ∧ j ≤ n - 1) {h : (downSet n (shapeFun n i j)).card = 1} :
    (theOne (downSet n (shapeFun n i j)) h).val = i := by
  rw [theOne_eq_of_singleton _ h (shape_down_singleton hn hi hj)]

private lemma late_val_shape {n i j : ℕ} (hn : 2 ≤ n) (hi : 1 ≤ i ∧ i ≤ n - 1)
    (hj : 1 ≤ j ∧ j ≤ n - 1) {h : (lateUpSet n (shapeFun n i j)).card = 1} :
    (theOne (lateUpSet n (shapeFun n i j)) h).val = 2 * n - 1 - j := by
  rw [theOne_eq_of_singleton _ h (shape_late_singleton hn hi hj)]

private def badToIndex (n : ℕ) (hn : 2 ≤ n) (w : Fin (2 * n) → Bool)
    (hw : IsDyck n w) (hc : ContainsPattern n w) : (Fin (n - 1) × Fin (n - 1)) ⊕ Unit :=
  if h0 : (downSet n w).card = 0 then Sum.inr ()
  else
    Sum.inl
      (⟨(theOne (downSet n w) (down_card_one hn hw hc h0)).val - 1, by
          have hb := early_index_bounds hn hw (down_card_one hn hw hc h0)
          omega⟩,
        ⟨(2 * n - 1 - (theOne (lateUpSet n w)
            (late_card_one hn hw (down_card_one hn hw hc h0))).val) - 1, by
          have hb := late_j_bounds hn hw (down_card_one hn hw hc h0)
          omega⟩)

private def badEquiv (n : ℕ) (hn : 2 ≤ n) :
    {w : Fin (2 * n) → Bool // IsDyck n w ∧ ContainsPattern n w} ≃
      (Fin (n - 1) × Fin (n - 1)) ⊕ Unit where
  toFun w := badToIndex n hn w.1 w.2.1 w.2.2
  invFun
    | Sum.inr () => ⟨mountainFun n, mountain_isDyck (by omega), mountain_pattern hn⟩
    | Sum.inl (⟨a, _⟩, ⟨b, _⟩) =>
      ⟨shapeFun n (a + 1) (b + 1), shape_isDyck hn (by omega) (by omega),
        shape_pattern hn (by omega) (by omega)⟩
  left_inv w := by
    by_cases h0 : (downSet n w.1).card = 0
    · apply Subtype.ext
      simp only [badToIndex, h0, dite_true]
      exact (zero_early_mountain hn w.2.1 h0).symm
    · apply Subtype.ext
      simp only [badToIndex, h0, dite_false]
      have h1 := down_card_one hn w.2.1 w.2.2 h0
      have hi := early_index_bounds hn w.2.1 h1
      have hj := late_j_bounds hn w.2.1 h1
      rw [Nat.sub_add_cancel hi.1, Nat.sub_add_cancel hj.1]
      exact (w_eq_shape hn w.2.1 h1).symm
  right_inv s := by
    cases s with
    | inr u =>
      cases u
      have h0 := mountain_down_empty (n := n) (by omega)
      simp [badToIndex, h0]
    | inl p =>
      rcases p with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      have hi : 1 ≤ a + 1 ∧ a + 1 ≤ n - 1 := by omega
      have hj : 1 ≤ b + 1 ∧ b + 1 ≤ n - 1 := by omega
      have hne : ¬ (downSet n (shapeFun n (a + 1) (b + 1))).card = 0 := by
        rw [shape_down_singleton hn hi hj]
        simp
      simp only [badToIndex, hne, dite_false]
      apply congrArg Sum.inl
      apply Prod.ext
      · apply Fin.ext
        simp only [Fin.val_mk]
        rw [early_val_shape hn hi hj]
        omega
      · apply Fin.ext
        simp only [Fin.val_mk]
        rw [late_val_shape hn hi hj]
        omega

private lemma bad_card (n : ℕ) (hn : 2 ≤ n) :
    Nat.card {w : Fin (2 * n) → Bool // IsDyck n w ∧ ContainsPattern n w} =
      (n - 1) ^ 2 + 1 := by
  rw [Nat.card_congr (badEquiv n hn), Nat.card_sum, Nat.card_prod]
  simp [Nat.card_fin, Nat.card_unique]
  ring

private lemma card_split_pattern (n : ℕ) :
    Nat.card {w : Fin (2 * n) → Bool // IsDyck n w} =
      Nat.card {w : Fin (2 * n) → Bool // IsDyck n w ∧ ContainsPattern n w} +
        Nat.card {w : Fin (2 * n) → Bool // IsDyck n w ∧ ¬ ContainsPattern n w} := by
  let e : {w : Fin (2 * n) → Bool // IsDyck n w} ≃
      {w : Fin (2 * n) → Bool // IsDyck n w ∧ ContainsPattern n w} ⊕
        {w : Fin (2 * n) → Bool // IsDyck n w ∧ ¬ ContainsPattern n w} :=
    { toFun := fun w =>
        if h : ContainsPattern n w.1 then Sum.inl ⟨w.1, w.2, h⟩ else Sum.inr ⟨w.1, w.2, h⟩
      invFun := fun s =>
        match s with
        | Sum.inl w => ⟨w.1, w.2.1⟩
        | Sum.inr w => ⟨w.1, w.2.1⟩
      left_inv := fun w => by
        by_cases h : ContainsPattern n w.1 <;> simp [h]
      right_inv := fun s => by
        cases s with
        | inl w => simp [w.2.2]
        | inr w => simp [w.2.2] }
  rw [Nat.card_congr e, Nat.card_sum]

private lemma closed_nat (n : ℕ) (hn : 2 ≤ n) :
    a n + ((n - 1) ^ 2 + 1) = catalan n := by
  have hsplit := card_split_pattern n
  have hdyck := card_dyck n
  have hbad := bad_card n hn
  unfold a
  omega

private lemma cast_closed (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℤ) = (catalan n : ℤ) - (((n - 1) ^ 2 + 1 : ℕ) : ℤ) := by
  have h := closed_nat n hn
  have hle : (n - 1) ^ 2 + 1 ≤ catalan n := by omega
  have ha : a n = catalan n - ((n - 1) ^ 2 + 1) := by omega
  rw [ha, Int.ofNat_sub hle]

private theorem catalan_step (k : ℕ) :
    (k + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < k + 1)
  calc
    (k + 1) * ((k + 2) * catalan (k + 1)) = (k + 1) * (k + 1).centralBinom := by
      rw [← succ_mul_catalan_eq_centralBinom (k + 1)]
    _ = 2 * (2 * k + 1) * k.centralBinom := Nat.succ_mul_centralBinom_succ k
    _ = (k + 1) * (2 * (2 * k + 1) * catalan k) := by
      rw [← succ_mul_catalan_eq_centralBinom k]
      ring

private theorem catalan_step_int (k : ℕ) :
    ((k : ℤ) + 2) * (catalan (k + 1) : ℤ) = 2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ) := by
  exact_mod_cast catalan_step k

private lemma mathar_catalan (m : ℕ) :
    -10 * ((m + 5 : ℤ) + 1) * ((m + 5 : ℤ) - 4) * (catalan (m + 5) : ℤ) +
        (51 * (m + 5 : ℤ) ^ 2 - 196 * (m + 5 : ℤ) + 80) * (catalan (m + 4) : ℤ) +
        (-45 * (m + 5 : ℤ) ^ 2 + 134 * (m + 5 : ℤ) - 99) * (catalan (m + 3) : ℤ) +
        2 * (2 * (m + 5 : ℤ) - 5) * ((m + 5 : ℤ) - 3) * (catalan (m + 2) : ℤ) = 0 := by
  have hc1 := catalan_step_int (m + 4)
  have hc2 := catalan_step_int (m + 3)
  have hc3 := catalan_step_int (m + 2)
  push_cast at hc1 hc2 hc3 ⊢
  linear_combination (-10 * ((m : ℤ) + 1)) * hc1 + (11 * (m : ℤ) + 39) * hc2 +
    (-((m : ℤ) + 2)) * hc3

private lemma mathar_poly (m : ℕ) :
    -10 * ((m + 5 : ℤ) + 1) * ((m + 5 : ℤ) - 4) * ((m + 4 : ℤ) ^ 2 + 1) +
        (51 * (m + 5 : ℤ) ^ 2 - 196 * (m + 5 : ℤ) + 80) * ((m + 3 : ℤ) ^ 2 + 1) +
        (-45 * (m + 5 : ℤ) ^ 2 + 134 * (m + 5 : ℤ) - 99) * ((m + 2 : ℤ) ^ 2 + 1) +
        2 * (2 * (m + 5 : ℤ) - 5) * ((m + 5 : ℤ) - 3) * ((m + 1 : ℤ) ^ 2 + 1) = 0 := by
  ring

private lemma mathar (n : ℕ) (hn : 5 ≤ n) :
    -10 * ((n : ℤ) + 1) * ((n : ℤ) - 4) * (a n : ℤ) +
        (51 * (n : ℤ) ^ 2 - 196 * (n : ℤ) + 80) * (a (n - 1) : ℤ) +
        (-45 * (n : ℤ) ^ 2 + 134 * (n : ℤ) - 99) * (a (n - 2) : ℤ) +
        2 * (2 * (n : ℤ) - 5) * ((n : ℤ) - 3) * (a (n - 3) : ℤ) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega]
  rw [cast_closed (m + 5) (by omega), cast_closed (m + 4) (by omega),
    cast_closed (m + 3) (by omega), cast_closed (m + 2) (by omega)]
  rw [show m + 5 - 1 = m + 4 by omega, show m + 4 - 1 = m + 3 by omega,
    show m + 3 - 1 = m + 2 by omega, show m + 2 - 1 = m + 1 by omega]
  push_cast
  linear_combination mathar_catalan m - mathar_poly m

private lemma stirling_factorial (m : ℕ) (hm : m ≠ 0) :
    (Nat.factorial m : ℝ) =
      Stirling.stirlingSeq m * Real.sqrt (2 * (m : ℝ)) * ((m : ℝ) / Real.exp 1) ^ m := by
  have hden : Real.sqrt (2 * (m : ℝ)) * ((m : ℝ) / Real.exp 1) ^ m ≠ 0 := by positivity
  unfold Stirling.stirlingSeq
  rw [mul_assoc]
  exact (div_mul_cancel₀ (Nat.factorial m : ℝ) hden).symm

private lemma central_real (n : ℕ) :
    (Nat.centralBinom n : ℝ) =
      (Nat.factorial (2 * n) : ℝ) / ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ)) := by
  rw [Nat.centralBinom_eq_two_mul_choose, show 2 * n = n + n by ring]
  exact Nat.cast_add_choose ℝ

private lemma catalan_real (n : ℕ) :
    (catalan n : ℝ) = (Nat.centralBinom n : ℝ) / ((n : ℝ) + 1) := by
  have h := succ_mul_catalan_eq_centralBinom n
  rw [eq_div_iff (by positivity : ((n : ℝ) + 1) ≠ 0), mul_comm]
  exact_mod_cast h

private lemma sqrt_four_mul (n : ℕ) :
    Real.sqrt (4 * (n : ℝ)) = 2 * Real.sqrt (n : ℝ) := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt (4 : ℝ) = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

private lemma pow_ratio_four (n : ℕ) (hn : 1 ≤ n) :
    ((2 * (n : ℝ)) / Real.exp 1) ^ (2 * n) / ((n : ℝ) / Real.exp 1) ^ (2 * n) = (4 : ℝ) ^ n := by
  rw [← div_pow]
  have hratio : ((2 * (n : ℝ)) / Real.exp 1) / ((n : ℝ) / Real.exp 1) = 2 := by
    field_simp
  rw [hratio, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]

private lemma central_stirling (n : ℕ) (hn : 1 ≤ n) :
    (Nat.centralBinom n : ℝ) =
      Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2 * (4 : ℝ) ^ n /
        Real.sqrt (n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by simp [Nat.cast_mul]
  have hsqrt : Real.sqrt (2 * (2 * (n : ℝ))) = 2 * Real.sqrt (n : ℝ) := by
    rw [show 2 * (2 * (n : ℝ)) = 4 * (n : ℝ) by ring]
    exact sqrt_four_mul n
  have hsq : (Real.sqrt (2 * (n : ℝ))) ^ 2 = 2 * (n : ℝ) := Real.sq_sqrt (by positivity)
  have hsqn : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hsqpow : (((n : ℝ) / Real.exp 1) ^ n) ^ 2 = ((n : ℝ) / Real.exp 1) ^ (2 * n) := by
    rw [← pow_mul]
    congr 1
    omega
  have hpow' : ((2 * (n : ℝ)) / Real.exp 1) ^ (2 * n) =
      (4 : ℝ) ^ n * ((n : ℝ) / Real.exp 1) ^ (2 * n) := by
    have hnz : ((n : ℝ) / Real.exp 1) ^ (2 * n) ≠ 0 := by positivity
    exact (div_eq_iff hnz).mp (pow_ratio_four n hn)
  have hSn : Stirling.stirlingSeq n ≠ 0 := by
    have hle := Stirling.sqrt_pi_le_stirlingSeq hn0
    exact (lt_of_lt_of_le (Real.sqrt_pos.2 Real.pi_pos) hle).ne'
  have hdenL :
      (Stirling.stirlingSeq n * Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) *
        (Stirling.stirlingSeq n * Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) ≠ 0 := by
    apply mul_ne_zero <;> exact mul_ne_zero (mul_ne_zero hSn (by positivity)) (by positivity)
  have hdenR : Stirling.stirlingSeq n ^ 2 * Real.sqrt (n : ℝ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hSn) (by positivity)
  have htarget :
      Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2 * (4 : ℝ) ^ n /
          Real.sqrt (n : ℝ) =
        (Stirling.stirlingSeq (2 * n) * (4 : ℝ) ^ n) /
          (Stirling.stirlingSeq n ^ 2 * Real.sqrt (n : ℝ)) := by
    rw [div_mul_eq_mul_div, div_div]
  rw [htarget, central_real, stirling_factorial (2 * n) (by omega), stirling_factorial n hn0,
    hcast, hsqrt]
  apply (div_eq_div_iff hdenL hdenR).2
  set p : ℝ := ((n : ℝ) / Real.exp 1) ^ n
  set q : ℝ := ((2 * (n : ℝ)) / Real.exp 1) ^ (2 * n)
  set r : ℝ := Real.sqrt (n : ℝ)
  set s : ℝ := Real.sqrt (2 * (n : ℝ))
  set S : ℝ := Stirling.stirlingSeq n
  set S2 : ℝ := Stirling.stirlingSeq (2 * n)
  set f : ℝ := (4 : ℝ) ^ n
  have hss : s * s = 2 * (n : ℝ) := by rw [← sq, hsq]
  have hrr : (2 * r) * r = 2 * (n : ℝ) := by
    rw [show (2 * r) * r = 2 * (r * r) by ring, ← sq, hsqn]
  have hq : q = f * (p * p) := by rw [hpow', ← hsqpow, sq]
  rw [hq, sq, show S2 * (2 * r) * (f * (p * p)) * ((S * S) * r) =
    S2 * f * (S * S) * (p * p) * ((2 * r) * r) by ring, hrr, hss.symm]
  ring

private lemma catalan_ratio_eq (n : ℕ) (hn : 1 ≤ n) :
    (catalan n : ℝ) * Real.sqrt Real.pi * (n : ℝ) ^ ((3 : ℝ) / 2) / (4 : ℝ) ^ n =
      (Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2 * Real.sqrt Real.pi) *
        ((n : ℝ) / ((n : ℝ) + 1)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hrpow : (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) * Real.sqrt (n : ℝ) := by
    rw [show (3 : ℝ) / 2 = 1 + (1 : ℝ) / 2 by norm_num, Real.rpow_add hnpos, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [catalan_real, central_stirling n hn, hrpow]
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hsqrt, h4, hn1]

private lemma tendsto_stirling_factor :
    Tendsto (fun n : ℕ =>
      Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2 * Real.sqrt Real.pi)
      atTop (nhds 1) := by
  have h2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun n hn => by omega⟩
  have hS2 := Stirling.tendsto_stirlingSeq_sqrt_pi.comp h2
  have hSsq := Stirling.tendsto_stirlingSeq_sqrt_pi.pow 2
  have hdiv : Tendsto (fun n : ℕ => Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2) atTop
      (nhds (Real.sqrt Real.pi / (Real.sqrt Real.pi) ^ 2)) :=
    hS2.div hSsq (by
      rw [Real.sq_sqrt Real.pi_nonneg]
      exact Real.pi_pos.ne')
  have hsimp : Real.sqrt Real.pi / (Real.sqrt Real.pi) ^ 2 = 1 / Real.sqrt Real.pi := by
    field_simp [Real.sq_sqrt Real.pi_nonneg, (Real.sqrt_pos.2 Real.pi_pos).ne']
  rw [hsimp] at hdiv
  have hmul := hdiv.mul (tendsto_const_nhds (x := Real.sqrt Real.pi))
  have hone : (1 / Real.sqrt Real.pi) * Real.sqrt Real.pi = 1 := by
    field_simp
  rw [hone] at hmul
  exact hmul

private lemma tendsto_nat_frac :
    Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (nhds 1) := by
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) := by
    have hcomp := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1)
    refine hcomp.congr fun n => ?_
    simp
  have heq : (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) =
      fun n : ℕ => 1 - (1 : ℝ) / ((n : ℝ) + 1) := by
    funext n
    by_cases hn : n = 0
    · subst hn
      norm_num
    · field_simp
      ring
  rw [heq]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0

private lemma tendsto_catalan_ratio :
    Tendsto (fun n : ℕ =>
      (catalan n : ℝ) * Real.sqrt Real.pi * (n : ℝ) ^ ((3 : ℝ) / 2) / (4 : ℝ) ^ n)
      atTop (nhds 1) := by
  have hprod := tendsto_stirling_factor.mul tendsto_nat_frac
  simp only [one_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (catalan_ratio_eq n hn).symm

private lemma four_pow_exp (n : ℕ) : (4 : ℝ) ^ n = Real.exp (Real.log 4 * (n : ℝ)) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4) _

private lemma tendsto_poly_over_four :
    Tendsto (fun n : ℕ => Real.sqrt Real.pi * (n : ℝ) ^ ((7 : ℝ) / 2) / (4 : ℝ) ^ n)
      atTop (nhds 0) := by
  have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((7 : ℝ) / 2) (Real.log 4)
    (Real.log_pos (by norm_num : (1 : ℝ) < 4))
  have hcomp := hbase.comp tendsto_natCast_atTop_atTop
  have hmul := (tendsto_const_nhds (x := Real.sqrt Real.pi)).mul hcomp
  simp only [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp_apply]
  have hneg : Real.exp (-Real.log 4 * (n : ℝ)) = (Real.exp (Real.log 4 * (n : ℝ)))⁻¹ := by
    rw [neg_mul]
    exact Real.exp_neg _
  rw [four_pow_exp,
    div_eq_mul_inv (Real.sqrt Real.pi * (n : ℝ) ^ ((7 : ℝ) / 2))
      (Real.exp (Real.log 4 * (n : ℝ))),
    hneg]
  ring

private lemma sq_bound (n : ℕ) (hn : 1 ≤ n) : (n - 1) ^ 2 + 1 ≤ n ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp [Nat.add_sub_cancel_left]
  nlinarith

private lemma real_closed (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℝ) = (catalan n : ℝ) - (((n - 1) ^ 2 + 1 : ℕ) : ℝ) := by
  exact_mod_cast cast_closed n hn

private lemma ratio_form (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℝ) / ((4 : ℝ) ^ n / (Real.sqrt Real.pi * (n : ℝ) ^ ((3 : ℝ) / 2))) =
      (a n : ℝ) * Real.sqrt Real.pi * (n : ℝ) ^ ((3 : ℝ) / 2) / (4 : ℝ) ^ n := by
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hs : Real.sqrt Real.pi * (n : ℝ) ^ ((3 : ℝ) / 2) ≠ 0 := by positivity
  field_simp

private lemma tendsto_error :
    Tendsto (fun n : ℕ =>
      (((n - 1) ^ 2 + 1 : ℕ) : ℝ) * Real.sqrt Real.pi * (n : ℝ) ^ ((3 : ℝ) / 2) / (4 : ℝ) ^ n)
      atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) tendsto_poly_over_four ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hle : (((n - 1) ^ 2 + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast sq_bound n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hr : (n : ℝ) ^ 2 * (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) ^ ((7 : ℝ) / 2) := by
      rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_add hnpos]
      norm_num
    calc
      (((n - 1) ^ 2 + 1 : ℕ) : ℝ) * Real.sqrt Real.pi * (n : ℝ) ^ ((3 : ℝ) / 2) / (4 : ℝ) ^ n
          ≤ ((n : ℝ) ^ 2) * Real.sqrt Real.pi * (n : ℝ) ^ ((3 : ℝ) / 2) / (4 : ℝ) ^ n := by
            gcongr
      _ = Real.sqrt Real.pi * (n : ℝ) ^ ((7 : ℝ) / 2) / (4 : ℝ) ^ n := by
            rw [show ((n : ℝ) ^ 2) * Real.sqrt Real.pi * (n : ℝ) ^ ((3 : ℝ) / 2) =
              Real.sqrt Real.pi * ((n : ℝ) ^ 2 * (n : ℝ) ^ ((3 : ℝ) / 2)) by ring, hr]

private lemma kotesovec :
    Tendsto (fun n : ℕ =>
      (a n : ℝ) / ((4 : ℝ) ^ n / (Real.sqrt Real.pi * (n : ℝ) ^ ((3 : ℝ) / 2))))
      atTop (nhds 1) := by
  have hdiff := tendsto_catalan_ratio.sub tendsto_error
  simp only [sub_zero] at hdiff
  refine hdiff.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [ratio_form n (by omega), real_closed n hn]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a225692.main := by
  refine ⟨?_, kotesovec⟩
  intro n hn
  exact mathar n hn

end
