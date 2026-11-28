import OMAReductions.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R3_H1_R1

/-!
# Hyperbolicity of the Free Product of Two Copies of a Hyperbolic Group

We prove `OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R3_H1_R1.H2`:
if `A` is a hyperbolic group, then `Monoid.CoprodI (fun _ : Fin 2 => A)` is hyperbolic.

## Proof outline
1. Given a finite generating family `P : Group.Generators A (Fin n)` with `P.IsHyperbolicWith δ`,
   form the disjoint-union generating family `doubleGen P : Group.Generators (A * A) (Fin (n + n))`.
2. Show that for every reduced word `w : CoprodI.Word (fun _ : Fin 2 => A)`, the word length
   `(doubleGen P).wordLength w.prod` equals the sum of `P.wordLength` over the letters of `w`.
3. Derive a recursive formula `gromovWord` for the Gromov product `Metric.gromovProduct 1 x.prod y.prod`
   along the common prefix of reduced words `x` and `y`.
4. Prove the four-point Gromov hyperbolicity inequality for `gromovWord` with the same constant `δ`
   by structural list induction, and extend from basepoint `1` to arbitrary `w` by left-invariance.
-/

namespace OMA.HyperbolicDouble

open Monoid Monoid.CoprodI

section Construction

variable {A : Type} [Group A] {n : ℕ} (P : Group.Generators A (Fin n))

private abbrev Fam (A : Type) : Fin 2 → Type := fun _ => A
private abbrev Double (A : Type) [Group A] : Type := CoprodI (Fam A)

private def doubleVal : Fin (n + n) → Double A :=
  Fin.addCases (fun k => CoprodI.of (i := (0 : Fin 2)) (P.val k))
    (fun k => CoprodI.of (i := (1 : Fin 2)) (P.val k))

private def doubleGen : Group.Generators (Double A) (Fin (n + n)) where
  val := doubleVal P
  closure_eq_top := by
    rw [eq_top_iff]
    intro g _
    clear ‹g ∈ ⊤›
    induction g using CoprodI.induction_on with
    | one => exact Subgroup.one_mem _
    | of i a =>
      have ha : a ∈ Subgroup.closure (Set.range P.val) := by
        rw [P.closure_eq_top]; trivial
      have hmap : CoprodI.of (M := Fam A) (i := i) a ∈
          Subgroup.map (CoprodI.of (M := Fam A) (i := i)) (Subgroup.closure (Set.range P.val)) :=
        ⟨a, ha, rfl⟩
      rw [MonoidHom.map_closure] at hmap
      have hsub : (CoprodI.of (M := Fam A) (i := i)) '' Set.range P.val ⊆ Set.range (doubleVal P) := by
        rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
        fin_cases i
        · exact ⟨Fin.castAdd n k, by simp only [doubleVal, Fin.addCases_left]⟩
        · exact ⟨Fin.natAdd n k, by simp only [doubleVal, Fin.addCases_right]⟩
      exact Subgroup.closure_mono hsub hmap
    | mul x y hx hy => exact Subgroup.mul_mem _ hx hy

private noncomputable def wordWeight (w : CoprodI.Word (Fam A)) : ℕ :=
  (w.toList.map fun x => P.wordLength x.2).sum

@[simp]
private lemma wordWeight_empty : wordWeight P (Word.empty : Word (Fam A)) = 0 := by
  simp [wordWeight]

@[simp]
private lemma wordWeight_cons {i : Fin 2} (a : A) (w : Word (Fam A))
    (h1 : w.fstIdx ≠ some i) (h2 : a ≠ 1) :
    wordWeight P (Word.cons (i := i) a w h1 h2) = P.wordLength a + wordWeight P w := by
  simp [wordWeight, Word.cons]

private lemma wordWeight_rcons [DecidableEq A] {i : Fin 2} (p : Word.Pair (Fam A) i) :
    wordWeight P (Word.rcons p) = P.wordLength p.head + wordWeight P p.tail := by
  unfold Word.rcons
  split_ifs with h
  · rw [h, Group.Generators.wordLength_one, zero_add]
  · exact wordWeight_cons P p.head p.tail p.fstIdx_ne h

private lemma wordWeight_of_smul_le [DecidableEq A] (i : Fin 2) (s : A) (w : Word (Fam A)) :
    wordWeight P (CoprodI.of (M := Fam A) (i := i) s • w) ≤ P.wordLength s + wordWeight P w := by
  rw [Word.of_smul_def, wordWeight_rcons]
  have h1 : P.wordLength (s * (Word.equivPair i w).head) ≤
      P.wordLength s + P.wordLength (Word.equivPair i w).head :=
    P.wordLength_mul_le s _
  have hw : wordWeight P w =
      P.wordLength (Word.equivPair i w).head + wordWeight P (Word.equivPair i w).tail := by
    conv_lhs => rw [← (Word.equivPair i).symm_apply_apply w]
    exact wordWeight_rcons P (Word.equivPair i w)
  dsimp only
  omega

private def liftLetter (i : Fin 2) (x : Fin n × Bool) : Fin (n + n) × Bool :=
  (if i = 0 then Fin.castAdd n x.1 else Fin.natAdd n x.1, x.2)

private lemma wordProd_map_liftLetter (i : Fin 2) (l : List (Fin n × Bool)) :
    (doubleGen P).wordProd (l.map (liftLetter i)) = CoprodI.of (M := Fam A) (i := i) (P.wordProd l) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rcases x with ⟨k, b⟩
    rw [List.map_cons, Group.Generators.wordProd_cons, Group.Generators.wordProd_cons, ih,
      map_mul]
    congr 1
    by_cases hi : i = 0
    · subst hi
      cases b <;> simp only [liftLetter, doubleGen, doubleVal, ↓reduceIte, Fin.addCases_left,
        Bool.cond_false, Bool.cond_true, map_inv]
    · have hi1 : i = 1 := by fin_cases i <;> tauto
      subst hi1
      cases b <;> simp only [liftLetter, doubleGen, doubleVal, hi, ↓reduceIte, Fin.addCases_right,
        Bool.cond_false, Bool.cond_true, map_inv]

private lemma wordLength_doubleGen_of_le (i : Fin 2) (a : A) :
    (doubleGen P).wordLength (CoprodI.of (i := i) a) ≤ P.wordLength a := by
  obtain ⟨l, hl, rfl⟩ := P.exists_isGeodesic a
  rw [hl.eq, ← wordProd_map_liftLetter P i l]
  have h := (doubleGen P).wordLength_wordProd_le (l.map (liftLetter i))
  simpa using h

private lemma wordLength_doubleGen_le_wordWeight (w : Word (Fam A)) :
    (doubleGen P).wordLength w.prod ≤ wordWeight P w := by
  induction w using Word.consRecOn with
  | empty => simp
  | cons i a w h1 h2 ih =>
    rw [Word.prod_cons, wordWeight_cons]
    calc (doubleGen P).wordLength (CoprodI.of (i := i) a * w.prod)
        ≤ (doubleGen P).wordLength (CoprodI.of (i := i) a) + (doubleGen P).wordLength w.prod :=
          (doubleGen P).wordLength_mul_le _ _
      _ ≤ P.wordLength a + wordWeight P w :=
          Nat.add_le_add (wordLength_doubleGen_of_le P i a) ih

private lemma wordWeight_equiv_wordProd_le [DecidableEq A] (l : List (Fin (n + n) × Bool)) :
    wordWeight P (Word.equiv ((doubleGen P).wordProd l)) ≤ l.length := by
  induction l with
  | nil =>
    have h1 : Word.equiv (1 : Double A) = Word.empty := by
      simp [Word.equiv]
    simp [h1]
  | cons x l ih =>
    rcases x with ⟨k, b⟩
    rw [Group.Generators.wordProd_cons, List.length_cons]
    have heq : Word.equiv (cond b ((doubleGen P).val k) ((doubleGen P).val k)⁻¹ *
        (doubleGen P).wordProd l) =
        cond b ((doubleGen P).val k) ((doubleGen P).val k)⁻¹ •
          Word.equiv ((doubleGen P).wordProd l) := by
      simp [Word.equiv, mul_smul]
    rw [heq]
    have hstep : ∃ (i : Fin 2) (s : A),
        cond b ((doubleGen P).val k) ((doubleGen P).val k)⁻¹ = CoprodI.of (M := Fam A) (i := i) s ∧
        P.wordLength s ≤ 1 := by
      by_cases hk : k.val < n
      · refine ⟨0, cond b (P.val ⟨k.val, hk⟩) (P.val ⟨k.val, hk⟩)⁻¹, ?_, ?_⟩
        · have hk' : k = Fin.castAdd n ⟨k.val, hk⟩ := by ext; rfl
          conv_lhs => rw [hk']
          cases b <;> simp only [doubleGen, doubleVal, Fin.addCases_left, Bool.cond_false,
            Bool.cond_true, map_inv]
        · cases b
          · simpa using P.wordLength_wordProd_le [(⟨k.val, hk⟩, false)]
          · simpa using P.wordLength_wordProd_le [(⟨k.val, hk⟩, true)]
      · have hk2 : k.val - n < n := by omega
        refine ⟨1, cond b (P.val ⟨k.val - n, hk2⟩) (P.val ⟨k.val - n, hk2⟩)⁻¹, ?_, ?_⟩
        · have hk' : k = Fin.natAdd n ⟨k.val - n, hk2⟩ := by ext; dsimp; omega
          conv_lhs => rw [hk']
          cases b <;> simp only [doubleGen, doubleVal, Fin.addCases_right, Bool.cond_false,
            Bool.cond_true, map_inv]
        · cases b
          · simpa using P.wordLength_wordProd_le [(⟨k.val - n, hk2⟩, false)]
          · simpa using P.wordLength_wordProd_le [(⟨k.val - n, hk2⟩, true)]
    obtain ⟨i, s, hs_eq, hs_len⟩ := hstep
    rw [hs_eq]
    have hle := wordWeight_of_smul_le P i s (Word.equiv ((doubleGen P).wordProd l))
    omega

private lemma wordLength_doubleGen_eq [DecidableEq A] (w : Word (Fam A)) :
    (doubleGen P).wordLength w.prod = wordWeight P w := by
  apply le_antisymm (wordLength_doubleGen_le_wordWeight P w)
  obtain ⟨l, hl, hprod⟩ := (doubleGen P).exists_isGeodesic w.prod
  rw [← hprod, hl.eq]
  have h1 := wordWeight_equiv_wordProd_le P l
  rw [hprod] at h1
  have heq : Word.equiv w.prod = w := Word.equiv.apply_symm_apply w
  rwa [heq] at h1

/- ### Reduced word inversion and non-canceling concatenation -/

private lemma isChain_reverse_of_symm {α : Type*} {r : α → α → Prop}
    (hsym : ∀ a b, r a b → r b a) :
    ∀ l : List α, l.IsChain r → l.reverse.IsChain r := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    rw [List.reverse_cons]
    cases l with
    | nil => simp
    | cons b l' =>
      rw [List.isChain_cons_cons] at h
      have hrev := ih h.2
      rw [List.reverse_cons] at hrev ⊢
      rw [List.append_assoc, List.singleton_append]
      rw [List.isChain_append] at hrev ⊢
      refine ⟨hrev.1, List.isChain_cons_cons.mpr ⟨hsym a b h.1, List.isChain_singleton _⟩, ?_⟩
      intro x hx y hy
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact hrev.2.2 x hx b (by simp)

private def invWord (w : Word (Fam A)) : Word (Fam A) where
  toList := (w.toList.map fun x => ⟨x.1, x.2⁻¹⟩).reverse
  ne_one := by
    intro l hl
    rw [List.mem_reverse, List.mem_map] at hl
    obtain ⟨x, hx, rfl⟩ := hl
    exact inv_ne_one.mpr (w.ne_one x hx)
  chain_ne := by
    have hmap : (w.toList.map fun x : Σ _ : Fin 2, A => (⟨x.1, x.2⁻¹⟩ : Σ _ : Fin 2, A)).IsChain
        (fun a b => a.1 ≠ b.1) := by
      rw [List.isChain_map]
      exact w.chain_ne
    exact isChain_reverse_of_symm (fun _ _ h => h.symm) _ hmap

private lemma invWord_prod (w : Word (Fam A)) : (invWord w).prod = w.prod⁻¹ := by
  unfold invWord Word.prod
  dsimp only
  rw [List.map_reverse, List.map_map]
  have hmap : (w.toList.map ((fun l : Σ _ : Fin 2, A => CoprodI.of (i := l.1) l.2) ∘
      fun x : Σ _ : Fin 2, A => (⟨x.1, x.2⁻¹⟩ : Σ _ : Fin 2, A))) =
      (w.toList.map fun l => CoprodI.of (i := l.1) l.2).map Inv.inv := by
    rw [List.map_map]
    refine List.map_congr_left fun x _ => ?_
    simp [Function.comp]
  rw [hmap, ← List.prod_inv_reverse]

private lemma wordWeight_invWord (w : Word (Fam A)) :
    wordWeight P (invWord w) = wordWeight P w := by
  unfold wordWeight invWord
  dsimp only
  rw [List.map_reverse, List.sum_reverse, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp [Function.comp]

private lemma invWord_getLast?_fst (w : Word (Fam A)) :
    (invWord w).toList.getLast?.map Sigma.fst = w.fstIdx := by
  unfold invWord Word.fstIdx
  dsimp only
  rw [List.getLast?_reverse, List.head?_map, Option.map_map]
  rfl

private def appendWord (u v : Word (Fam A))
    (h : ∀ a ∈ u.toList.getLast?, ∀ b ∈ v.toList.head?, a.1 ≠ b.1) : Word (Fam A) where
  toList := u.toList ++ v.toList
  ne_one := by
    intro l hl
    rcases List.mem_append.mp hl with hu | hv
    · exact u.ne_one l hu
    · exact v.ne_one l hv
  chain_ne := List.isChain_append.mpr ⟨u.chain_ne, v.chain_ne, h⟩

private lemma appendWord_prod (u v : Word (Fam A))
    (h : ∀ a ∈ u.toList.getLast?, ∀ b ∈ v.toList.head?, a.1 ≠ b.1) :
    (appendWord u v h).prod = u.prod * v.prod := by
  simp [appendWord, Word.prod]

private lemma wordWeight_appendWord (u v : Word (Fam A))
    (h : ∀ a ∈ u.toList.getLast?, ∀ b ∈ v.toList.head?, a.1 ≠ b.1) :
    wordWeight P (appendWord u v h) = wordWeight P u + wordWeight P v := by
  simp [wordWeight, appendWord]

private lemma wordLength_inv_mul_of_ne_idx [DecidableEq A]
    {i j : Fin 2} (hij : i ≠ j) (a b : A) (xs ys : Word (Fam A))
    (hxs : xs.fstIdx ≠ some i) (ha : a ≠ 1)
    (hys : ys.fstIdx ≠ some j) (hb : b ≠ 1) :
    (doubleGen P).wordLength ((Word.cons (i := i) a xs hxs ha).prod⁻¹ *
        (Word.cons (i := j) b ys hys hb).prod) =
      wordWeight P (Word.cons (i := i) a xs hxs ha) +
        wordWeight P (Word.cons (i := j) b ys hys hb) := by
  set x := Word.cons (i := i) a xs hxs ha
  set y := Word.cons (i := j) b ys hys hb
  have hjoin : ∀ p ∈ (invWord x).toList.getLast?, ∀ q ∈ y.toList.head?, p.1 ≠ q.1 := by
    intro p hp q hq
    have hp1 : p.1 = i := by
      have h1 := invWord_getLast?_fst x
      rw [Word.fstIdx_cons] at h1
      have : (invWord x).toList.getLast? = some p := hp
      rw [this] at h1
      simpa using h1
    have hq1 : q.1 = j := by
      have : y.toList.head? = some ⟨j, b⟩ := rfl
      rw [this] at hq
      have hqp : q = ⟨j, b⟩ := Option.some.inj hq.symm
      rw [hqp]
    rw [hp1, hq1]
    exact hij
  have hprod : (appendWord (invWord x) y hjoin).prod = x.prod⁻¹ * y.prod := by
    rw [appendWord_prod, invWord_prod]
  rw [← hprod, wordLength_doubleGen_eq, wordWeight_appendWord, wordWeight_invWord]

private lemma wordLength_inv_mul_of_same_idx_ne [DecidableEq A]
    {i : Fin 2} {a b : A} (hab : a ≠ b) (xs ys : Word (Fam A))
    (hxs : xs.fstIdx ≠ some i) (ha : a ≠ 1)
    (hys : ys.fstIdx ≠ some i) (hb : b ≠ 1) :
    (doubleGen P).wordLength ((Word.cons (i := i) a xs hxs ha).prod⁻¹ *
        (Word.cons (i := i) b ys hys hb).prod) =
      wordWeight P xs + P.wordLength (a⁻¹ * b) + wordWeight P ys := by
  have hne : a⁻¹ * b ≠ 1 := by
    intro h
    exact hab (inv_mul_eq_one.mp h)
  let v := Word.cons (i := i) (a⁻¹ * b) ys hys hne
  have hjoin : ∀ p ∈ (invWord xs).toList.getLast?, ∀ q ∈ v.toList.head?, p.1 ≠ q.1 := by
    intro p hp q hq
    have hp1 : p.1 ≠ i := by
      have h1 := invWord_getLast?_fst xs
      have : (invWord xs).toList.getLast? = some p := hp
      rw [this] at h1
      intro hpi
      apply hxs
      rw [← h1, Option.map_some, hpi]
    have hq1 : q.1 = i := by
      have : v.toList.head? = some ⟨i, a⁻¹ * b⟩ := rfl
      rw [this] at hq
      have hqp : q = ⟨i, a⁻¹ * b⟩ := Option.some.inj hq.symm
      rw [hqp]
    rw [hq1]
    exact hp1
  have hprod : (appendWord (invWord xs) v hjoin).prod =
      (Word.cons (i := i) a xs hxs ha).prod⁻¹ * (Word.cons (i := i) b ys hys hb).prod := by
    rw [appendWord_prod, invWord_prod, Word.prod_cons, Word.prod_cons, Word.prod_cons,
      mul_inv_rev, map_mul, map_inv]
    group
  rw [← hprod, wordLength_doubleGen_eq, wordWeight_appendWord, wordWeight_invWord,
    wordWeight_cons, add_assoc]

/- ### Gromov product formula and four-point inequality on reduced words -/

private noncomputable def gromovWord [DecidableEq A] :
    List (Σ _ : Fin 2, A) → List (Σ _ : Fin 2, A) → ℝ
  | [], _ => 0
  | _, [] => 0
  | ⟨i, a⟩ :: xs, ⟨j, b⟩ :: ys =>
      if i ≠ j then 0
      else if a = b then (P.wordLength a : ℝ) + gromovWord xs ys
      else
        letI := P.normedGroup
        Metric.gromovProduct (1 : A) a b

private lemma gromovWord_nonneg [DecidableEq A] :
    ∀ xs ys : List (Σ _ : Fin 2, A), 0 ≤ gromovWord P xs ys
  | [], _ => le_rfl
  | _ :: _, [] => le_rfl
  | ⟨i, a⟩ :: xs, ⟨j, b⟩ :: ys => by
    unfold gromovWord
    split_ifs
    · exact le_rfl
    · have ih := gromovWord_nonneg xs ys
      have ha : (0 : ℝ) ≤ (P.wordLength a : ℝ) := Nat.cast_nonneg _
      linarith
    · let := P.normedGroup
      exact Metric.gromovProduct_nonneg (1 : A) a b

private lemma dist_eq_wordLength_inv_mul {G ι : Type*} [Group G] (Q : Group.Generators G ι)
    (x y : G) :
    letI := Q.normedGroup
    dist x y = (Q.wordLength (x⁻¹ * y) : ℝ) := by
  rfl

private lemma gromovProduct_one_eq_gromovWord [DecidableEq A] :
    ∀ x y : Word (Fam A),
      letI := (doubleGen P).normedGroup
      Metric.gromovProduct (1 : Double A) x.prod y.prod = gromovWord P x.toList y.toList := by
  intro x
  induction x using Word.consRecOn with
  | empty =>
    intro y
    let := (doubleGen P).normedGroup
    simp [Word.prod_empty, gromovWord]
  | cons i a xs hxs ha ih =>
    intro y
    induction y using Word.consRecOn with
    | empty =>
      let := (doubleGen P).normedGroup
      simp [Word.prod_empty, gromovWord]
    | cons j b ys hys hb _ =>
      let := (doubleGen P).normedGroup
      have hdist_x : dist (1 : Double A) (Word.cons (i := i) a xs hxs ha).prod =
          (P.wordLength a : ℝ) + (wordWeight P xs : ℝ) := by
        rw [dist_eq_wordLength_inv_mul, inv_one, one_mul, wordLength_doubleGen_eq,
          wordWeight_cons, Nat.cast_add]
      have hdist_y : dist (1 : Double A) (Word.cons (i := j) b ys hys hb).prod =
          (P.wordLength b : ℝ) + (wordWeight P ys : ℝ) := by
        rw [dist_eq_wordLength_inv_mul, inv_one, one_mul, wordLength_doubleGen_eq,
          wordWeight_cons, Nat.cast_add]
      change Metric.gromovProduct (1 : Double A) (Word.cons (i := i) a xs hxs ha).prod
          (Word.cons (i := j) b ys hys hb).prod =
        gromovWord P (⟨i, a⟩ :: xs.toList) (⟨j, b⟩ :: ys.toList)
      unfold gromovWord
      by_cases hij : i ≠ j
      · rw [if_pos hij, Metric.gromovProduct_eq, hdist_x, hdist_y, dist_eq_wordLength_inv_mul,
          wordLength_inv_mul_of_ne_idx P hij a b xs ys hxs ha hys hb,
          wordWeight_cons, wordWeight_cons]
        push_cast
        ring
      · push Not at hij
        subst hij
        rw [if_neg (not_not.mpr rfl)]
        by_cases hab : a = b
        · subst hab
          rw [if_pos rfl, ← ih ys, Metric.gromovProduct_eq, Metric.gromovProduct_eq]
          have hxs_d : dist (1 : Double A) xs.prod = (wordWeight P xs : ℝ) := by
            rw [dist_eq_wordLength_inv_mul, inv_one, one_mul, wordLength_doubleGen_eq]
          have hys_d : dist (1 : Double A) ys.prod = (wordWeight P ys : ℝ) := by
            rw [dist_eq_wordLength_inv_mul, inv_one, one_mul, wordLength_doubleGen_eq]
          have hcancel : (Word.cons (i := i) a xs hxs ha).prod⁻¹ *
              (Word.cons (i := i) a ys hys hb).prod = xs.prod⁻¹ * ys.prod := by
            rw [Word.prod_cons, Word.prod_cons, mul_inv_rev]
            group
          rw [hdist_x, hdist_y, hxs_d, hys_d, dist_eq_wordLength_inv_mul,
            dist_eq_wordLength_inv_mul, hcancel]
          ring
        · rw [if_neg hab, Metric.gromovProduct_eq, hdist_x, hdist_y, dist_eq_wordLength_inv_mul,
            wordLength_inv_mul_of_same_idx_ne P hab xs ys hxs ha hys hb]
          let := P.normedGroup
          rw [Metric.gromovProduct_eq, dist_eq_wordLength_inv_mul, dist_eq_wordLength_inv_mul,
            dist_eq_wordLength_inv_mul, inv_one, one_mul, one_mul]
          push_cast
          ring

private lemma gromovWord_four_point [DecidableEq A] {δ : ℝ} (hδ : P.IsHyperbolicWith δ) :
    ∀ xs ys zs : List (Σ _ : Fin 2, A),
      min (gromovWord P xs ys) (gromovWord P ys zs) - δ ≤ gromovWord P xs zs := by
  have hδ_nn : 0 ≤ δ := by
    let := P.normedGroup
    have h0 := hδ 1 1 1 1
    simp only [Metric.gromovProduct_self_left, min_self, zero_sub] at h0
    linarith
  intro xs
  induction xs with
  | nil =>
    intro ys zs
    have h1 : gromovWord P [] ys = 0 := rfl
    have h2 : gromovWord P [] zs = 0 := rfl
    rw [h1, h2]
    have := gromovWord_nonneg P ys zs
    have : min (0 : ℝ) (gromovWord P ys zs) = 0 := min_eq_left this
    linarith
  | cons x xs ih =>
    intro ys zs
    rcases x with ⟨i, a⟩
    cases ys with
    | nil =>
      have h1 : gromovWord P (⟨i, a⟩ :: xs) [] = 0 := rfl
      rw [h1]
      have hnn := gromovWord_nonneg P (⟨i, a⟩ :: xs) zs
      have hmin : min (0 : ℝ) (gromovWord P [] zs) ≤ 0 := min_le_left _ _
      linarith
    | cons y ys =>
      rcases y with ⟨j, b⟩
      cases zs with
      | nil =>
        have h1 : gromovWord P (⟨j, b⟩ :: ys) [] = 0 := rfl
        have h2 : gromovWord P (⟨i, a⟩ :: xs) [] = 0 := rfl
        rw [h1, h2]
        have hmin : min (gromovWord P (⟨i, a⟩ :: xs) (⟨j, b⟩ :: ys)) 0 ≤ 0 := min_le_right _ _
        linarith
      | cons z zs =>
        rcases z with ⟨k, c⟩
        by_cases hij : i ≠ j
        · have h1 : gromovWord P (⟨i, a⟩ :: xs) (⟨j, b⟩ :: ys) = 0 := by
            simp [gromovWord, hij]
          rw [h1]
          have hnn := gromovWord_nonneg P (⟨i, a⟩ :: xs) (⟨k, c⟩ :: zs)
          have hmin : min (0 : ℝ) (gromovWord P (⟨j, b⟩ :: ys) (⟨k, c⟩ :: zs)) ≤ 0 :=
            min_le_left _ _
          linarith
        · by_cases hjk : j ≠ k
          · have h1 : gromovWord P (⟨j, b⟩ :: ys) (⟨k, c⟩ :: zs) = 0 := by
              simp [gromovWord, hjk]
            rw [h1]
            have hnn := gromovWord_nonneg P (⟨i, a⟩ :: xs) (⟨k, c⟩ :: zs)
            have hmin : min (gromovWord P (⟨i, a⟩ :: xs) (⟨j, b⟩ :: ys)) 0 ≤ 0 :=
              min_le_right _ _
            linarith
          · push Not at hij hjk
            subst hij
            subst hjk
            by_cases hab : a = b
            · subst hab
              by_cases hbc : a = c
              · subst hbc
                simp only [gromovWord, ne_eq, not_true_eq_false, ↓reduceIte]
                have hstep := ih ys zs
                rw [← add_min]
                linarith
              · have h1 : gromovWord P (⟨i, a⟩ :: ys) (⟨i, c⟩ :: zs) =
                    gromovWord P (⟨i, a⟩ :: xs) (⟨i, c⟩ :: zs) := by
                  simp [gromovWord, hbc]
                rw [h1]
                have hmin : min (gromovWord P (⟨i, a⟩ :: xs) (⟨i, a⟩ :: ys))
                    (gromovWord P (⟨i, a⟩ :: xs) (⟨i, c⟩ :: zs)) ≤
                    gromovWord P (⟨i, a⟩ :: xs) (⟨i, c⟩ :: zs) := min_le_right _ _
                linarith
            · by_cases hbc : b = c
              · subst hbc
                have h1 : gromovWord P (⟨i, a⟩ :: xs) (⟨i, b⟩ :: ys) =
                    gromovWord P (⟨i, a⟩ :: xs) (⟨i, b⟩ :: zs) := by
                  simp [gromovWord, hab]
                rw [h1]
                have hmin : min (gromovWord P (⟨i, a⟩ :: xs) (⟨i, b⟩ :: zs))
                    (gromovWord P (⟨i, b⟩ :: ys) (⟨i, b⟩ :: zs)) ≤
                    gromovWord P (⟨i, a⟩ :: xs) (⟨i, b⟩ :: zs) := min_le_left _ _
                linarith
              · by_cases hac : a = c
                · subst hac
                  have h1 : gromovWord P (⟨i, a⟩ :: xs) (⟨i, b⟩ :: ys) =
                      letI := P.normedGroup; Metric.gromovProduct (1 : A) a b := by
                    simp [gromovWord, hab]
                  have h2 : gromovWord P (⟨i, a⟩ :: xs) (⟨i, a⟩ :: zs) =
                      (P.wordLength a : ℝ) + gromovWord P xs zs := by
                    simp [gromovWord]
                  rw [h1, h2]
                  have hle_a : (letI := P.normedGroup; Metric.gromovProduct (1 : A) a b) ≤
                      (P.wordLength a : ℝ) := by
                    let := P.normedGroup
                    have h := Metric.gromovProduct_le_dist_left (1 : A) a b
                    simpa [dist_eq_wordLength_inv_mul, inv_one, one_mul] using h
                  have hnn := gromovWord_nonneg P xs zs
                  have hmin : min (letI := P.normedGroup; Metric.gromovProduct (1 : A) a b)
                      (gromovWord P (⟨i, b⟩ :: ys) (⟨i, a⟩ :: zs)) ≤
                      (letI := P.normedGroup; Metric.gromovProduct (1 : A) a b) := min_le_left _ _
                  linarith
                · have h1 : gromovWord P (⟨i, a⟩ :: xs) (⟨i, b⟩ :: ys) =
                      letI := P.normedGroup; Metric.gromovProduct (1 : A) a b := by
                    simp [gromovWord, hab]
                  have h2 : gromovWord P (⟨i, b⟩ :: ys) (⟨i, c⟩ :: zs) =
                      letI := P.normedGroup; Metric.gromovProduct (1 : A) b c := by
                    simp [gromovWord, hbc]
                  have h3 : gromovWord P (⟨i, a⟩ :: xs) (⟨i, c⟩ :: zs) =
                      letI := P.normedGroup; Metric.gromovProduct (1 : A) a c := by
                    simp [gromovWord, hac]
                  rw [h1, h2, h3]
                  exact hδ 1 a b c

private lemma doubleGen_isHyperbolicWith [DecidableEq A] {δ : ℝ} (hδ : P.IsHyperbolicWith δ) :
    (doubleGen P).IsHyperbolicWith δ := by
  let := (doubleGen P).normedGroup
  intro w x y z
  have hshift : ∀ u v : Double A,
      Metric.gromovProduct w u v = Metric.gromovProduct (1 : Double A) (w⁻¹ * u) (w⁻¹ * v) := by
    intro u v
    simp only [Metric.gromovProduct_eq, dist_eq_wordLength_inv_mul]
    have h1 : (1 : Double A)⁻¹ * (w⁻¹ * u) = w⁻¹ * u := by simp
    have h2 : (1 : Double A)⁻¹ * (w⁻¹ * v) = w⁻¹ * v := by simp
    have h3 : (w⁻¹ * u)⁻¹ * (w⁻¹ * v) = u⁻¹ * v := by group
    rw [h1, h2, h3]
  rw [hshift x y, hshift y z, hshift x z]
  set wx := Word.equiv (w⁻¹ * x)
  set wy := Word.equiv (w⁻¹ * y)
  set wz := Word.equiv (w⁻¹ * z)
  have hx : wx.prod = w⁻¹ * x := Word.equiv.symm_apply_apply (w⁻¹ * x)
  have hy : wy.prod = w⁻¹ * y := Word.equiv.symm_apply_apply (w⁻¹ * y)
  have hz : wz.prod = w⁻¹ * z := Word.equiv.symm_apply_apply (w⁻¹ * z)
  rw [← hx, ← hy, ← hz,
    gromovProduct_one_eq_gromovWord P wx wy,
    gromovProduct_one_eq_gromovWord P wy wz,
    gromovProduct_one_eq_gromovWord P wx wz]
  exact gromovWord_four_point P hδ wx.toList wy.toList wz.toList

end Construction

end OMA.HyperbolicDouble

theorem OMA.solution :
    OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R3_H1_R1.H2 := by
  intro A _ _
  classical
  obtain ⟨n, P, δ, hδ⟩ := Group.IsHyperbolic.exists_isHyperbolicWith A
  exact ⟨n + n, OMA.HyperbolicDouble.doubleGen P, δ,
    OMA.HyperbolicDouble.doubleGen_isHyperbolicWith P hδ⟩
