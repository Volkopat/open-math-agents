import OMAStatements.S_oeis_a208064

-- Original proof by @marcusbuffett in #33226, statement by @clementtrecourt.
-- Split the rows by index parity, then count the descending chains independently.

namespace OMA.A208064

abbrev Row := Fin 3 → Fin 2

abbrev LegalRow := {r : Row // r ≠ (fun _ => 0) ∧ r ≠ (fun _ => 1)}

def ChainCondition {m : ℕ} (rows : Fin m → LegalRow) : Prop :=
  ∀ (i j : Fin m), i ≤ j → ∀ c : Fin 3, (rows j).val c ≤ (rows i).val c

instance {m : ℕ} : DecidablePred (@ChainCondition m) := fun rows => by
  unfold ChainCondition
  infer_instance

abbrev Chain (m : ℕ) := {rows : Fin m → LegalRow // ChainCondition rows}

end OMA.A208064

namespace OMA.A208064

open OMA.S_oeis_a208064

private def Good {n : ℕ} (x : Fin n → Row) : Prop :=
  (∀ i, x i ≠ (fun _ => 0) ∧ x i ≠ (fun _ => 1)) ∧
  ∀ (i : ℕ) (hi : i + 2 < n) (c : Fin 3), x ⟨i + 2, hi⟩ c ≤ x ⟨i, by omega⟩ c

private lemma row_iff : ∀ r : Row,
    (((r 0 : ℕ), (r 1 : ℕ), (r 2 : ℕ)) ≠ (0, 0, 0) ∧
      ((r 0 : ℕ), (r 1 : ℕ), (r 2 : ℕ)) ≠ (1, 1, 1)) ↔
      r ≠ (fun _ => 0) ∧ r ≠ (fun _ => 1) := by decide

private lemma col_iff : ∀ a b c : Fin 2,
    (((a : ℕ), (b : ℕ), (c : ℕ)) ≠ (0, 0, 1) ∧
      ((a : ℕ), (b : ℕ), (c : ℕ)) ≠ (0, 1, 1)) ↔ c ≤ a := by decide

private lemma avoids_iff {n : ℕ} (x : Fin n → Row) : avoids x = true ↔ Good x := by
  simp only [avoids, decide_eq_true_eq, Good]
  constructor
  · rintro ⟨hor, ver⟩
    refine ⟨?_, ?_⟩
    · intro i
      refine (row_iff (x i)).mp ?_
      simpa [S_oeis_a208064.get, i.isLt] using hor i i.isLt 0 (by decide)
    · intro i hi j
      have h0 : i < n := by omega
      have h1 : i + 1 < n := by omega
      exact (col_iff _ (x ⟨i + 1, h1⟩ j) _).mp (by
        simpa [S_oeis_a208064.get, h0, h1, hi, j.isLt] using ver i (by omega) j j.isLt)
  · rintro ⟨hor, ver⟩
    refine ⟨?_, ?_⟩
    · intro i hi j hj
      have : j = 0 := by omega
      subst j
      simpa [S_oeis_a208064.get, hi] using (row_iff _).mpr (hor ⟨i, hi⟩)
    · intro i hi j hj
      have h0 : i < n := by omega
      have h1 : i + 1 < n := by omega
      have h2 : i + 2 < n := by omega
      simpa [S_oeis_a208064.get, h0, h1, h2, hj] using
        (col_iff _ (x ⟨i + 1, h1⟩ ⟨j, hj⟩) _).mpr (ver i h2 ⟨j, hj⟩)

private def rowsAt {n m : ℕ} (x : {x : Fin n → Row // Good x}) (e : ℕ)
    (h : ∀ i : Fin m, 2 * (i : ℕ) + e < n) : Chain m :=
  ⟨fun i => ⟨x.val ⟨2 * (i : ℕ) + e, h i⟩, x.property.1 _⟩, by
    cases m with
    | zero => intro i; exact Fin.elim0 i
    | succ m =>
      intro i j hij c
      let f (k : Fin (m + 1)) := x.val ⟨2 * (k : ℕ) + e, h k⟩ c
      apply ((Fin.antitone_iff_succ_le (f := f)).mpr ?_) hij
      intro k
      have hk := h k.succ
      have hs : 2 * (k : ℕ) + e + 2 < n := by simp only [Fin.val_succ] at hk; omega
      have he : (⟨2 * (k.succ : ℕ) + e, hk⟩ : Fin n) = ⟨2 * (k : ℕ) + e + 2, hs⟩ :=
        Fin.ext (by simp only [Fin.val_succ]; omega)
      simp only [f, he, Fin.val_castSucc]
      exact x.property.2 _ hs c⟩

private def splitRows {n : ℕ} (x : {x : Fin n → Row // Good x}) :
    Chain (n / 2 + n % 2) × Chain (n / 2) :=
  (rowsAt x 0 (fun i => by have hi := i.isLt; omega),
   rowsAt x 1 (fun i => by have hi := i.isLt; omega))

private def mix {n : ℕ} (p : Chain (n / 2 + n % 2) × Chain (n / 2)) (i : Fin n) : LegalRow :=
  if hi : (i : ℕ) % 2 = 0 then
    p.1.val ⟨(i : ℕ) / 2, by have hb := i.isLt; omega⟩
  else
    p.2.val ⟨(i : ℕ) / 2, by have hb := i.isLt; omega⟩

private def mergeRows {n : ℕ} (p : Chain (n / 2 + n % 2) × Chain (n / 2)) :
    {x : Fin n → Row // Good x} :=
  ⟨fun i => (mix p i).val, ⟨fun i => (mix p i).property, by
    intro i hi c
    by_cases hp : i % 2 = 0
    · simp only [mix, dif_pos hp, dif_pos (show (i + 2) % 2 = 0 by omega)]
      exact p.1.property _ _ (by change i / 2 ≤ (i + 2) / 2; omega) c
    · simp only [mix, dif_neg hp, dif_neg (show (i + 2) % 2 ≠ 0 by omega)]
      exact p.2.property _ _ (by change i / 2 ≤ (i + 2) / 2; omega) c⟩⟩

private def parityEquiv (n : ℕ) :
    {x : Fin n → Row // Good x} ≃ Chain (n / 2 + n % 2) × Chain (n / 2) where
  toFun := splitRows
  invFun := mergeRows
  left_inv x := by
    apply Subtype.ext
    funext i
    change (mix (splitRows x) i).val = x.val i
    by_cases hi : (i : ℕ) % 2 = 0
    · simp only [mix, dif_pos hi, splitRows, rowsAt]
      exact congrArg x.val (Fin.ext (by dsimp; omega))
    · simp only [mix, dif_neg hi, splitRows, rowsAt]
      exact congrArg x.val (Fin.ext (by dsimp; omega))
  right_inv p := by
    apply Prod.ext <;> apply Subtype.ext <;> funext i <;> apply Subtype.ext
    · change (mix p ⟨2 * (i : ℕ) + 0, _⟩).val = (p.1.val i).val
      simp (disch := omega) only [mix, dif_pos]
      exact congrArg (fun j => (p.1.val j).val) (Fin.ext (by dsimp; omega))
    · change (mix p ⟨2 * (i : ℕ) + 1, _⟩).val = (p.2.val i).val
      simp (disch := omega) only [mix, dif_neg]
      exact congrArg (fun j => (p.2.val j).val) (Fin.ext (by dsimp; omega))

theorem array_card (n : ℕ) :
    a n = (Fintype.card (Chain (n / 2 + n % 2)) : ℤ) * Fintype.card (Chain (n / 2)) := by
  let e := (Equiv.subtypeEquivRight (fun x : Fin n → Row =>
    show x ∈ Finset.univ.filter (fun x => avoids x) ↔ Good x by
      simp [avoids_iff])).trans (parityEquiv n)
  have h := Fintype.card_congr e
  rw [Fintype.card_coe, Fintype.card_prod] at h
  unfold a
  exact_mod_cast h

end OMA.A208064

namespace OMA.A208064

private abbrev RowLE (a b : LegalRow) := ∀ c : Fin 3, a.val c ≤ b.val c

private abbrev StrictPair :=
  {p : LegalRow × LegalRow // RowLE p.2 p.1 ∧ p.1 ≠ p.2}

set_option maxRecDepth 2048 in
private theorem no_third_row :
    ∀ (a b c : LegalRow), RowLE b a → RowLE c b → a ≠ b → b = c := by
  have check : ∀ p : LegalRow × LegalRow × LegalRow,
      ¬ (RowLE p.2.1 p.1 ∧ RowLE p.2.2 p.2.1 ∧ p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2) := by
    decide
  intro a b c hab hbc hne
  by_contra h
  exact check (a, b, c) ⟨hab, hbc, hne, h⟩

private theorem strict_pair_card : Fintype.card StrictPair = 6 := by decide

private def constantChain {m : ℕ} (a : LegalRow) : Chain m :=
  ⟨fun _ => a, fun _ _ _ _ => le_rfl⟩

private def consChain {m : ℕ} (a : LegalRow) (x : Chain (m + 1))
    (h : RowLE (x.val 0) a) : Chain (m + 2) := ⟨Fin.cons a x.val, by
  intro i
  induction i using Fin.cases with
  | zero =>
    intro j
    induction j using Fin.cases with
    | zero => exact fun _ _ => le_rfl
    | succ j =>
      intro _ c
      simpa only [Fin.cons_succ, Fin.cons_zero] using (x.property 0 j (Fin.zero_le j) c).trans (h c)
  | succ i =>
    intro j
    induction j using Fin.cases with
    | zero =>
      intro hij
      simp only [Fin.le_def, Fin.val_succ, Fin.val_zero] at hij
      omega
    | succ j =>
      intro hij c
      simpa only [Fin.cons_succ] using x.property i j (Fin.succ_le_succ_iff.mp hij) c⟩

private def tailChain {m : ℕ} (x : Chain (m + 2)) : Chain (m + 1) :=
  ⟨fun i => x.val i.succ, fun i j h => x.property i.succ j.succ (Fin.succ_le_succ_iff.mpr h)⟩

private theorem chain_ext {m : ℕ} {x y : Chain m} (h : ∀ i, x.val i = y.val i) : x = y :=
  Subtype.ext (funext h)

-- If the first two rows differ, all following rows equal the second.
private def chainStep (m : ℕ) : Chain (m + 2) ≃ Chain (m + 1) ⊕ StrictPair where
  toFun x := if h : x.val 0 = x.val (Fin.succ 0) then .inl (tailChain x)
    else .inr ⟨(x.val 0, x.val (Fin.succ 0)), x.property 0 _ (Fin.zero_le _), h⟩
  invFun
    | .inl x => consChain (x.val 0) x fun _ => le_rfl
    | .inr p => consChain p.val.1 (constantChain p.val.2) p.property.1
  left_inv x := by
    by_cases h : x.val 0 = x.val (Fin.succ 0)
    · simp only [h, dite_true]
      apply chain_ext
      intro i
      exact Fin.cases (by simpa [consChain, tailChain] using h.symm)
        (fun j => by simp [consChain, tailChain]) i
    · simp only [h, dite_false]
      apply chain_ext
      intro i
      refine Fin.cases (by simp [consChain]) (fun j => ?_) i
      simpa [consChain, constantChain] using no_third_row (x.val 0) (x.val (Fin.succ 0))
        (x.val j.succ) (x.property 0 _ (Fin.zero_le _))
          (x.property (Fin.succ 0) j.succ (Fin.succ_le_succ_iff.mpr (Fin.zero_le j))) h
  right_inv x := by
    cases x with
    | inl x =>
      simp only [consChain, Fin.cons_zero, Fin.cons_succ, dite_true, Sum.inl.injEq]
      apply chain_ext
      intro i
      simp [tailChain]
    | inr p =>
      simp only [consChain, Fin.cons_zero, Fin.cons_succ, constantChain, p.property.2, dite_false]

private theorem chain_card_succ (m : ℕ) : Fintype.card (Chain (m + 1)) = 6 * (m + 1) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [Fintype.card_congr (chainStep m), Fintype.card_sum, ih, strict_pair_card]
    omega

theorem chain_card (m : ℕ) : Fintype.card (Chain m) = if m = 0 then 1 else 6 * m := by
  cases m with
  | zero => decide
  | succ m => simpa using chain_card_succ m

end OMA.A208064

namespace OMA.A208064

open PowerSeries OMA.S_oeis_a208064

theorem main_of_card (h : ∀ n : ℕ, a n =
    (↑((if n / 2 + n % 2 = 0 then 1 else 6 * (n / 2 + n % 2)) *
      (if n / 2 = 0 then 1 else 6 * (n / 2)) : ℕ) : ℤ)) :
    type_of% @OMA.S_oeis_a208064.main := by
  have form (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = 9 * (n : ℚ) ^ 2 - 9 * (↑(n % 2) : ℚ) := by
    rw [h, if_neg (by omega), if_neg (by omega)]
    change (↑((6 * (n / 2 + n % 2)) * (6 * (n / 2)) : ℕ) : ℚ) = _
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    have e : (n : ℚ) = 2 * (↑(n / 2) : ℚ) + (↑(n % 2) : ℚ) := by
      exact_mod_cast (show n = 2 * (n / 2) + n % 2 by omega)
    rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with hp | hp <;>
      rw [hp] at e ⊢ <;> rw [e] <;> ring
  refine ⟨?_, fun n hn he => ?_, fun n hn ho => ?_⟩
  · let b : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ)
    let A := mk b
    have e : A * ((1 - X) ^ 3 * (1 + X)) =
        A - C 2 * (X ^ 1 * A) + C 2 * (X ^ 3 * A) - X ^ 4 * A := by
      rw [map_ofNat C 2]
      ring
    have e' : (6 * X * (1 + 4 * X + 2 * X ^ 3 - X ^ 4) : ℚ⟦X⟧) =
        C 6 * X ^ 1 + C 24 * X ^ 2 + C 12 * X ^ 4 - C 6 * X ^ 5 := by
      simp only [map_ofNat]
      ring
    change A * _ = _
    rw [e, e']
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, A, coeff_mk]
    by_cases hn : n < 6
    · interval_cases n <;> norm_num [b, h]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
      simp (disch := omega) [Nat.add_sub_assoc, Nat.cast_add, b, form,
        show (k + 6) % 2 = (k + 2) % 2 by omega,
        show (k + 5) % 2 = (k + 3) % 2 by omega]
      ring
  · simp [form n hn, Nat.even_iff.mp he]
  · simp [form n hn, Nat.odd_iff.mp ho]

end OMA.A208064

open OMA.A208064 in
theorem OMA.solution : type_of% @OMA.S_oeis_a208064.main := by
  apply main_of_card
  intro n
  rw [array_card, chain_card, chain_card, Nat.cast_mul]
