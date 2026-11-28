import OMAStatements.S_oeis_a159227
import Mathlib

section ProofHelpers

private def sqVal : Fin 6 → Fin 28
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 9
  | 4 => 16
  | 5 => 25

private lemma sqVal_injective : Function.Injective sqVal := by
  intro i j h
  revert i j h
  decide

private lemma isSquare_iff_exists_sqVal (v : Fin 28) :
    OMA.S_oeis_a159227.isSquare v.1 ↔ ∃ s : Fin 6, sqVal s = v := by
  revert v
  decide

private def valid2x2 (a b c d : Fin 6) : Bool :=
  (sqVal a).1 + (sqVal b).1 + (sqVal c).1 + (sqVal d).1 == 27

private lemma valid2x2_card :
    (Finset.univ.filter
      (fun b : Fin 6 × Fin 6 × Fin 6 × Fin 6 => valid2x2 b.1 b.2.1 b.2.2.1 b.2.2.2 = true)).card =
      28 := by
  decide

private lemma valid2x2_symm_row {a b c d : Fin 6} (h : valid2x2 a b c d = true) :
    valid2x2 b a d c = true := by
  simp only [valid2x2, beq_iff_eq] at h ⊢
  omega

private lemma valid2x2_symm_col {a b c d : Fin 6} (h : valid2x2 a b c d = true) :
    valid2x2 c d a b = true := by
  simp only [valid2x2, beq_iff_eq] at h ⊢
  omega

private lemma valid2x2_symm_transpose {a b c d : Fin 6} (h : valid2x2 a b c d = true) :
    valid2x2 a c b d = true := by
  simp only [valid2x2, beq_iff_eq] at h ⊢
  omega

private def check3x3 : Bool :=
  (List.finRange 6).all fun a00 =>
  (List.finRange 6).all fun a01 =>
  (List.finRange 6).all fun a10 =>
  (List.finRange 6).all fun a11 =>
    if !(valid2x2 a00 a01 a10 a11) then true else
    (List.finRange 6).all fun a02 =>
    (List.finRange 6).all fun a12 =>
      if !(valid2x2 a01 a02 a11 a12) then true else
      (List.finRange 6).all fun a20 =>
      (List.finRange 6).all fun a21 =>
        if !(valid2x2 a10 a11 a20 a21) then true else
        (List.finRange 6).all fun a22 =>
          if !(valid2x2 a11 a12 a21 a22) then true else
          let req0 := decide (a00 = a20)
          let req1 := decide (a01 = a21)
          let req2 := decide (a02 = a22)
          let ceq0 := decide (a00 = a02)
          let ceq1 := decide (a10 = a12)
          let ceq2 := decide (a20 = a22)
          (req0 == req1 && req1 == req2) &&
          (ceq0 == ceq1 && ceq1 == ceq2) &&
          (req0 || ceq0)

private lemma check3x3_true : check3x3 = true := by
  decide

private lemma prop_3x3 {a00 a01 a02 a10 a11 a12 a20 a21 a22 : Fin 6}
    (h00 : valid2x2 a00 a01 a10 a11 = true)
    (h01 : valid2x2 a01 a02 a11 a12 = true)
    (h10 : valid2x2 a10 a11 a20 a21 = true)
    (h11 : valid2x2 a11 a12 a21 a22 = true) :
    ((a00 = a20 ↔ a01 = a21) ∧ (a01 = a21 ↔ a02 = a22)) ∧
    ((a00 = a02 ↔ a10 = a12) ∧ (a10 = a12 ↔ a20 = a22)) ∧
    (a00 = a20 ∨ a00 = a02) := by
  have h := check3x3_true
  dsimp [check3x3] at h
  replace h := (List.all_eq_true.mp h) a00 (List.mem_finRange _)
  replace h := (List.all_eq_true.mp h) a01 (List.mem_finRange _)
  replace h := (List.all_eq_true.mp h) a10 (List.mem_finRange _)
  replace h := (List.all_eq_true.mp h) a11 (List.mem_finRange _)
  simp only [h00, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  replace h := (List.all_eq_true.mp h) a02 (List.mem_finRange _)
  replace h := (List.all_eq_true.mp h) a12 (List.mem_finRange _)
  simp only [h01, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  replace h := (List.all_eq_true.mp h) a20 (List.mem_finRange _)
  replace h := (List.all_eq_true.mp h) a21 (List.mem_finRange _)
  simp only [h10, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  replace h := (List.all_eq_true.mp h) a22 (List.mem_finRange _)
  simp only [h11, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
    beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨r01, r12⟩, ⟨c01, c12⟩⟩, hor⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, hor⟩
  · constructor <;> intro heq <;> [exact decide_eq_true_eq.mp (r01 ▸ decide_eq_true heq);
      exact decide_eq_true_eq.mp (r01.symm ▸ decide_eq_true heq)]
  · constructor <;> intro heq <;> [exact decide_eq_true_eq.mp (r12 ▸ decide_eq_true heq);
      exact decide_eq_true_eq.mp (r12.symm ▸ decide_eq_true heq)]
  · constructor <;> intro heq <;> [exact decide_eq_true_eq.mp (c01 ▸ decide_eq_true heq);
      exact decide_eq_true_eq.mp (c01.symm ▸ decide_eq_true heq)]
  · constructor <;> intro heq <;> [exact decide_eq_true_eq.mp (c12 ▸ decide_eq_true heq);
      exact decide_eq_true_eq.mp (c12.symm ▸ decide_eq_true heq)]

private def isValid6 (n : ℕ) (g : Fin n → Fin n → Fin 6) : Prop :=
  ∀ i j : Fin n, ∀ (hi : i.1 + 1 < n) (hj : j.1 + 1 < n),
    valid2x2 (g i j) (g i ⟨j.1 + 1, hj⟩)
      (g ⟨i.1 + 1, hi⟩ j) (g ⟨i.1 + 1, hi⟩ ⟨j.1 + 1, hj⟩) = true

instance (n : ℕ) (g : Fin n → Fin n → Fin 6) : Decidable (isValid6 n g) := by
  unfold isValid6
  infer_instance

private def rowPer2 {n : ℕ} (g : Fin n → Fin n → Fin 6) : Prop :=
  ∀ i : Fin n, ∀ (hi : i.1 + 2 < n) (j : Fin n), g ⟨i.1 + 2, hi⟩ j = g i j

private def colPer2 {n : ℕ} (g : Fin n → Fin n → Fin 6) : Prop :=
  ∀ (i : Fin n) (j : Fin n), ∀ (hj : j.1 + 2 < n), g i ⟨j.1 + 2, hj⟩ = g i j

instance {n : ℕ} (g : Fin n → Fin n → Fin 6) : Decidable (rowPer2 g) := by
  unfold rowPer2
  infer_instance

instance {n : ℕ} (g : Fin n → Fin n → Fin 6) : Decidable (colPer2 g) := by
  unfold colPer2
  infer_instance

private lemma valid6_3x3 {n : ℕ} {g : Fin n → Fin n → Fin 6} (hg : isValid6 n g)
    {r c : ℕ} (hr : r + 2 < n) (hc : c + 2 < n) :
    ((g ⟨r, by omega⟩ ⟨c, by omega⟩ = g ⟨r + 2, hr⟩ ⟨c, by omega⟩ ↔
      g ⟨r, by omega⟩ ⟨c + 1, by omega⟩ = g ⟨r + 2, hr⟩ ⟨c + 1, by omega⟩) ∧
     (g ⟨r, by omega⟩ ⟨c + 1, by omega⟩ = g ⟨r + 2, hr⟩ ⟨c + 1, by omega⟩ ↔
      g ⟨r, by omega⟩ ⟨c + 2, hc⟩ = g ⟨r + 2, hr⟩ ⟨c + 2, hc⟩)) ∧
    ((g ⟨r, by omega⟩ ⟨c, by omega⟩ = g ⟨r, by omega⟩ ⟨c + 2, hc⟩ ↔
      g ⟨r + 1, by omega⟩ ⟨c, by omega⟩ = g ⟨r + 1, by omega⟩ ⟨c + 2, hc⟩) ∧
     (g ⟨r + 1, by omega⟩ ⟨c, by omega⟩ = g ⟨r + 1, by omega⟩ ⟨c + 2, hc⟩ ↔
      g ⟨r + 2, hr⟩ ⟨c, by omega⟩ = g ⟨r + 2, hr⟩ ⟨c + 2, hc⟩)) ∧
    (g ⟨r, by omega⟩ ⟨c, by omega⟩ = g ⟨r + 2, hr⟩ ⟨c, by omega⟩ ∨
     g ⟨r, by omega⟩ ⟨c, by omega⟩ = g ⟨r, by omega⟩ ⟨c + 2, hc⟩) := by
  have h00 := hg ⟨r, by omega⟩ ⟨c, by omega⟩ (by dsimp; omega) (by dsimp; omega)
  have h01 := hg ⟨r, by omega⟩ ⟨c + 1, by omega⟩ (by dsimp; omega) (by dsimp; omega)
  have h10 := hg ⟨r + 1, by omega⟩ ⟨c, by omega⟩ (by dsimp; omega) (by dsimp; omega)
  have h11 := hg ⟨r + 1, by omega⟩ ⟨c + 1, by omega⟩ (by dsimp; omega) (by dsimp; omega)
  have hr2 : (⟨r + 1 + 1, hr⟩ : Fin n) = ⟨r + 2, hr⟩ := Fin.ext rfl
  have hc2 : (⟨c + 1 + 1, hc⟩ : Fin n) = ⟨c + 2, hc⟩ := Fin.ext rfl
  dsimp only at h00 h01 h10 h11
  rw [hr2] at h10 h11
  rw [hc2] at h01 h11
  exact prop_3x3 h00 h01 h10 h11

private lemma valid6_dichotomy {n : ℕ} (hn : 3 ≤ n) {g : Fin n → Fin n → Fin 6}
    (hg : isValid6 n g) : rowPer2 g ∨ colPer2 g := by
  by_cases hr : rowPer2 g
  · exact Or.inl hr
  · right
    simp only [rowPer2, not_forall] at hr
    rcases hr with ⟨i₀, hi₀, j₀, hj₀⟩
    have hrow_step : ∀ (k : ℕ) (hk : k + 1 < n),
        (g ⟨i₀.1 + 2, hi₀⟩ ⟨k, by omega⟩ = g i₀ ⟨k, by omega⟩ ↔
         g ⟨i₀.1 + 2, hi₀⟩ ⟨k + 1, hk⟩ = g i₀ ⟨k + 1, hk⟩) := by
      intro k hk
      by_cases hk2 : k + 2 < n
      · have h3 := (valid6_3x3 hg hi₀ hk2).1.1
        have hfin : (⟨i₀.1, by omega⟩ : Fin n) = i₀ := Fin.ext rfl
        simpa [hfin, eq_comm] using h3
      · have hk1 : 1 ≤ k := by omega
        have h3 := (valid6_3x3 hg hi₀ (show (k - 1) + 2 < n by omega)).1.2
        have hfin : (⟨i₀.1, by omega⟩ : Fin n) = i₀ := Fin.ext rfl
        have hfk : (⟨k, by omega⟩ : Fin n) = ⟨k - 1 + 1, by omega⟩ := Fin.ext (by dsimp; omega)
        have hfk1 : (⟨k + 1, hk⟩ : Fin n) = ⟨k - 1 + 2, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hfin] at h3
        rw [hfk, hfk1]
        simpa [eq_comm] using h3
    have hrow_all_eq : ∀ j1 j2 : Fin n,
        (g ⟨i₀.1 + 2, hi₀⟩ j1 = g i₀ j1 ↔ g ⟨i₀.1 + 2, hi₀⟩ j2 = g i₀ j2) := by
      have h0 : ∀ m : ℕ, ∀ hm : m < n,
          (g ⟨i₀.1 + 2, hi₀⟩ ⟨0, by omega⟩ = g i₀ ⟨0, by omega⟩ ↔
           g ⟨i₀.1 + 2, hi₀⟩ ⟨m, hm⟩ = g i₀ ⟨m, hm⟩) := by
        intro m
        induction m with
        | zero => intro hm; rfl
        | succ m ihm =>
          intro hm
          exact (ihm (by omega)).trans (hrow_step m hm)
      intro j1 j2
      exact (h0 j1.1 j1.2).symm.trans (h0 j2.1 j2.2)
    have hrow_ne : ∀ j : Fin n, g ⟨i₀.1 + 2, hi₀⟩ j ≠ g i₀ j := by
      intro j hjeq
      exact hj₀ ((hrow_all_eq j j₀).mp hjeq)
    intro i j hj
    have hi₀_eq : g i₀ j = g i₀ ⟨j.1 + 2, hj⟩ := by
      have h3 := (valid6_3x3 hg hi₀ hj).2.2
      have hfin : (⟨i₀.1, by omega⟩ : Fin n) = i₀ := Fin.ext rfl
      have hjfin : (⟨j.1, by omega⟩ : Fin n) = j := Fin.ext rfl
      rw [hfin, hjfin] at h3
      rcases h3 with heq | heq
      · exact False.elim (hrow_ne j heq.symm)
      · exact heq
    have hcol_step : ∀ (k : ℕ) (hk : k + 1 < n),
        (g ⟨k, by omega⟩ j = g ⟨k, by omega⟩ ⟨j.1 + 2, hj⟩ ↔
         g ⟨k + 1, hk⟩ j = g ⟨k + 1, hk⟩ ⟨j.1 + 2, hj⟩) := by
      intro k hk
      by_cases hk2 : k + 2 < n
      · have h3 := (valid6_3x3 hg hk2 hj).2.1.1
        have hjfin : (⟨j.1, by omega⟩ : Fin n) = j := Fin.ext rfl
        simpa [hjfin] using h3
      · have hk1 : 1 ≤ k := by omega
        have h3 := (valid6_3x3 hg (show (k - 1) + 2 < n by omega) hj).2.1.2
        have hjfin : (⟨j.1, by omega⟩ : Fin n) = j := Fin.ext rfl
        have hfk : (⟨k, by omega⟩ : Fin n) = ⟨k - 1 + 1, by omega⟩ := Fin.ext (by dsimp; omega)
        have hfk1 : (⟨k + 1, hk⟩ : Fin n) = ⟨k - 1 + 2, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hjfin] at h3
        rw [hfk, hfk1]
        exact h3
    have hcol_all_eq : ∀ i1 i2 : Fin n,
        (g i1 j = g i1 ⟨j.1 + 2, hj⟩ ↔ g i2 j = g i2 ⟨j.1 + 2, hj⟩) := by
      have h0 : ∀ m : ℕ, ∀ hm : m < n,
          (g ⟨0, by omega⟩ j = g ⟨0, by omega⟩ ⟨j.1 + 2, hj⟩ ↔
           g ⟨m, hm⟩ j = g ⟨m, hm⟩ ⟨j.1 + 2, hj⟩) := by
        intro m
        induction m with
        | zero => intro hm; rfl
        | succ m ihm =>
          intro hm
          exact (ihm (by omega)).trans (hcol_step m hm)
      intro i1 i2
      exact (h0 i1.1 i1.2).symm.trans (h0 i2.1 i2.2)
    exact ((hcol_all_eq i₀ i).mp hi₀_eq).symm

private lemma total_eq_card_valid6 (n : ℕ) :
    OMA.S_oeis_a159227.total n = (Finset.univ.filter (fun g : Fin n → Fin n → Fin 6 => isValid6 n g)).card := by
  unfold OMA.S_oeis_a159227.total
  refine Finset.card_bij
    (fun x hx => fun i j => Classical.choose ((isSquare_iff_exists_sqVal (x i j)).mp
      ((Finset.mem_filter.mp hx).2.1 i j)))
    ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun i j hi hj => ?_⟩
    have hsum := (Finset.mem_filter.mp hx).2.2 i.1 j.1 hi hj
    have hsq : ∀ (r c : Fin n),
        sqVal (Classical.choose ((isSquare_iff_exists_sqVal (x r c)).mp
          ((Finset.mem_filter.mp hx).2.1 r c))) = x r c := fun r c =>
      Classical.choose_spec ((isSquare_iff_exists_sqVal (x r c)).mp
        ((Finset.mem_filter.mp hx).2.1 r c))
    simp only [valid2x2, beq_iff_eq, hsq]
    exact hsum
  · intro x hx y hy hxy
    funext i j
    have hsqx := Classical.choose_spec ((isSquare_iff_exists_sqVal (x i j)).mp
      ((Finset.mem_filter.mp hx).2.1 i j))
    have hsqy := Classical.choose_spec ((isSquare_iff_exists_sqVal (y i j)).mp
      ((Finset.mem_filter.mp hy).2.1 i j))
    have hij := congr_fun (congr_fun hxy i) j
    rw [← hsqx, ← hsqy, hij]
  · intro g hg
    refine ⟨fun i j => sqVal (g i j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
    · intro i j
      exact (isSquare_iff_exists_sqVal (sqVal (g i j))).mpr ⟨g i j, rfl⟩
    · intro i j hi hj
      have h := (Finset.mem_filter.mp hg).2 ⟨i, by omega⟩ ⟨j, by omega⟩ hi hj
      simpa [valid2x2] using h
    · funext i j
      apply sqVal_injective
      exact Classical.choose_spec ((isSquare_iff_exists_sqVal (sqVal (g i j))).mp
        ((isSquare_iff_exists_sqVal (sqVal (g i j))).mpr ⟨g i j, rfl⟩))

private def isValidStrip (n : ℕ) (s : Fin 2 → Fin n → Fin 6) : Prop :=
  ∀ j : Fin n, ∀ (hj : j.1 + 1 < n),
    valid2x2 (s 0 j) (s 0 ⟨j.1 + 1, hj⟩)
      (s 1 j) (s 1 ⟨j.1 + 1, hj⟩) = true

instance (n : ℕ) (s : Fin 2 → Fin n → Fin 6) : Decidable (isValidStrip n s) := by
  unfold isValidStrip
  infer_instance

private def compOfCol : Fin 6 × Fin 6 → Option (Fin 8)
  | (0, 1) | (1, 0) => some 0
  | (1, 5) | (5, 1) => some 1
  | (1, 3) | (3, 1) => some 2
  | (1, 4) | (4, 1) => some 3
  | (0, 3) | (3, 0) => some 4
  | (3, 3) => some 5
  | (1, 1) => some 6
  | (0, 5) | (3, 4) | (4, 3) | (5, 0) => some 7
  | _ => none

private def partner : Fin 8 → Fin 8
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 5
  | 5 => 4
  | 6 => 7
  | 7 => 6

private lemma partner_partner (c : Fin 8) : partner (partner c) = c := by
  fin_cases c <;> rfl

private lemma valid2x2_iff_comp (x y : Fin 6 × Fin 6) :
    valid2x2 x.1 y.1 x.2 y.2 = true ↔
      ∃ c : Fin 8, compOfCol x = some c ∧ compOfCol y = some (partner c) := by
  revert x y
  decide

private def compSize : Fin 8 → ℕ
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 1
  | 6 => 1
  | 7 => 4

private lemma comp_card (c : Fin 8) :
    (Finset.univ.filter (fun p : Fin 6 × Fin 6 => compOfCol p = some c)).card = compSize c := by
  revert c
  decide

private lemma card_validStrips {n : ℕ} (hn : 2 ≤ n) :
    (Finset.univ.filter (fun s : Fin 2 → Fin n → Fin 6 => isValidStrip n s)).card =
      ∑ c : Fin 8, ∏ j : Fin n, if Even j.1 then compSize c else compSize (partner c) := by
  rcases n with _ | m
  · omega
  let S (c : Fin 8) : Finset (Fin 2 → Fin (m + 1) → Fin 6) :=
    Finset.univ.filter fun s =>
      ∀ j : Fin (m + 1), compOfCol (s 0 j, s 1 j) = some (if Even j.1 then c else partner c)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 8))) S := by
    intro c1 _ c2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro s hs1 hs2
    have h1 := (Finset.mem_filter.mp hs1).2 ⟨0, by omega⟩
    have h2 := (Finset.mem_filter.mp hs2).2 ⟨0, by omega⟩
    simp only [show Even (0 : ℕ) from ⟨0, rfl⟩, ↓reduceIte] at h1 h2
    exact hne (Option.some.inj (h1.symm.trans h2))
  have hunion : Finset.univ.filter (fun s : Fin 2 → Fin (m + 1) → Fin 6 => isValidStrip (m + 1) s) =
      Finset.univ.biUnion S := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, S]
    constructor
    · intro hs
      have h01 : (⟨0, by omega⟩ : Fin (m + 1)).1 + 1 < m + 1 := by simp; omega
      obtain ⟨c0, hc0, _⟩ := (valid2x2_iff_comp (s 0 ⟨0, by omega⟩, s 1 ⟨0, by omega⟩)
        (s 0 ⟨1, by omega⟩, s 1 ⟨1, by omega⟩)).mp (hs ⟨0, by omega⟩ h01)
      refine ⟨c0, fun j => ?_⟩
      induction j using Fin.inductionOn with
      | zero => simpa using hc0
      | succ j ih =>
        have htrans := (valid2x2_iff_comp (s 0 j.castSucc, s 1 j.castSucc)
          (s 0 j.succ, s 1 j.succ)).mp (hs j.castSucc j.succ.2)
        rcases htrans with ⟨c', hc', hnext⟩
        have hceq : c' = if Even j.1 then c0 else partner c0 :=
          Option.some.inj (hc'.symm.trans ih)
        rw [hceq] at hnext
        have hval : (j.succ : ℕ) = j.1 + 1 := Fin.val_succ j
        rw [hval]
        by_cases hev : Even j.1
        · have hev' : ¬ Even (j.1 + 1) := by simpa [Nat.even_add_one] using hev
          rw [if_pos hev] at hnext
          rw [if_neg hev']
          exact hnext
        · have hev' : Even (j.1 + 1) := by simpa [Nat.even_add_one] using hev
          rw [if_neg hev, partner_partner] at hnext
          rw [if_pos hev']
          exact hnext
    · rintro ⟨c, hc⟩ j hj
      rw [valid2x2_iff_comp (s 0 j, s 1 j) (s 0 ⟨j.1 + 1, hj⟩, s 1 ⟨j.1 + 1, hj⟩)]
      have h1 := hc j
      have h2 := hc ⟨j.1 + 1, hj⟩
      dsimp only at h1 h2
      by_cases hev : Even j.1
      · have hev' : ¬ Even (j.1 + 1) := by simpa [Nat.even_add_one] using hev
        rw [if_pos hev] at h1
        rw [if_neg hev'] at h2
        exact ⟨c, h1, h2⟩
      · have hev' : Even (j.1 + 1) := by simpa [Nat.even_add_one] using hev
        rw [if_neg hev] at h1
        rw [if_pos hev'] at h2
        rw [← partner_partner c] at h2
        exact ⟨partner c, h1, h2⟩
  rw [hunion, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hbij : (S c).card = Fintype.card
      (∀ j : Fin (m + 1),
        {p : Fin 6 × Fin 6 // compOfCol p = some (if Even j.1 then c else partner c)}) := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ?_
    refine
      { toFun := fun s j => ⟨(s.1 0 j, s.1 1 j), (Finset.mem_filter.mp s.2).2 j⟩
        invFun := fun f => ⟨fun i j => if i = 0 then (f j).1.1 else (f j).1.2,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => by
            simpa using (f j).2⟩⟩
        left_inv := fun s => by
          apply Subtype.ext
          funext i j
          fin_cases i <;> rfl
        right_inv := fun f => by
          funext j
          apply Subtype.ext
          rfl }
  rw [hbij, Fintype.card_pi]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Fintype.card_subtype]
  split_ifs <;> exact comp_card _

private lemma prod_even_odd_two_mul (k a b : ℕ) :
    (∏ j : Fin (2 * k), if Even j.1 then a else b) = (a * b) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    let e : Fin (2 * (k + 1)) ≃ Fin ((2 * k + 1) + 1) := finCongr (by omega)
    rw [← Equiv.prod_comp e.symm]
    have heq : ∀ j : Fin ((2 * k + 1) + 1), (e.symm j).1 = j.1 := fun j => rfl
    simp_rw [heq]
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    have h0 : Even (2 * k) := ⟨k, by omega⟩
    have h1 : ¬ Even (2 * k + 1) := by intro ⟨m, hm⟩; omega
    rw [if_pos h0, if_neg h1]
    ring

private lemma prod_even_odd_two_mul_add_one (k a b : ℕ) :
    (∏ j : Fin (2 * k + 1), if Even j.1 then a else b) = a * (a * b) ^ k := by
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [prod_even_odd_two_mul]
  have hlast : Even (2 * k) := ⟨k, by omega⟩
  rw [if_pos hlast]
  ring

private lemma card_validStrips_even {k : ℕ} (hk : 1 ≤ k) :
    (Finset.univ.filter (fun s : Fin 2 → Fin (2 * k) → Fin 6 => isValidStrip (2 * k) s)).card =
      6 * 4 ^ k + 2 * 2 ^ k := by
  rw [card_validStrips (by omega)]
  simp only [prod_even_odd_two_mul, Fin.sum_univ_eight]
  norm_num [compSize, partner]
  ring

private lemma card_validStrips_odd {k : ℕ} (hk : 1 ≤ k) :
    (Finset.univ.filter
        (fun s : Fin 2 → Fin (2 * k + 1) → Fin 6 => isValidStrip (2 * k + 1) s)).card =
      13 * 4 ^ k + 3 * 2 ^ k := by
  rw [card_validStrips (by omega)]
  simp only [prod_even_odd_two_mul_add_one, Fin.sum_univ_eight]
  norm_num [compSize, partner]
  ring

private lemma card_rowPer2 {n : ℕ} (hn : 2 ≤ n) :
    ((Finset.univ.filter (fun g : Fin n → Fin n → Fin 6 => isValid6 n g)).filter rowPer2).card =
      (Finset.univ.filter (fun s : Fin 2 → Fin n → Fin 6 => isValidStrip n s)).card := by
  refine Finset.card_bij
    (fun g _ i j => g ⟨i.1, by omega⟩ j)
    ?_ ?_ ?_
  · intro g hg
    rw [Finset.mem_filter, Finset.mem_filter] at hg
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun j hj => ?_⟩
    have h01 : (⟨0, by omega⟩ : Fin n).1 + 1 < n := by simp; omega
    exact hg.1.2 ⟨0, by omega⟩ j h01 hj
  · intro g1 hg1 g2 hg2 h12
    have h1 := (Finset.mem_filter.mp hg1).2
    have h2 := (Finset.mem_filter.mp hg2).2
    have hmod : ∀ g : Fin n → Fin n → Fin 6, rowPer2 g →
        ∀ (m : ℕ) (hm : m < n) (j : Fin n), g ⟨m, hm⟩ j = g ⟨m % 2, by omega⟩ j := by
      intro g hr m
      induction m using Nat.strong_induction_on with
      | h m ihm =>
        intro hm j
        by_cases hm2 : m < 2
        · have : m % 2 = m := Nat.mod_eq_of_lt hm2
          simp [this]
        · have hm2lt : (⟨m - 2, by omega⟩ : Fin n).1 + 2 < n := by dsimp; omega
          have hstep := hr ⟨m - 2, by omega⟩ hm2lt j
          have hfin : (⟨m - 2 + 2, hm2lt⟩ : Fin n) = ⟨m, hm⟩ := Fin.ext (by dsimp; omega)
          dsimp only at hstep
          rw [hfin] at hstep
          rw [hstep, ihm (m - 2) (by omega) (by omega) j]
          have : (m - 2) % 2 = m % 2 := by omega
          simp [this]
    funext i j
    rw [hmod g1 h1 i.1 i.2 j, hmod g2 h2 i.1 i.2 j]
    have h0 : g1 ⟨0, by omega⟩ j = g2 ⟨0, by omega⟩ j := congr_fun (congr_fun h12 0) j
    have h1' : g1 ⟨1, by omega⟩ j = g2 ⟨1, by omega⟩ j := congr_fun (congr_fun h12 1) j
    rcases Nat.mod_two_eq_zero_or_one i.1 with hm0 | hm1
    · simpa [hm0] using h0
    · simpa [hm1] using h1'
  · intro s hs
    rw [Finset.mem_filter] at hs
    let g : Fin n → Fin n → Fin 6 := fun i j => s ⟨i.1 % 2, Nat.mod_lt _ (by decide)⟩ j
    refine ⟨g, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, fun i j hi hj => ?_⟩, fun i hi j => ?_⟩
      · have hstrip := hs.2 j hj
        rcases Nat.mod_two_eq_zero_or_one i.1 with hm0 | hm1
        · have hm' : (i.1 + 1) % 2 = 1 := by omega
          simpa [g, hm0, hm'] using hstrip
        · have hm' : (i.1 + 1) % 2 = 0 := by omega
          simpa [g, hm1, hm'] using valid2x2_symm_col hstrip
      · have hmod : (i.1 + 2) % 2 = i.1 % 2 := by omega
        simp [g, hmod]
    · funext i j
      fin_cases i <;> simp [g]

private lemma card_colPer2_eq_rowPer2 (n : ℕ) :
    ((Finset.univ.filter (fun g : Fin n → Fin n → Fin 6 => isValid6 n g)).filter colPer2).card =
      ((Finset.univ.filter (fun g : Fin n → Fin n → Fin 6 => isValid6 n g)).filter rowPer2).card := by
  refine Finset.card_bij (fun g _ i j => g j i) ?_ ?_ ?_
  · intro g hg
    rw [Finset.mem_filter, Finset.mem_filter] at hg ⊢
    rcases hg with ⟨⟨_, hgv⟩, hgc⟩
    refine ⟨⟨Finset.mem_univ _, fun i j hi hj => ?_⟩, fun i hi j => ?_⟩
    · exact valid2x2_symm_transpose (hgv j i hj hi)
    · exact hgc j i hi
  · intro g1 _ g2 _ h12
    funext i j
    exact congr_fun (congr_fun h12 j) i
  · intro g hg
    rw [Finset.mem_filter, Finset.mem_filter] at hg
    rcases hg with ⟨⟨_, hgv⟩, hgr⟩
    refine ⟨fun i j => g j i, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, fun i j hi hj => ?_⟩, fun i j hj => ?_⟩
      · exact valid2x2_symm_transpose (hgv j i hj hi)
      · exact hgr j hj i
    · funext i j; rfl

private lemma card_inter_row_col {n : ℕ} (hn : 2 ≤ n) :
    (((Finset.univ.filter (fun g : Fin n → Fin n → Fin 6 => isValid6 n g)).filter rowPer2) ∩
      ((Finset.univ.filter (fun g : Fin n → Fin n → Fin 6 => isValid6 n g)).filter colPer2)).card =
      28 := by
  rw [← valid2x2_card]
  refine Finset.card_bij
    (fun g _ => (g ⟨0, by omega⟩ ⟨0, by omega⟩, g ⟨0, by omega⟩ ⟨1, by omega⟩,
      g ⟨1, by omega⟩ ⟨0, by omega⟩, g ⟨1, by omega⟩ ⟨1, by omega⟩))
    ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    rw [Finset.mem_filter]
    have h01 : (⟨0, by omega⟩ : Fin n).1 + 1 < n := by simp; omega
    exact ⟨Finset.mem_univ _, hg.1.1 ⟨0, by omega⟩ ⟨0, by omega⟩ h01 h01⟩
  · intro g1 hg1 g2 hg2 h12
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hg1 hg2
    have hmod_r : ∀ g : Fin n → Fin n → Fin 6, rowPer2 g →
        ∀ (m : ℕ) (hm : m < n) (j : Fin n), g ⟨m, hm⟩ j = g ⟨m % 2, by omega⟩ j := by
      intro g hr m
      induction m using Nat.strong_induction_on with
      | h m ihm =>
        intro hm j
        by_cases hm2 : m < 2
        · have : m % 2 = m := Nat.mod_eq_of_lt hm2; simp [this]
        · have hm2lt : (⟨m - 2, by omega⟩ : Fin n).1 + 2 < n := by dsimp; omega
          have hstep := hr ⟨m - 2, by omega⟩ hm2lt j
          have hfin : (⟨m - 2 + 2, hm2lt⟩ : Fin n) = ⟨m, hm⟩ := Fin.ext (by dsimp; omega)
          dsimp only at hstep
          rw [hfin] at hstep
          rw [hstep, ihm (m - 2) (by omega) (by omega) j]
          have : (m - 2) % 2 = m % 2 := by omega
          simp [this]
    have hmod_c : ∀ g : Fin n → Fin n → Fin 6, colPer2 g →
        ∀ (i : Fin n) (m : ℕ) (hm : m < n), g i ⟨m, hm⟩ = g i ⟨m % 2, by omega⟩ := by
      intro g hc i m
      induction m using Nat.strong_induction_on with
      | h m ihm =>
        intro hm
        by_cases hm2 : m < 2
        · have : m % 2 = m := Nat.mod_eq_of_lt hm2; simp [this]
        · have hm2lt : (⟨m - 2, by omega⟩ : Fin n).1 + 2 < n := by dsimp; omega
          have hstep := hc i ⟨m - 2, by omega⟩ hm2lt
          have hfin : (⟨m - 2 + 2, hm2lt⟩ : Fin n) = ⟨m, hm⟩ := Fin.ext (by dsimp; omega)
          dsimp only at hstep
          rw [hfin] at hstep
          rw [hstep, ihm (m - 2) (by omega) (by omega)]
          have : (m - 2) % 2 = m % 2 := by omega
          simp [this]
    have h00 : g1 ⟨0, by omega⟩ ⟨0, by omega⟩ = g2 ⟨0, by omega⟩ ⟨0, by omega⟩ :=
      congrArg Prod.fst h12
    have h01 : g1 ⟨0, by omega⟩ ⟨1, by omega⟩ = g2 ⟨0, by omega⟩ ⟨1, by omega⟩ :=
      congrArg (Prod.fst ∘ Prod.snd) h12
    have h10 : g1 ⟨1, by omega⟩ ⟨0, by omega⟩ = g2 ⟨1, by omega⟩ ⟨0, by omega⟩ :=
      congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) h12
    have h11 : g1 ⟨1, by omega⟩ ⟨1, by omega⟩ = g2 ⟨1, by omega⟩ ⟨1, by omega⟩ :=
      congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) h12
    funext i j
    rw [hmod_r g1 hg1.1.2 i.1 i.2 j, hmod_c g1 hg1.2.2 ⟨i.1 % 2, by omega⟩ j.1 j.2,
      hmod_r g2 hg2.1.2 i.1 i.2 j, hmod_c g2 hg2.2.2 ⟨i.1 % 2, by omega⟩ j.1 j.2]
    rcases Nat.mod_two_eq_zero_or_one i.1 with hi | hi <;>
      rcases Nat.mod_two_eq_zero_or_one j.1 with hj | hj <;>
      simp [hi, hj, h00, h01, h10, h11]
  · intro b hb
    rw [Finset.mem_filter] at hb
    let g : Fin n → Fin n → Fin 6 := fun i j =>
      if i.1 % 2 = 0 then (if j.1 % 2 = 0 then b.1 else b.2.1)
      else (if j.1 % 2 = 0 then b.2.2.1 else b.2.2.2)
    refine ⟨g, ?_, ?_⟩
    · simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨fun i j hi hj => ?_, fun i hi j => ?_⟩,
        ⟨fun i j hi hj => ?_, fun i j hj => ?_⟩⟩
      · rcases Nat.mod_two_eq_zero_or_one i.1 with hi0 | hi1
        · rcases Nat.mod_two_eq_zero_or_one j.1 with hj0 | hj1
          · have hi' : (i.1 + 1) % 2 = 1 := by omega
            have hj' : (j.1 + 1) % 2 = 1 := by omega
            simpa [g, hi0, hj0, hi', hj'] using hb.2
          · have hi' : (i.1 + 1) % 2 = 1 := by omega
            have hj' : (j.1 + 1) % 2 = 0 := by omega
            simpa [g, hi0, hj1, hi', hj'] using valid2x2_symm_row hb.2
        · rcases Nat.mod_two_eq_zero_or_one j.1 with hj0 | hj1
          · have hi' : (i.1 + 1) % 2 = 0 := by omega
            have hj' : (j.1 + 1) % 2 = 1 := by omega
            simpa [g, hi1, hj0, hi', hj'] using valid2x2_symm_col hb.2
          · have hi' : (i.1 + 1) % 2 = 0 := by omega
            have hj' : (j.1 + 1) % 2 = 0 := by omega
            simpa [g, hi1, hj1, hi', hj'] using valid2x2_symm_row (valid2x2_symm_col hb.2)
      · have hmod : (i.1 + 2) % 2 = i.1 % 2 := by omega
        simp [g, hmod]
      · rcases Nat.mod_two_eq_zero_or_one i.1 with hi0 | hi1
        · rcases Nat.mod_two_eq_zero_or_one j.1 with hj0 | hj1
          · have hi' : (i.1 + 1) % 2 = 1 := by omega
            have hj' : (j.1 + 1) % 2 = 1 := by omega
            simpa [g, hi0, hj0, hi', hj'] using hb.2
          · have hi' : (i.1 + 1) % 2 = 1 := by omega
            have hj' : (j.1 + 1) % 2 = 0 := by omega
            simpa [g, hi0, hj1, hi', hj'] using valid2x2_symm_row hb.2
        · rcases Nat.mod_two_eq_zero_or_one j.1 with hj0 | hj1
          · have hi' : (i.1 + 1) % 2 = 0 := by omega
            have hj' : (j.1 + 1) % 2 = 1 := by omega
            simpa [g, hi1, hj0, hi', hj'] using valid2x2_symm_col hb.2
          · have hi' : (i.1 + 1) % 2 = 0 := by omega
            have hj' : (j.1 + 1) % 2 = 0 := by omega
            simpa [g, hi1, hj1, hi', hj'] using valid2x2_symm_row (valid2x2_symm_col hb.2)
      · have hmod : (j.1 + 2) % 2 = j.1 % 2 := by omega
        simp [g, hmod]
    · simp [g]

private lemma total_eq_two_mul_strips {n : ℕ} (hn : 2 ≤ n) :
    OMA.S_oeis_a159227.total n + 28 =
      2 * (Finset.univ.filter (fun s : Fin 2 → Fin n → Fin 6 => isValidStrip n s)).card := by
  rw [total_eq_card_valid6]
  let V := Finset.univ.filter (fun g : Fin n → Fin n → Fin 6 => isValid6 n g)
  let R := V.filter rowPer2
  let C := V.filter colPer2
  have hunion : V = R ∪ C := by
    ext g
    simp only [Finset.mem_union, Finset.mem_filter, V, R, C]
    constructor
    · intro hg
      rcases lt_or_ge n 3 with hn2 | hn3
      · left
        refine ⟨hg, fun i hi j => ?_⟩
        omega
      · rcases valid6_dichotomy hn3 hg.2 with hr | hc
        · exact Or.inl ⟨hg, hr⟩
        · exact Or.inr ⟨hg, hc⟩
    · rintro (⟨hg, _⟩ | ⟨hg, _⟩) <;> exact hg
  have hcard := Finset.card_union_add_card_inter R C
  rw [← hunion] at hcard
  have hinter : (R ∩ C).card = 28 := card_inter_row_col hn
  have hcol : C.card = R.card := card_colPer2_eq_rowPer2 n
  have hrow : R.card =
      (Finset.univ.filter (fun s : Fin 2 → Fin n → Fin 6 => isValidStrip n s)).card :=
    card_rowPer2 hn
  dsimp only [V, R, C] at hcard hinter hcol hrow
  omega

private lemma a_even {k : ℕ} (hk : 1 ≤ k) :
    (OMA.S_oeis_a159227.a (2 * k) : ℚ) = 3 * 4 ^ k + 2 ^ k - 7 := by
  have h2 : 2 * k ≥ 2 := by omega
  have ha : OMA.S_oeis_a159227.a (2 * k) = OMA.S_oeis_a159227.total (2 * k) / 4 := by
    cases h2k : 2 * k with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' => rfl
  have htot := total_eq_two_mul_strips h2
  rw [card_validStrips_even hk] at htot
  have hdiv : OMA.S_oeis_a159227.total (2 * k) = 4 * (3 * 4 ^ k + 2 ^ k - 7) := by
    have hpow : 4 ^ k ≥ 4 := by
      calc
        4 ^ k ≥ 4 ^ 1 := Nat.pow_le_pow_right (by decide) hk
        _ = 4 := by norm_num
    omega
  rw [ha, hdiv, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
  have hle : 7 ≤ 3 * 4 ^ k + 2 ^ k := by
    have : 4 ^ k ≥ 4 := by
      calc
        4 ^ k ≥ 4 ^ 1 := Nat.pow_le_pow_right (by decide) hk
        _ = 4 := by norm_num
    omega
  rw [Nat.cast_sub hle]
  push_cast
  ring

private lemma a_odd {k : ℕ} (hk : 1 ≤ k) :
    (OMA.S_oeis_a159227.a (2 * k + 1) : ℚ) = 26 * 4 ^ (k - 1) + 3 * 2 ^ (k - 1) - 7 := by
  have h2 : 2 * k + 1 ≥ 2 := by omega
  have ha : OMA.S_oeis_a159227.a (2 * k + 1) = OMA.S_oeis_a159227.total (2 * k + 1) / 4 := by
    cases h2k : 2 * k + 1 with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' => rfl
  have htot := total_eq_two_mul_strips h2
  rw [card_validStrips_odd hk] at htot
  have h4 : 4 ^ k = 4 * 4 ^ (k - 1) := by
    rw [← pow_succ', show k - 1 + 1 = k by omega]
  have h2p : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ', show k - 1 + 1 = k by omega]
  rw [h4, h2p] at htot
  have hdiv : OMA.S_oeis_a159227.total (2 * k + 1) = 4 * (26 * 4 ^ (k - 1) + 3 * 2 ^ (k - 1) - 7) := by
    have hge : 1 ≤ 4 ^ (k - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  rw [ha, hdiv, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
  have hle : 7 ≤ 26 * 4 ^ (k - 1) + 3 * 2 ^ (k - 1) := by
    have : 1 ≤ 4 ^ (k - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  rw [Nat.cast_sub hle]
  push_cast
  ring

end ProofHelpers

theorem OMA.solution : type_of% @OMA.S_oeis_a159227.main := by
  have hpoly :
      ((PowerSeries.X - 1) * (2 * PowerSeries.X + 1) * (2 * PowerSeries.X - 1) *
          (2 * PowerSeries.X ^ 2 - 1) : PowerSeries ℚ) =
        PowerSeries.C 8 * PowerSeries.X ^ 5 + PowerSeries.C (-8) * PowerSeries.X ^ 4 +
          PowerSeries.C (-6) * PowerSeries.X ^ 3 + PowerSeries.C 6 * PowerSeries.X ^ 2 +
          PowerSeries.C 1 * PowerSeries.X ^ 1 + PowerSeries.C (-1) * PowerSeries.X ^ 0 := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  have hrhs :
      PowerSeries.X ^ 2 * (-7 - 8 * PowerSeries.X ^ 4 + 32 * PowerSeries.X ^ 3 +
          19 * PowerSeries.X ^ 2 - 15 * PowerSeries.X : PowerSeries ℚ) =
        PowerSeries.C (-8) * PowerSeries.X ^ 6 + PowerSeries.C 32 * PowerSeries.X ^ 5 +
          PowerSeries.C 19 * PowerSeries.X ^ 4 + PowerSeries.C (-15) * PowerSeries.X ^ 3 +
          PowerSeries.C (-7) * PowerSeries.X ^ 2 := by
    simp only [map_neg, map_ofNat]
    ring
  rw [hpoly, hrhs]
  ext n
  simp only [mul_add, map_add]
  have hterm : ∀ (c : ℚ) (d : ℕ),
      PowerSeries.coeff n
          ((PowerSeries.mk fun m => (OMA.S_oeis_a159227.a m : ℚ)) * (PowerSeries.C c * PowerSeries.X ^ d)) =
        if d ≤ n then c * (OMA.S_oeis_a159227.a (n - d) : ℚ) else 0 := by
    intro c d
    rw [← mul_assoc, mul_comm (PowerSeries.mk _) (PowerSeries.C c), mul_assoc,
      PowerSeries.coeff_C_mul, mul_comm (PowerSeries.mk _), PowerSeries.coeff_X_pow_mul']
    split_ifs with h
    · rw [PowerSeries.coeff_mk]
    · rw [mul_zero]
  simp only [hterm, PowerSeries.coeff_C_mul_X_pow]
  rcases lt_or_ge n 7 with hn | hn
  · have ha0 : OMA.S_oeis_a159227.a 0 = 0 := rfl
    have ha1 : OMA.S_oeis_a159227.a 1 = 0 := rfl
    have ha2 : (OMA.S_oeis_a159227.a 2 : ℚ) = 7 := by
      have h := a_even (k := 1) (by decide)
      rw [show (2 * 1 : ℕ) = 2 from rfl] at h
      exact h.trans (by norm_num)
    have ha3 : (OMA.S_oeis_a159227.a 3 : ℚ) = 22 := by
      have h := a_odd (k := 1) (by decide)
      rw [show (2 * 1 + 1 : ℕ) = 3 from rfl] at h
      exact h.trans (by norm_num)
    have ha4 : (OMA.S_oeis_a159227.a 4 : ℚ) = 45 := by
      have h := a_even (k := 2) (by decide)
      rw [show (2 * 2 : ℕ) = 4 from rfl] at h
      exact h.trans (by norm_num)
    have ha5 : (OMA.S_oeis_a159227.a 5 : ℚ) = 103 := by
      have h := a_odd (k := 2) (by decide)
      rw [show (2 * 2 + 1 : ℕ) = 5 from rfl] at h
      exact h.trans (by norm_num)
    have ha6 : (OMA.S_oeis_a159227.a 6 : ℚ) = 193 := by
      have h := a_even (k := 3) (by decide)
      rw [show (2 * 3 : ℕ) = 6 from rfl] at h
      exact h.trans (by norm_num)
    interval_cases n <;>
      simp only [Nat.reduceLeDiff, Nat.zero_le, ↓reduceIte, Nat.reduceSub, Nat.sub_self,
        Nat.reduceEqDiff, ha0, ha1, ha2, ha3, ha4, ha5, ha6, Nat.cast_zero] <;>
      norm_num
  · have hge5 : 5 ≤ n := by omega
    have hge4 : 4 ≤ n := by omega
    have hge3 : 3 ≤ n := by omega
    have hge2 : 2 ≤ n := by omega
    have hge1 : 1 ≤ n := by omega
    have hge0 : 0 ≤ n := by omega
    have hne6 : n ≠ 6 := by omega
    have hne5 : n ≠ 5 := by omega
    have hne4 : n ≠ 4 := by omega
    have hne3 : n ≠ 3 := by omega
    have hne2 : n ≠ 2 := by omega
    simp only [hge5, hge4, hge3, hge2, hge1, hge0, hne6, hne5, hne4, hne3, hne2, ↓reduceIte]
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hk4 : 4 ≤ k := by omega
      have hn0 : n - 0 = 2 * k := by omega
      have hn1 : n - 1 = 2 * (k - 1) + 1 := by omega
      have hn2 : n - 2 = 2 * (k - 1) := by omega
      have hn3 : n - 3 = 2 * (k - 2) + 1 := by omega
      have hn4 : n - 4 = 2 * (k - 2) := by omega
      have hn5 : n - 5 = 2 * (k - 3) + 1 := by omega
      rw [hn0, hn1, hn2, hn3, hn4, hn5,
        a_even (by omega), a_odd (by omega), a_even (by omega),
        a_odd (by omega), a_even (by omega), a_odd (by omega)]
      have h4k : (4 : ℚ) ^ k = 16 * 4 ^ (k - 2) := by
        conv_lhs => rw [show k = (k - 2) + 2 by omega, pow_add]
        ring
      have h4k1 : (4 : ℚ) ^ (k - 1) = 4 * 4 ^ (k - 2) := by
        conv_lhs => rw [show k - 1 = (k - 2) + 1 by omega, pow_add]
        ring
      have h4k3 : (4 : ℚ) ^ (k - 2) = 16 * 4 ^ (k - 4) := by
        conv_lhs => rw [show k - 2 = (k - 4) + 2 by omega, pow_add]
        ring
      have h4k3' : (4 : ℚ) ^ (k - 3) = 4 * 4 ^ (k - 4) := by
        conv_lhs => rw [show k - 3 = (k - 4) + 1 by omega, pow_add]
        ring
      have h2k : (2 : ℚ) ^ k = 4 * 2 ^ (k - 2) := by
        conv_lhs => rw [show k = (k - 2) + 2 by omega, pow_add]
        ring
      have h2k1 : (2 : ℚ) ^ (k - 1) = 2 * 2 ^ (k - 2) := by
        conv_lhs => rw [show k - 1 = (k - 2) + 1 by omega, pow_add]
        ring
      have h2k3 : (2 : ℚ) ^ (k - 2) = 4 * 2 ^ (k - 4) := by
        conv_lhs => rw [show k - 2 = (k - 4) + 2 by omega, pow_add]
        ring
      have h2k3' : (2 : ℚ) ^ (k - 3) = 2 * 2 ^ (k - 4) := by
        conv_lhs => rw [show k - 3 = (k - 4) + 1 by omega, pow_add]
        ring
      rw [show k - 1 - 1 = k - 2 by omega, show k - 2 - 1 = k - 3 by omega,
        show k - 3 - 1 = k - 4 by omega]
      rw [h4k, h4k1, h4k3', h4k3, h2k, h2k1, h2k3', h2k3]
      ring
    · have hk3 : 3 ≤ k := by omega
      have hn0 : n - 0 = 2 * k + 1 := by omega
      have hn1 : n - 1 = 2 * k := by omega
      have hn2 : n - 2 = 2 * (k - 1) + 1 := by omega
      have hn3 : n - 3 = 2 * (k - 1) := by omega
      have hn4 : n - 4 = 2 * (k - 2) + 1 := by omega
      have hn5 : n - 5 = 2 * (k - 2) := by omega
      rw [hn0, hn1, hn2, hn3, hn4, hn5,
        a_odd (by omega), a_even (by omega), a_odd (by omega),
        a_even (by omega), a_odd (by omega), a_even (by omega)]
      have h4k : (4 : ℚ) ^ k = 16 * 4 ^ (k - 2) := by
        conv_lhs => rw [show k = (k - 2) + 2 by omega, pow_add]
        ring
      have h4k1 : (4 : ℚ) ^ (k - 1) = 4 * 4 ^ (k - 2) := by
        conv_lhs => rw [show k - 1 = (k - 2) + 1 by omega, pow_add]
        ring
      have h4k2 : (4 : ℚ) ^ (k - 2) = 4 * 4 ^ (k - 3) := by
        conv_lhs => rw [show k - 2 = (k - 3) + 1 by omega, pow_add]
        ring
      have h2k : (2 : ℚ) ^ k = 4 * 2 ^ (k - 2) := by
        conv_lhs => rw [show k = (k - 2) + 2 by omega, pow_add]
        ring
      have h2k1 : (2 : ℚ) ^ (k - 1) = 2 * 2 ^ (k - 2) := by
        conv_lhs => rw [show k - 1 = (k - 2) + 1 by omega, pow_add]
        ring
      have h2k2 : (2 : ℚ) ^ (k - 2) = 2 * 2 ^ (k - 3) := by
        conv_lhs => rw [show k - 2 = (k - 3) + 1 by omega, pow_add]
        ring
      rw [show k - 1 - 1 = k - 2 by omega, show k - 2 - 1 = k - 3 by omega]
      rw [h4k, h4k1, h4k2, h2k, h2k1, h2k2]
      ring
