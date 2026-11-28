import OMAStatements.S_oeis_a214353

/-!
OEIS A214353 (R. H. Hardin, Jul 13 2012): Number of 3 X 3 X 3 triangular 0..n arrays with no element lying outside the (possibly reversed) range delimited by its sw and se neighbors.
Conjectures from Colin Barker, Jul 22 2018: G.f.: x*(26 - 13*x + 23*x^2 - 30*x^3 + 20*x^4 - 7*x^5 + x^6) / (1 - x)^7. a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.

Proof. The condition only compares entries, so it holds for an array exactly when it holds for the
surjection onto Fin j that ranks its j distinct values (`rank_decomp`): a(n) = sum_j C(n + 1, j)
c_j, with c_j the number of valid surjections from the six cells onto Fin j. The condition splits
across the middle row (cells 1, 2), so the counts b_q over Fin q (q <= 6) are sums over the middle
row of products of counts for the top cell and for the bottom row (`sum_split`), checked in the
kernel; triangular elimination gives the c_j
(`c_vals`), and a(n) is an explicit polynomial of degree 6 (`a_poly`), from which the g.f. and the
recurrence follow by comparing coefficients.
-/

namespace OMA.S_oeis_a214353

open PowerSeries Finset


section engine

/-- The window condition: R holds on every three consecutive entries. -/
def Win (R : ℕ → ℕ → ℕ → Prop) {L : ℕ} (y : Fin L → ℕ) : Prop :=
  ∀ i j k : Fin L, j.val = i.val + 1 → k.val = i.val + 2 → R (y i) (y j) (y k)

instance instWin (R : ℕ → ℕ → ℕ → Prop) [∀ a b c, Decidable (R a b c)] {L : ℕ} :
    DecidablePred (Win R (L := L)) := fun y => by unfold Win; infer_instance

/-- An order embedding Fin j ↪o Fin N extended to a strictly increasing map of ℕ. -/
def ext {j N : ℕ} (e : Fin j ↪o Fin N) (k : ℕ) : ℕ := if h : k < j then (e ⟨k, h⟩ : ℕ) else N + k

lemma ext_mono {j N : ℕ} (e : Fin j ↪o Fin N) : StrictMono (ext e) := by
  intro x y hxy
  unfold ext
  split_ifs with hx hy hy
  · exact e.strictMono (show (⟨x, hx⟩ : Fin j) < ⟨y, hy⟩ from hxy)
  · have := (e ⟨x, hx⟩).isLt
    omega
  · omega
  · omega

lemma ext_apply {j N : ℕ} (e : Fin j ↪o Fin N) (r : Fin j) : ext e r = (e r : ℕ) := by
  unfold ext
  rw [dif_pos r.isLt]

/-- The arrays over Fin j that take every value and satisfy P. -/
def surjCount {L : ℕ} (P : (Fin L → ℕ) → Prop) [DecidablePred P] (j : ℕ) : ℕ :=
  ((univ : Finset (Fin L → Fin j)).filter
    (fun r : Fin L → Fin j => Function.Surjective r ∧ P (fun i => (r i : ℕ)))).card

lemma fiber_card {L : ℕ} (P : (Fin L → ℕ) → Prop) [DecidablePred P]
    (hP : ∀ f : ℕ → ℕ, StrictMono f → ∀ y : Fin L → ℕ, P (f ∘ y) ↔ P y)
    {N : ℕ} (S : Finset (Fin N)) :
    ((univ : Finset (Fin L → Fin N)).filter
      (fun x => P (fun i => (x i : ℕ)) ∧ univ.image x = S)).card = surjCount P S.card := by
  unfold surjCount
  symm
  set e := S.orderEmbOfFin rfl with he
  refine card_bij (fun r _ => fun i => e (r i)) ?_ ?_ ?_
  · intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    obtain ⟨hs, hp⟩ := hr
    refine ⟨?_, ?_⟩
    · have h := hP (ext e) (ext_mono e) (fun i => (r i : ℕ))
      have heq : (ext e ∘ fun i => (r i : ℕ)) = fun i => ((e (r i) : Fin N) : ℕ) := by
        funext i
        simp [ext_apply]
      rw [heq] at h
      exact h.mpr hp
    · ext y
      simp only [mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact S.orderEmbOfFin_mem rfl (r i)
      · intro hy
        have hy' : y ∈ Set.range e := by
          rw [he, S.range_orderEmbOfFin rfl]
          exact hy
        obtain ⟨k, rfl⟩ := hy'
        obtain ⟨i, hi⟩ := hs k
        exact ⟨i, by rw [hi]⟩
  · intro r1 _ r2 _ h
    funext i
    exact e.injective (congrFun h i)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨hp, himg⟩ := hx
    have hmem : ∀ i, x i ∈ S := fun i => by
      rw [← himg]
      exact mem_image_of_mem x (mem_univ i)
    set r : Fin L → Fin S.card := fun i => (S.orderIsoOfFin rfl).symm ⟨x i, hmem i⟩ with hr
    have hxr : ∀ i, e (r i) = x i := by
      intro i
      rw [he, ← S.coe_orderIsoOfFin_apply rfl, hr]
      simp
    refine ⟨r, ?_, funext hxr⟩
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · intro k
      have hk : e k ∈ univ.image x := by
        rw [himg]
        exact S.orderEmbOfFin_mem rfl k
      obtain ⟨i, -, hi⟩ := mem_image.mp hk
      exact ⟨i, e.injective (by rw [hxr, hi])⟩
    · have h := hP (ext e) (ext_mono e) (fun i => (r i : ℕ))
      have heq : (ext e ∘ fun i => (r i : ℕ)) = fun i => ((x i : Fin N) : ℕ) := by
        funext i
        simp [ext_apply, hxr]
      rw [heq] at h
      exact h.mp hp

/-- Counting arrays by their value sets: an array over Fin N is the increasing enumeration of a
j-element value set composed with a surjection onto Fin j. -/
theorem rank_decomp {L : ℕ} (P : (Fin L → ℕ) → Prop) [DecidablePred P]
    (hP : ∀ f : ℕ → ℕ, StrictMono f → ∀ y : Fin L → ℕ, P (f ∘ y) ↔ P y) (N : ℕ) :
    ((univ : Finset (Fin L → Fin N)).filter (fun x => P (fun i => (x i : ℕ)))).card =
      ∑ j ∈ range (L + 1), N.choose j * surjCount P j := by
  set T : Finset (Finset (Fin N)) := univ.filter (fun S => S.card ≤ L) with hT
  rw [card_eq_sum_card_fiberwise (f := fun x => univ.image x) (t := T)]
  · have hfib : ∀ S ∈ T, (((univ : Finset (Fin L → Fin N)).filter
        (fun x => P (fun i => (x i : ℕ)))).filter (fun x => univ.image x = S)).card =
          surjCount P S.card := fun S _ => by
      rw [filter_filter]
      exact fiber_card P hP S
    have hmaps : ∀ S ∈ T, S.card ∈ range (L + 1) := by
      intro S hS
      simp only [hT, mem_filter, mem_univ, true_and] at hS
      exact mem_range.mpr (Nat.lt_succ_of_le hS)
    rw [sum_congr rfl hfib, ← sum_fiberwise_of_maps_to hmaps (fun S => surjCount P S.card)]
    refine sum_congr rfl (fun j hj => ?_)
    have hc : ∀ S ∈ T.filter (fun S => S.card = j), surjCount P S.card = surjCount P j :=
      fun S hS => by rw [(mem_filter.mp hS).2]
    rw [sum_congr rfl hc, sum_const, smul_eq_mul]
    congr 1
    have hset : T.filter (fun S => S.card = j) = powersetCard j univ := by
      ext S
      simp only [hT, mem_filter, mem_univ, true_and, mem_powersetCard_univ]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · intro h
        exact ⟨by rw [h]; exact Nat.lt_succ_iff.mp (mem_range.mp hj), h⟩
    rw [hset, card_powersetCard, card_univ, Fintype.card_fin]
  · intro x _
    simp only [hT, coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    calc (univ.image x).card ≤ (univ : Finset (Fin L)).card := card_image_le
      _ = L := by simp

end engine
lemma choose_q (m j : ℕ) :
    ((m.choose j : ℕ) : ℚ) = (∏ i ∈ range j, ((m : ℚ) - i)) / (j.factorial : ℚ) := by
  rw [Nat.cast_choose_eq_descPochhammer_div, descPochhammer_eval_eq_prod_range]


/-- The condition on arrays of naturals. -/
def Rg (v a b : ℕ) : Prop := (a ≤ v ∧ v ≤ b) ∨ (b ≤ v ∧ v ≤ a)

/-- The condition on arrays of naturals. -/
def P (y : Fin 6 → ℕ) : Prop :=
  Rg (y 0) (y 1) (y 2) ∧ Rg (y 1) (y 3) (y 4) ∧ Rg (y 2) (y 4) (y 5)

instance instP : DecidablePred P := fun y => by unfold P Rg; infer_instance

lemma P_inv : ∀ f : ℕ → ℕ, StrictMono f → ∀ y : Fin 6 → ℕ, P (f ∘ y) ↔ P y := by
  intro f hf y
  simp only [P, Rg, Function.comp_apply, hf.le_iff_le]

lemma good_iff {N : ℕ} (x : Fin 6 → Fin N) : good x ↔ P (fun i => (x i : ℕ)) := by
  simp only [good, inRange, P, Rg, Fin.le_def]

/-- The part of the condition on the top two rows (cells 0, 1, 2). -/
def Pa (x0 x1 x2 : ℕ) : Prop := Rg x0 x1 x2

/-- The part of the condition that involves the bottom row (cells 3, 4, 5). -/
def Pb (x1 x2 x3 x4 x5 : ℕ) : Prop := Rg x1 x3 x4 ∧ Rg x2 x4 x5

instance (x0 x1 x2 : ℕ) : Decidable (Pa x0 x1 x2) := by unfold Pa Rg; infer_instance
instance (x1 x2 x3 x4 x5 : ℕ) : Decidable (Pb x1 x2 x3 x4 x5) := by unfold Pb Rg; infer_instance

lemma P_split (y : Fin 6 → ℕ) : P y ↔ Pa (y 0) (y 1) (y 2) ∧ Pb (y 1) (y 2) (y 3) (y 4) (y 5) := by
  unfold P Pa Pb
  tauto

/-- Top-part weight. -/
def wa (x0 x1 x2 : ℕ) : ℕ := if Pa x0 x1 x2 then 1 else 0

/-- Bottom-part weight. -/
def wb (x1 x2 x3 x4 x5 : ℕ) : ℕ := if Pb x1 x2 x3 x4 x5 then 1 else 0

lemma ind_P (y : Fin 6 → ℕ) :
    (if P y then 1 else 0) = wa (y 0) (y 1) (y 2) * wb (y 1) (y 2) (y 3) (y 4) (y 5) := by
  unfold wa wb
  by_cases ha : Pa (y 0) (y 1) (y 2) <;> by_cases hb : Pb (y 1) (y 2) (y 3) (y 4) (y 5) <;>
    simp [P_split, ha, hb]

/-- The tuple view of an array of six cells. -/
def tup (q : ℕ) : Fin q × Fin q × Fin q × Fin q × Fin q × Fin q ≃ (Fin 6 → Fin q) where
  toFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2]
  invFun x := (x 0, x 1, x 2, x 3, x 4, x 5)
  left_inv p := rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

/-- Summing a weight that factors through the middle row (cells 1, 2): the top cell and the
bottom row are then summed independently. -/
lemma sum_split (q : ℕ) (fa : ℕ → ℕ → ℕ → ℕ) (fb : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) :
    ∑ x : Fin 6 → Fin q, fa (x 0) (x 1) (x 2) * fb (x 1) (x 2) (x 3) (x 4) (x 5) =
      ∑ u : Fin q, ∑ v : Fin q, (∑ w : Fin q, fa w u v) *
        ∑ p : Fin q × Fin q × Fin q, fb u v p.1 p.2.1 p.2.2 := by
  rw [← (tup q).sum_comp]
  simp only [Fintype.sum_prod_type]
  show ∑ a0 : Fin q, ∑ a1 : Fin q, ∑ a2 : Fin q, ∑ a3 : Fin q, ∑ a4 : Fin q, ∑ a5 : Fin q,
      fa a0 a1 a2 * fb a1 a2 a3 a4 a5 = _
  rw [Finset.sum_comm]
  refine sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_comm]
  refine sum_congr rfl (fun v _ => ?_)
  rw [Finset.sum_mul]
  refine sum_congr rfl (fun w _ => ?_)
  rw [Finset.mul_sum]
  refine sum_congr rfl (fun s _ => ?_)
  rw [Finset.mul_sum]
  refine sum_congr rfl (fun t _ => ?_)
  rw [Finset.mul_sum]

/-- The count over Fin q. -/
def bc (q : ℕ) : ℕ := ((univ : Finset (Fin 6 → Fin q)).filter (fun x => P (fun i => (x i : ℕ)))).card

lemma b_split (q : ℕ) : bc q =
    (∑ u : Fin q, ∑ v : Fin q, (∑ w : Fin q, wa w u v) *
        ∑ p : Fin q × Fin q × Fin q, wb u v p.1 p.2.1 p.2.2) := by
  rw [bc, card_filter]
  simp only [ind_P]
  rw [sum_split q wa wb]

theorem check_all :
    (∑ u : Fin 1, ∑ v : Fin 1, (∑ w : Fin 1, wa w u v) *
        ∑ p : Fin 1 × Fin 1 × Fin 1, wb u v p.1 p.2.1 p.2.2) = 1 ∧
    (∑ u : Fin 2, ∑ v : Fin 2, (∑ w : Fin 2, wa w u v) *
        ∑ p : Fin 2 × Fin 2 × Fin 2, wb u v p.1 p.2.1 p.2.2) = 26 ∧
    (∑ u : Fin 3, ∑ v : Fin 3, (∑ w : Fin 3, wa w u v) *
        ∑ p : Fin 3 × Fin 3 × Fin 3, wb u v p.1 p.2.1 p.2.2) = 169 ∧
    (∑ u : Fin 4, ∑ v : Fin 4, (∑ w : Fin 4, wa w u v) *
        ∑ p : Fin 4 × Fin 4 × Fin 4, wb u v p.1 p.2.1 p.2.2) = 660 ∧
    (∑ u : Fin 5, ∑ v : Fin 5, (∑ w : Fin 5, wa w u v) *
        ∑ p : Fin 5 × Fin 5 × Fin 5, wb u v p.1 p.2.1 p.2.2) = 1951 ∧
    (∑ u : Fin 6, ∑ v : Fin 6, (∑ w : Fin 6, wa w u v) *
        ∑ p : Fin 6 × Fin 6 × Fin 6, wb u v p.1 p.2.1 p.2.2) = 4822 := by
  decide +kernel

/-- The triangular system for the c_j, over an arbitrary function (kept apart from surjCount, whose
values the kernel would otherwise compute when it compares terms). -/
lemma solve (s : ℕ → ℕ)
    (e0 : 0 = ∑ j ∈ range 7, (0 : ℕ).choose j * s j)
    (e1 : 1 = ∑ j ∈ range 7, (1 : ℕ).choose j * s j)
    (e2 : 26 = ∑ j ∈ range 7, (2 : ℕ).choose j * s j)
    (e3 : 169 = ∑ j ∈ range 7, (3 : ℕ).choose j * s j)
    (e4 : 660 = ∑ j ∈ range 7, (4 : ℕ).choose j * s j)
    (e5 : 1951 = ∑ j ∈ range 7, (5 : ℕ).choose j * s j)
    (e6 : 4822 = ∑ j ∈ range 7, (6 : ℕ).choose j * s j) :
    s 0 = 0 ∧ s 1 = 1 ∧ s 2 = 24 ∧ s 3 = 94 ∧ s 4 = 136 ∧ s 5 = 86 ∧ s 6 = 20 := by
  simp only [sum_range_succ, sum_range_zero, zero_add, one_mul, zero_mul, add_zero,
    show (0 : ℕ).choose 0 = 1 by decide, show (0 : ℕ).choose 1 = 0 by decide, show (0 : ℕ).choose 2 = 0 by decide, show (0 : ℕ).choose 3 = 0 by decide, show (0 : ℕ).choose 4 = 0 by decide, show (0 : ℕ).choose 5 = 0 by decide, show (0 : ℕ).choose 6 = 0 by decide,
    show (1 : ℕ).choose 0 = 1 by decide, show (1 : ℕ).choose 1 = 1 by decide, show (1 : ℕ).choose 2 = 0 by decide, show (1 : ℕ).choose 3 = 0 by decide, show (1 : ℕ).choose 4 = 0 by decide, show (1 : ℕ).choose 5 = 0 by decide, show (1 : ℕ).choose 6 = 0 by decide,
    show (2 : ℕ).choose 0 = 1 by decide, show (2 : ℕ).choose 1 = 2 by decide, show (2 : ℕ).choose 2 = 1 by decide, show (2 : ℕ).choose 3 = 0 by decide, show (2 : ℕ).choose 4 = 0 by decide, show (2 : ℕ).choose 5 = 0 by decide, show (2 : ℕ).choose 6 = 0 by decide,
    show (3 : ℕ).choose 0 = 1 by decide, show (3 : ℕ).choose 1 = 3 by decide, show (3 : ℕ).choose 2 = 3 by decide, show (3 : ℕ).choose 3 = 1 by decide, show (3 : ℕ).choose 4 = 0 by decide, show (3 : ℕ).choose 5 = 0 by decide, show (3 : ℕ).choose 6 = 0 by decide,
    show (4 : ℕ).choose 0 = 1 by decide, show (4 : ℕ).choose 1 = 4 by decide, show (4 : ℕ).choose 2 = 6 by decide, show (4 : ℕ).choose 3 = 4 by decide, show (4 : ℕ).choose 4 = 1 by decide, show (4 : ℕ).choose 5 = 0 by decide, show (4 : ℕ).choose 6 = 0 by decide,
    show (5 : ℕ).choose 0 = 1 by decide, show (5 : ℕ).choose 1 = 5 by decide, show (5 : ℕ).choose 2 = 10 by decide, show (5 : ℕ).choose 3 = 10 by decide, show (5 : ℕ).choose 4 = 5 by decide, show (5 : ℕ).choose 5 = 1 by decide, show (5 : ℕ).choose 6 = 0 by decide,
    show (6 : ℕ).choose 0 = 1 by decide, show (6 : ℕ).choose 1 = 6 by decide, show (6 : ℕ).choose 2 = 15 by decide, show (6 : ℕ).choose 3 = 20 by decide, show (6 : ℕ).choose 4 = 15 by decide, show (6 : ℕ).choose 5 = 6 by decide, show (6 : ℕ).choose 6 = 1 by decide] at e0 e1 e2 e3 e4 e5 e6
  omega

lemma c_vals : surjCount P 0 = 0 ∧ surjCount P 1 = 1 ∧ surjCount P 2 = 24 ∧ surjCount P 3 = 94 ∧ surjCount P 4 = 136 ∧ surjCount P 5 = 86 ∧ surjCount P 6 = 20 := by
  have hb1 : bc 1 = 1 := (b_split 1).trans check_all.1
  have hb2 : bc 2 = 26 := (b_split 2).trans check_all.2.1
  have hb3 : bc 3 = 169 := (b_split 3).trans check_all.2.2.1
  have hb4 : bc 4 = 660 := (b_split 4).trans check_all.2.2.2.1
  have hb5 : bc 5 = 1951 := (b_split 5).trans check_all.2.2.2.2.1
  have hb6 : bc 6 = 4822 := (b_split 6).trans check_all.2.2.2.2.2
  have e0 : bc 0 = ∑ j ∈ range 7, (0 : ℕ).choose j * surjCount P j :=
    rank_decomp P P_inv 0
  have e1 : bc 1 = ∑ j ∈ range 7, (1 : ℕ).choose j * surjCount P j :=
    rank_decomp P P_inv 1
  have e2 : bc 2 = ∑ j ∈ range 7, (2 : ℕ).choose j * surjCount P j :=
    rank_decomp P P_inv 2
  have e3 : bc 3 = ∑ j ∈ range 7, (3 : ℕ).choose j * surjCount P j :=
    rank_decomp P P_inv 3
  have e4 : bc 4 = ∑ j ∈ range 7, (4 : ℕ).choose j * surjCount P j :=
    rank_decomp P P_inv 4
  have e5 : bc 5 = ∑ j ∈ range 7, (5 : ℕ).choose j * surjCount P j :=
    rank_decomp P P_inv 5
  have e6 : bc 6 = ∑ j ∈ range 7, (6 : ℕ).choose j * surjCount P j :=
    rank_decomp P P_inv 6
  have hb0 : bc 0 = 0 := by
    rw [b_split]
    simp
  exact solve _ (hb0.symm.trans e0) (hb1.symm.trans e1) (hb2.symm.trans e2) (hb3.symm.trans e3) (hb4.symm.trans e4) (hb5.symm.trans e5) (hb6.symm.trans e6)

lemma a_sum (n : ℕ) : (a n : ℚ) = ∑ j ∈ range 7, (((n + 1).choose j : ℕ) : ℚ) *
    (surjCount P j : ℚ) := by
  have h := rank_decomp P P_inv (n + 1)
  have ha : a n = ((univ : Finset (Fin 6 → Fin (n + 1))).filter
      (fun x => P (fun i => (x i : ℕ)))).card := by
    unfold a
    exact congrArg Finset.card (filter_congr (fun x _ => good_iff x))
  rw [ha, h]
  simp only [Nat.cast_sum, Nat.cast_mul]

/-- a(n) as a polynomial in n. -/
lemma a_poly (n : ℕ) : (a n : ℚ) = 1 + (151 / 30) * (n : ℚ) + (331 / 36) * (n : ℚ) ^ 2 + (15 / 2) * (n : ℚ) ^ 3 + (25 / 9) * (n : ℚ) ^ 4 + (7 / 15) * (n : ℚ) ^ 5 + (1 / 36) * (n : ℚ) ^ 6 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := c_vals
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero, choose_q, prod_range_succ, prod_range_zero,
    c0, c1, c2, c3, c4, c5, c6, Nat.factorial]
  push_cast
  ring

/-- Barker's g.f. -/
theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (26 - 13 * X + 23 * X ^ 2 - 30 * X ^ 3 + 20 * X ^ 4 - 7 * X ^ 5 + X ^ 6) := by
  have v1 : (a 1 : ℚ) = 26 := by rw [a_poly]; norm_num
  have v2 : (a 2 : ℚ) = 169 := by rw [a_poly]; norm_num
  have v3 : (a 3 : ℚ) = 660 := by rw [a_poly]; norm_num
  have v4 : (a 4 : ℚ) = 1951 := by rw [a_poly]; norm_num
  have v5 : (a 5 : ℚ) = 4822 := by rw [a_poly]; norm_num
  have v6 : (a 6 : ℚ) = 10507 := by rw [a_poly]; norm_num
  have v7 : (a 7 : ℚ) = 20840 := by rw [a_poly]; norm_num
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 7 = A - C (7 : ℚ) * (A * X ^ 1) + C (21 : ℚ) * (A * X ^ 2) - C (35 : ℚ) * (A * X ^ 3) + C (35 : ℚ) * (A * X ^ 4) - C (21 : ℚ) * (A * X ^ 5) + C (7 : ℚ) * (A * X ^ 6) - A * X ^ 7 := by
    simp only [map_ofNat]
    ring
  have e2 : (X * (26 - 13 * X + 23 * X ^ 2 - 30 * X ^ 3 + 20 * X ^ 4 - 7 * X ^ 5 + X ^ 6) : ℚ⟦X⟧) = X ^ 1 * C (26 : ℚ) - X ^ 2 * C (13 : ℚ) + X ^ 3 * C (23 : ℚ) - X ^ 4 * C (30 : ℚ) + X ^ 5 * C (20 : ℚ) - X ^ 6 * C (7 : ℚ) + X ^ 7 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk,
    coeff_C_mul]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | m
  · simp
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1, v2]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1, v2, v3]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1, v2, v3, v4]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1, v2, v3, v4, v5]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1, v2, v3, v4, v5, v6]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1, v2, v3, v4, v5, v6, v7]
    all_goals norm_num
  · simp only [show ¬ (m + 8 = 0) by omega,
      show 1 ≤ m + 8 by omega,
      show m + 8 - 1 = m + 7 by omega,
      show ¬ (m + 7 = 0) by omega,
      show 2 ≤ m + 8 by omega,
      show m + 8 - 2 = m + 6 by omega,
      show ¬ (m + 6 = 0) by omega,
      show 3 ≤ m + 8 by omega,
      show m + 8 - 3 = m + 5 by omega,
      show ¬ (m + 5 = 0) by omega,
      show 4 ≤ m + 8 by omega,
      show m + 8 - 4 = m + 4 by omega,
      show ¬ (m + 4 = 0) by omega,
      show 5 ≤ m + 8 by omega,
      show m + 8 - 5 = m + 3 by omega,
      show ¬ (m + 3 = 0) by omega,
      show 6 ≤ m + 8 by omega,
      show m + 8 - 6 = m + 2 by omega,
      show ¬ (m + 2 = 0) by omega,
      show 7 ≤ m + 8 by omega,
      show m + 8 - 7 = m + 1 by omega,
      show ¬ (m + 1 = 0) by omega,
      show ¬ (m + 8 = 1) by omega,
      show ¬ (m + 8 = 2) by omega,
      show ¬ (m + 8 = 3) by omega,
      show ¬ (m + 8 = 4) by omega,
      show ¬ (m + 8 = 5) by omega,
      show ¬ (m + 8 = 6) by omega,
      show ¬ (m + 8 = 7) by omega, if_true, if_false]
    rw [a_poly (m + 8), a_poly (m + 7), a_poly (m + 6), a_poly (m + 5), a_poly (m + 4), a_poly (m + 3), a_poly (m + 2), a_poly (m + 1)]
    push_cast
    ring

/-- Barker's recurrence. -/
theorem recur : ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega, show m + 8 - 7 = m + 1 by omega]
  have h : (a (m + 8) : ℚ) = 7 * a (m + 7) - 21 * a (m + 6) + 35 * a (m + 5) - 35 * a (m + 4) + 21 * a (m + 3) - 7 * a (m + 2) + a (m + 1) := by
    rw [a_poly (m + 8), a_poly (m + 7), a_poly (m + 6), a_poly (m + 5), a_poly (m + 4), a_poly (m + 3), a_poly (m + 2), a_poly (m + 1)]
    push_cast
    ring
  exact_mod_cast h

/-- Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (26 - 13 * X + 23 * X ^ 2 - 30 * X ^ 3 + 20 * X ^ 4 - 7 * X ^ 5 + X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a214353

theorem OMA.solution : type_of% @OMA.S_oeis_a214353.main :=
  OMA.S_oeis_a214353.conjecture
