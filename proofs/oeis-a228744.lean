import OMAStatements.S_oeis_a228744

namespace OrderOnly

open Finset PowerSeries

variable {L : ℕ} (P : (Fin L → ℕ) → Prop) [DecidablePred P]

/-- The number of 0..n arrays x(0..L-1) with property P. -/
def count (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin L → Fin (n + 1) => P (fun i => (x i : ℕ)))).card

/-- The number of surjective patterns g : Fin L → Fin j with property P. -/
def pc (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun g : Fin L → Fin j => Function.Surjective g ∧ P (fun i => (g i : ℕ)))).card

/-- P is invariant under strictly monotone relabeling of the values. -/
def Invariant : Prop := ∀ f : ℕ → ℕ, StrictMono f → ∀ x : Fin L → ℕ, P (f ∘ x) ↔ P x

variable {P}

/-- An order embedding of Fin m into ℕ extends to a strictly monotone map of ℕ. -/
lemma extend (m : ℕ) (e : Fin m ↪o ℕ) : ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ i : Fin m, f i = e i := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨id, strictMono_id, fun i => i.elim0⟩
  · refine ⟨fun i => if h : i < m then e ⟨i, h⟩ else e ⟨m - 1, by omega⟩ + 1 + (i - m), ?_, ?_⟩
    · intro i j hij
      simp only
      by_cases hj : j < m
      · rw [dif_pos (lt_trans hij hj), dif_pos hj]
        exact e.strictMono (Fin.mk_lt_mk.2 hij)
      · rw [dif_neg hj]
        by_cases hi : i < m
        · rw [dif_pos hi]
          have : e ⟨i, hi⟩ ≤ e ⟨m - 1, by omega⟩ := e.monotone (Fin.mk_le_mk.2 (by omega))
          omega
        · rw [dif_neg hi]
          omega
    · intro i
      simp only [dif_pos i.isLt]

omit [DecidablePred P] in
/-- Invariance in the form used by the pattern count: relabeling a pattern by two order
embeddings does not change P. -/
lemma inv_emb (hP : Invariant P) (m : ℕ) (e₁ e₂ : Fin m ↪o ℕ) (g : Fin L → Fin m) :
    P (fun i => e₁ (g i)) ↔ P (fun i => e₂ (g i)) := by
  obtain ⟨f₁, hf₁, he₁⟩ := extend m e₁
  obtain ⟨f₂, hf₂, he₂⟩ := extend m e₂
  have h₁ : (fun i => e₁ (g i)) = f₁ ∘ (fun i => (g i : ℕ)) := funext fun i => (he₁ (g i)).symm
  have h₂ : (fun i => e₂ (g i)) = f₂ ∘ (fun i => (g i : ℕ)) := funext fun i => (he₂ (g i)).symm
  rw [h₁, h₂, hP f₁ hf₁, hP f₂ hf₂]

omit [DecidablePred P] in
/-- Conversely, invariance under relabeling patterns by order embeddings gives invariance under
strictly monotone maps: restrict the map to an initial segment that contains the values. -/
lemma inv_of_emb (h : ∀ (m : ℕ) (e₁ e₂ : Fin m ↪o ℕ) (g : Fin L → Fin m),
    P (fun i => e₁ (g i)) ↔ P (fun i => e₂ (g i))) : Invariant P := by
  intro f hf x
  obtain ⟨m, hm⟩ : ∃ m, ∀ i, x i < m :=
    ⟨Finset.univ.sup x + 1, fun i => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))⟩
  let e₁ : Fin m ↪o ℕ := OrderEmbedding.ofStrictMono (fun i => f i) (fun i j hij => hf hij)
  exact h m e₁ (Fin.valOrderEmb m) (fun i => ⟨x i, hm i⟩)

/-- The arrays with image S correspond to the surjective patterns onto Fin S.card. -/
theorem fiber_card (hP : Invariant P) {n : ℕ} (S : Finset (Fin (n + 1))) :
    ((Finset.univ.filter (fun x : Fin L → Fin (n + 1) => P (fun i => (x i : ℕ)))).filter
      (fun x => Finset.univ.image x = S)).card = pc P S.card := by
  symm
  unfold pc
  apply Finset.card_bij (fun g _ => fun i => S.orderEmbOfFin rfl (g i))
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨hs, hp⟩ := hg
    refine ⟨?_, ?_⟩
    · have h := inv_emb hP S.card ((S.orderEmbOfFin rfl).trans (Fin.valOrderEmb (n + 1)))
        (Fin.valOrderEmb S.card) g
      simp only [RelEmbedding.trans_apply, Fin.valOrderEmb_apply] at h
      exact h.2 hp
    · ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact Finset.orderEmbOfFin_mem S rfl (g i)
      · intro hy
        have hy' : y ∈ Set.range (S.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]
          exact hy
        obtain ⟨j, hj⟩ := hy'
        obtain ⟨i, hi⟩ := hs j
        exact ⟨i, by rw [hi, hj]⟩
  · intro g₁ _ g₂ _ h
    funext i
    exact (S.orderEmbOfFin rfl).injective (congrFun h i)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hp, himg⟩ := hx
    have hmem : ∀ i, x i ∈ S := fun i => by
      rw [← himg]
      exact Finset.mem_image_of_mem x (Finset.mem_univ i)
    have hx_eq : ∀ i, S.orderEmbOfFin rfl ((S.orderIsoOfFin rfl).symm ⟨x i, hmem i⟩) = x i := by
      intro i
      rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
    refine ⟨fun i => (S.orderIsoOfFin rfl).symm ⟨x i, hmem i⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · intro j
        have hj : S.orderEmbOfFin rfl j ∈ Finset.univ.image x := by
          rw [himg]
          exact Finset.orderEmbOfFin_mem S rfl j
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hj
        obtain ⟨i, hi⟩ := hj
        refine ⟨i, ?_⟩
        apply (S.orderEmbOfFin rfl).injective
        show S.orderEmbOfFin rfl ((S.orderIsoOfFin rfl).symm ⟨x i, hmem i⟩) = S.orderEmbOfFin rfl j
        rw [hx_eq]
        exact hi
      · have h := inv_emb hP S.card ((S.orderEmbOfFin rfl).trans (Fin.valOrderEmb (n + 1)))
          (Fin.valOrderEmb S.card) (fun i => (S.orderIsoOfFin rfl).symm ⟨x i, hmem i⟩)
        simp only [RelEmbedding.trans_apply, Fin.valOrderEmb_apply, hx_eq] at h
        exact h.1 hp
    · funext i
      exact hx_eq i

lemma pc_eq_zero (j : ℕ) (hj : L < j) : pc P j = 0 := by
  unfold pc
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro g - ⟨hs, -⟩
  have := Fintype.card_le_of_surjective g hs
  simp only [Fintype.card_fin] at this
  omega

/-- The count of arrays as a sum over the number of distinct values. -/
theorem count_eq (hP : Invariant P) (n : ℕ) :
    count P n = ∑ j ∈ Finset.range (L + 1), (n + 1).choose j * pc P j := by
  unfold count
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin L → Fin (n + 1) => Finset.univ.image x)
    (t := Finset.univ) (by intro x _; simp)]
  refine (Finset.sum_congr rfl (fun S _ => fiber_card hP S)).trans ?_
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card (f := pc P)]
  simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have e1 : ∑ m ∈ Finset.range (n + 1 + 1), (n + 1).choose m * pc P m =
      ∑ m ∈ Finset.range (n + L + 2), (n + 1).choose m * pc P m := by
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro m _ hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  have e2 : ∑ m ∈ Finset.range (L + 1), (n + 1).choose m * pc P m =
      ∑ m ∈ Finset.range (n + L + 2), (n + 1).choose m * pc P m := by
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro m _ hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [pc_eq_zero m (by omega), mul_zero]
  rw [e1, e2]

/-- The sum over j ≤ L equals the sum over j ≤ D when the patterns with more than D values
fail P. -/
lemma count_eq_D (hP : Invariant P) (D : ℕ) (hD : ∀ j, D < j → pc P j = 0) (n : ℕ) :
    count P n = ∑ j ∈ Finset.range (D + 1), (n + 1).choose j * pc P j := by
  rw [count_eq hP]
  have e1 : ∑ j ∈ Finset.range (L + 1), (n + 1).choose j * pc P j =
      ∑ j ∈ Finset.range (L + D + 1), (n + 1).choose j * pc P j := by
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro m _ hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [pc_eq_zero m (by omega), mul_zero]
  have e2 : ∑ j ∈ Finset.range (D + 1), (n + 1).choose j * pc P j =
      ∑ j ∈ Finset.range (L + D + 1), (n + 1).choose j * pc P j := by
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro m _ hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [hD m (by omega), mul_zero]
  rw [e1, e2]

/-! ### The polynomial -/

/-- C(X + 1, j) as a polynomial over ℚ. -/
noncomputable def binomPoly (j : ℕ) : Polynomial ℚ :=
  (1 / (j.factorial : ℚ)) • (descPochhammer ℚ j).comp (Polynomial.X + 1)

lemma binomPoly_eval (j n : ℕ) : (binomPoly j).eval (n : ℚ) = ((n + 1).choose j : ℚ) := by
  rw [binomPoly, Polynomial.eval_smul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, show (n : ℚ) + 1 = ((n + 1 : ℕ) : ℚ) by push_cast; ring,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose, smul_eq_mul]
  have : (j.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma binomPoly_natDegree (j : ℕ) : (binomPoly j).natDegree ≤ j := by
  rw [binomPoly]
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  rw [Polynomial.natDegree_comp, descPochhammer_natDegree, ← Polynomial.C_1,
    Polynomial.natDegree_X_add_C, mul_one]

variable (P)

/-- The polynomial of the count, through the patterns with at most D values. -/
noncomputable def countPoly (D : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (D + 1), (pc P j : ℚ) • binomPoly j

variable {P}

lemma countPoly_natDegree (D : ℕ) : (countPoly P D).natDegree ≤ D := by
  unfold countPoly
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun j hj => ?_⟩
  rw [Finset.mem_range] at hj
  exact (Polynomial.natDegree_smul_le _ _).trans ((binomPoly_natDegree j).trans (by omega))

/-- The count is the value of a polynomial of degree at most D. -/
theorem count_poly (hP : Invariant P) (D : ℕ) (hD : ∀ j, D < j → pc P j = 0) (n : ℕ) :
    (count P n : ℚ) = (countPoly P D).eval (n : ℚ) := by
  rw [count_eq_D hP D hD, countPoly, Polynomial.eval_finsetSum]
  push_cast
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Polynomial.eval_smul, binomPoly_eval, smul_eq_mul, mul_comm]

/-- The (1 - x)^(D + 1) recurrence, in forward form: valid for every n. -/
theorem recurrence (hP : Invariant P) (D : ℕ) (hD : ∀ j, D < j → pc P j = 0) (n : ℕ) :
    ∑ k ∈ Finset.range (D + 2), (-1 : ℤ) ^ (D + 1 - k) * (D + 1).choose k * (count P (n + k) : ℤ) = 0 := by
  have h := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (P := countPoly P D) (n := D + 1)
    (by have := countPoly_natDegree (P := P) D; omega)
  have h1 := congrFun h (n : ℚ)
  rw [fwdDiff_iter_eq_sum_shift, Pi.zero_apply] at h1
  have h2 : ((∑ k ∈ Finset.range (D + 2),
      (-1 : ℤ) ^ (D + 1 - k) * (D + 1).choose k * (count P (n + k) : ℤ) : ℤ) : ℚ) = 0 := by
    rw [← h1]
    push_cast
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [zsmul_eq_mul, nsmul_eq_mul, mul_one,
      show ((n : ℚ) + k) = ((n + k : ℕ) : ℚ) by push_cast; ring, ← count_poly hP D hD (n + k)]
    push_cast
    ring
  exact_mod_cast h2

/-! ### The generating function -/

/-- Sum_n C(n + 1, j) x^n = x^(j-1) / (1 - x)^(j+1). -/
lemma binom_series (j : ℕ) :
    PowerSeries.mk (fun n => ((n + 1).choose j : ℤ)) * (1 - X) ^ (j + 1) = X ^ (j - 1) := by
  cases j with
  | zero =>
    simp only [Nat.choose_zero_right, Nat.cast_one, zero_add, pow_one, zero_tsub, pow_zero]
    exact mk_one_mul_one_sub_eq_one ℤ
  | succ d =>
    have hshift : PowerSeries.mk (fun n => ((n + 1).choose (d + 1) : ℤ)) =
        X ^ d * PowerSeries.mk (fun k => ((d + 1 + k).choose (d + 1) : ℤ)) := by
      ext n
      rw [coeff_mk, coeff_X_pow_mul', coeff_mk]
      split_ifs with h
      · congr 2
        omega
      · rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
    rw [hshift, mul_assoc, mk_add_choose_mul_one_sub_pow_eq_one, mul_one, Nat.add_sub_cancel]

/-- The generating function: A(x) (1 - x)^(D + 1) = Sum_{j ≤ D} pc P j x^(j - 1) (1 - x)^(D - j). -/
theorem gf (hP : Invariant P) (D : ℕ) (hD : ∀ j, D < j → pc P j = 0) :
    PowerSeries.mk (fun n => (count P n : ℤ)) * (1 - X) ^ (D + 1) =
      ∑ j ∈ Finset.range (D + 1), (pc P j : ℤ⟦X⟧) * X ^ (j - 1) * (1 - X) ^ (D - j) := by
  have hA : PowerSeries.mk (fun n => (count P n : ℤ)) =
      ∑ j ∈ Finset.range (D + 1), (pc P j : ℤ⟦X⟧) * PowerSeries.mk (fun n => ((n + 1).choose j : ℤ)) := by
    ext n
    rw [coeff_mk, count_eq_D hP D hD, map_sum]
    push_cast
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← map_natCast (C (R := ℤ)), coeff_C_mul, coeff_mk, mul_comm]
  rw [hA, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  rw [show (1 - X : ℤ⟦X⟧) ^ (D + 1) = (1 - X) ^ (j + 1) * (1 - X) ^ (D - j) by
      rw [← pow_add]; congr 1; omega,
    show (pc P j : ℤ⟦X⟧) * PowerSeries.mk (fun n => ((n + 1).choose j : ℤ)) *
        ((1 - X) ^ (j + 1) * (1 - X) ^ (D - j)) =
      (pc P j : ℤ⟦X⟧) * (PowerSeries.mk (fun n => ((n + 1).choose j : ℤ)) * (1 - X) ^ (j + 1)) *
        (1 - X) ^ (D - j) by ring, binom_series]

/-! ### Corollary tools -/

lemma pc_zero (hL : 1 ≤ L) : pc P 0 = 0 := by
  unfold pc
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g _
  exact Fin.elim0 (g ⟨0, hL⟩)

/-- For n = 0 only the constant array remains, a pattern with one value. -/
lemma count_zero (hP : Invariant P) (hL : 1 ≤ L) : count P 0 = pc P 1 := by
  rw [count_eq hP 0, Finset.sum_eq_single 1]
  · simp
  · intro j _ hj
    rcases Nat.lt_or_ge j 1 with h | h
    · rw [show j = 0 by omega, pc_zero hL, mul_zero]
    · rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

/-- The pattern counts are determined by the counts for n < L (when L ≥ 1): the system
count P n = Sum_j C(n + 1, j) v_j, n < L, is triangular in v_1, ..., v_L. -/
theorem pc_of_counts (hP : Invariant P) (hL : 1 ≤ L) (v : ℕ → ℕ) (hv0 : v 0 = 0)
    (hv : ∀ n, n < L → count P n = ∑ j ∈ Finset.range (L + 1), (n + 1).choose j * v j) :
    ∀ j, j ≤ L → pc P j = v j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases j with _ | m
    · rw [pc_zero hL, hv0]
    · have e := (count_eq hP m).symm.trans (hv m (by omega))
      have hcut : ∀ w : ℕ → ℕ, ∑ i ∈ Finset.range (L + 1), (m + 1).choose i * w i =
          ∑ i ∈ Finset.range (m + 1), (m + 1).choose i * w i + w (m + 1) := by
        intro w
        rw [← Finset.sum_subset (Finset.range_subset_range.2 (show m + 2 ≤ L + 1 by omega))
          (fun i _ hi => by
            simp only [Finset.mem_range, not_lt] at hi
            rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]),
          Finset.sum_range_succ, Nat.choose_self, one_mul]
      rw [hcut (pc P), hcut v, Finset.sum_congr rfl (fun i hi => by
        rw [ih i (by rw [Finset.mem_range] at hi; omega) (by rw [Finset.mem_range] at hi; omega)])] at e
      omega

/-- The generating function of the sequence with a(0) replaced by 0 (offset 1). -/
theorem gf_offset (hP : Invariant P) (D : ℕ) (hD : ∀ j, D < j → pc P j = 0) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else count P n) * (1 - X) ^ (D + 1) =
      ∑ j ∈ Finset.range (D + 1), (pc P j : ℤ⟦X⟧) * X ^ (j - 1) * (1 - X) ^ (D - j) -
        (count P 0 : ℤ⟦X⟧) * (1 - X) ^ (D + 1) := by
  have hmk : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else count P n) =
      PowerSeries.mk (fun n => (count P n : ℤ)) - C (count P 0 : ℤ) := by
    ext n
    rw [coeff_mk, map_sub, coeff_mk, coeff_C]
    split_ifs with h
    · subst h
      simp
    · simp
  rw [hmk, sub_mul, gf hP D hD, map_natCast]

end OrderOnly

namespace OMA.S_oeis_a228744

open PowerSeries OrderOnly




/-! ### Realizing an array of medians -/

lemma med_map {α β : Type*} [LinearOrder α] [LinearOrder β] {g : α → β} (hg : Monotone g)
    (u v w : α) : g (med u v w) = med (g u) (g v) (g w) := by
  unfold med
  rw [hg.map_max, hg.map_min, hg.map_min, hg.map_max]

/-- x(0..k+1) has the medians y(0..k-1) of its three adjacent elements. -/
def realizes {k : ℕ} (x : Fin (k + 2) → ℕ) (y : Fin k → ℕ) : Prop :=
  ∀ i : Fin k, med (x i.castSucc.castSucc) (x i.castSucc.succ) (x i.succ.succ) = y i

lemma realizes_cons {k : ℕ} (u : ℕ) (x : Fin (k + 2) → ℕ) (c : ℕ) (y : Fin k → ℕ) :
    realizes (Fin.cons u x : Fin (k + 3) → ℕ) (Fin.cons c y : Fin (k + 1) → ℕ) ↔
      med u (x 0) (x 1) = c ∧ realizes x y := by
  unfold realizes
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.cons_one,
    Fin.succ_one_eq_two, Fin.castSucc_succ]
  rfl

/-! ### Bitmasks of pairs -/

/-- The bitmask with bit i set exactly when p i, for i < K. -/
def mask (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | K + 1 => mask p K ||| (if p K then 2 ^ K else 0)

lemma testBit_ite (b : Bool) (K i : ℕ) :
    (if b then 2 ^ K else 0).testBit i = (b && decide (K = i)) := by
  cases b
  · simp
  · simp [Nat.testBit_two_pow]

lemma testBit_mask (p : ℕ → Bool) : ∀ K i, (mask p K).testBit i = (decide (i < K) && p i)
  | 0, i => by simp [mask]
  | K + 1, i => by
    rw [mask, Nat.testBit_lor, testBit_mask p K i, testBit_ite]
    rcases Nat.lt_trichotomy i K with h | rfl | h
    · simp [h, h.ne', show i < K + 1 by omega]
    · simp
    · simp [h.ne, show ¬ i < K by omega, show ¬ i < K + 1 by omega]

lemma mask_lt (p : ℕ → Bool) : ∀ K, mask p K < 2 ^ K
  | 0 => by simp [mask]
  | K + 1 => by
    rw [mask]
    refine Nat.or_lt_two_pow ((mask_lt p K).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))) ?_
    split_ifs
    · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    · positivity

/-- The values d < N with med a b d = c, as a bitmask. -/
def M (N a b c : ℕ) : ℕ :=
  if c < min a b ∨ max a b < c then 0
  else if min a b = max a b then 2 ^ N - 1
  else if c = min a b then 2 ^ (c + 1) - 1
  else if c = max a b then (2 ^ (N - c) - 1) <<< c
  else 2 ^ c

lemma testBit_M (N a b c d : ℕ) (ha : a < N) (hb : b < N) :
    (M N a b c).testBit d = (decide (d < N) && decide (med a b d = c)) := by
  have hmed : med a b d = max (min a b) (min (max a b) d) := rfl
  rw [hmed]
  unfold M
  split_ifs with h1 h2 h3 h4
  · simp only [Nat.zero_testBit]
    symm
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right
    omega
  · rw [Nat.testBit_two_pow_sub_one]
    by_cases hd : d < N
    · simp [hd]
      omega
    · simp [hd]
  · rw [Nat.testBit_two_pow_sub_one]
    by_cases hd : d < N
    · simp only [hd, decide_true, Bool.true_and]
      congr 1
      apply propext
      omega
    · simp only [hd, decide_false, Bool.false_and, decide_eq_false_iff_not]
      omega
  · rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases hd : d < N
    · simp only [hd, decide_true, Bool.true_and]
      have e : (decide (d ≥ c) && decide (d - c < N - c)) = decide (c ≤ d) := by
        by_cases hcd : c ≤ d
        · simp [hcd, show d - c < N - c by omega]
        · simp [hcd]
      rw [e]
      congr 1
      apply propext
      omega
    · simp only [hd, decide_false, Bool.false_and]
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      right
      omega
  · rw [Nat.testBit_two_pow]
    by_cases hd : d < N
    · simp only [hd, decide_true, Bool.true_and]
      congr 1
      apply propext
      omega
    · simp only [hd, decide_false, Bool.false_and, decide_eq_false_iff_not]
      omega

/-- The pairs (a, b) of values below N, as bits a * N + b, for which some d < N has
med a b d = c and (b, d) in S. -/
def stepF (N c S : ℕ) : ℕ :=
  mask (fun i => decide ((S >>> (i % N * N)) &&& M N (i / N) (i % N) c ≠ 0)) (N * N)

lemma testBit_stepF (N c S a b : ℕ) (ha : a < N) (hb : b < N) :
    (stepF N c S).testBit (a * N + b) = true ↔
      ∃ d < N, med a b d = c ∧ S.testBit (b * N + d) = true := by
  have hlt : a * N + b < N * N := by nlinarith
  have hdiv : (a * N + b) / N = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, zero_add]
  have hmod : (a * N + b) % N = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  rw [stepF, testBit_mask, hdiv, hmod]
  simp only [hlt, decide_true, Bool.true_and, decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨d, hd⟩ := Nat.exists_testBit_of_ne_zero h
    rw [Nat.testBit_land, Nat.testBit_shiftRight, testBit_M N a b c d ha hb] at hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
    exact ⟨d, hd.2.1, hd.2.2, hd.1⟩
  · rintro ⟨d, hd, hm, hs⟩ h0
    have := congrArg (fun t => Nat.testBit t d) h0
    simp only [Nat.testBit_land, Nat.testBit_shiftRight, testBit_M N a b c d ha hb, hs, hd, hm,
      Nat.zero_testBit] at this
    simp at this

/-- The feasible first pairs (x(0), x(1)), values below N, for the medians y. -/
def feas (N : ℕ) : List ℕ → ℕ
  | [] => 2 ^ (N * N) - 1
  | c :: y => stepF N c (feas N y)

lemma feas_lt (N : ℕ) : ∀ y, feas N y < 2 ^ (N * N)
  | [] => by
    show 2 ^ (N * N) - 1 < 2 ^ (N * N)
    have := Nat.one_le_two_pow (n := N * N)
    omega
  | c :: y => mask_lt _ _

lemma testBit_feas (N : ℕ) : ∀ {k : ℕ} (y : Fin k → ℕ) (u v : ℕ), u < N → v < N →
    ((feas N (List.ofFn y)).testBit (u * N + v) = true ↔
      ∃ x : Fin (k + 2) → ℕ, (∀ j, x j < N) ∧ x 0 = u ∧ x 1 = v ∧ realizes x y)
  | 0, y, u, v, hu, hv => by
    have hlt : u * N + v < N * N := by nlinarith
    simp only [List.ofFn_zero, feas, Nat.testBit_two_pow_sub_one, hlt, decide_true]
    simp only [true_iff]
    refine ⟨![u, v], fun j => ?_, rfl, rfl, fun i => i.elim0⟩
    fin_cases j
    · exact hu
    · exact hv
  | k + 1, y, u, v, hu, hv => by
    rw [List.ofFn_succ, feas, testBit_stepF N _ _ u v hu hv]
    constructor
    · rintro ⟨d, hd, hm, hs⟩
      obtain ⟨x, hx, hx0, hx1, hr⟩ := (testBit_feas N (fun i => y i.succ) v d hv hd).1 hs
      refine ⟨Fin.cons u x, fun j => ?_, rfl, by simp [hx0], ?_⟩
      · refine Fin.cases hu (fun j => ?_) j
        simpa using hx j
      · rw [show y = Fin.cons (y 0) (fun i => y i.succ) from (Fin.cons_self_tail y).symm,
          realizes_cons, hx0, hx1]
        exact ⟨hm, hr⟩
    · rintro ⟨x, hx, hx0, hx1, hr⟩
      rw [show x = Fin.cons (x 0) (Fin.tail x) from (Fin.cons_self_tail x).symm,
        show y = Fin.cons (y 0) (fun i => y i.succ) from (Fin.cons_self_tail y).symm,
        realizes_cons] at hr
      refine ⟨x 2, hx 2, ?_, ?_⟩
      · rw [← hx0, ← hx1]
        exact hr.1
      · refine (testBit_feas N (fun i => y i.succ) v (x 2) hv (hx 2)).2
          ⟨Fin.tail x, fun j => hx _, by rw [← hx1]; rfl, rfl, hr.2⟩

/-- An array of medians, values below N, is realized iff its feasible set is nonempty. -/
lemma realizable_iff (N : ℕ) {k : ℕ} (y : Fin k → ℕ) :
    (∃ x : Fin (k + 2) → ℕ, (∀ j, x j < N) ∧ realizes x y) ↔ feas N (List.ofFn y) ≠ 0 := by
  constructor
  · rintro ⟨x, hx, hr⟩ h0
    have := (testBit_feas N y (x 0) (x 1) (hx 0) (hx 1)).2 ⟨x, hx, rfl, rfl, hr⟩
    rw [h0, Nat.zero_testBit] at this
    exact Bool.false_ne_true this
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
    have hiN : i < N * N := by
      by_contra hc
      rw [Nat.testBit_lt_two_pow ((feas_lt N _).trans_le
        (Nat.pow_le_pow_right (by norm_num) (by omega)))] at hi
      exact Bool.false_ne_true hi
    have hN : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · subst h0; omega
      · exact h0
    have hu : i / N < N := by
      rw [Nat.div_lt_iff_lt_mul hN]
      exact hiN
    have hv : i % N < N := Nat.mod_lt _ hN
    rw [show i = i / N * N + i % N by rw [Nat.mul_comm]; exact (Nat.div_add_mod i N).symm] at hi
    obtain ⟨x, hx, -, -, hr⟩ := (testBit_feas N y _ _ hu hv).1 hi
    exact ⟨x, hx, hr⟩

/-! ### Counting through a closed set of feasible sets -/

/-- Entry i of a packed table: the digit i of P in base 2^w. -/
def entry (w P i : ℕ) : ℕ := P / 2 ^ (w * i) % 2 ^ w

/-- The state index of the medians y, read from the right, under the transitions T. -/
def idx (T : ℕ → ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | c :: y => T (idx T y) c

/-- With verified transitions, the state of y is one of the L states and is its feasible set. -/
lemma idx_spec (N L : ℕ) (St : ℕ → ℕ) (T : ℕ → ℕ → ℕ)
    (h0 : St 0 = 2 ^ (N * N) - 1) (hpos : 0 < L)
    (hT : ∀ i < L, ∀ c < N, T i c < L ∧ stepF N c (St i) = St (T i c)) :
    ∀ y : List ℕ, (∀ c ∈ y, c < N) → idx T y < L ∧ St (idx T y) = feas N y
  | [], _ => ⟨hpos, h0⟩
  | c :: y, hy => by
    obtain ⟨h1, h2⟩ := idx_spec N L St T h0 hpos hT y (fun d hd => hy d (List.mem_cons_of_mem _ hd))
    obtain ⟨h3, h4⟩ := hT (idx T y) h1 c (hy c List.mem_cons_self)
    refine ⟨h3, ?_⟩
    show St (T (idx T y) c) = stepF N c (feas N y)
    rw [← h4, h2]

/-- Counts are packed as digits in base B = 2^20. -/
def B : ℕ := 2 ^ 20

lemma B_pos : 0 < B := by
  unfold B
  positivity

lemma digits_succ (n : ℕ → ℕ) (h : ∀ i, n i < B) (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), n i * B ^ i) % B = n 0 ∧
      (∑ i ∈ Finset.range (m + 1), n i * B ^ i) / B = ∑ i ∈ Finset.range m, n (i + 1) * B ^ i := by
  have e : ∑ i ∈ Finset.range (m + 1), n i * B ^ i =
      n 0 + B * ∑ i ∈ Finset.range m, n (i + 1) * B ^ i := by
    rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero, mul_one, add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pow_succ]
    ring
  rw [e]
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h 0)]
  · rw [Nat.add_mul_div_left _ _ B_pos, Nat.div_eq_of_lt (h 0), zero_add]

lemma list_sum_range (f : ℕ → ℕ) : ∀ N, ((List.range N).map f).sum = ∑ c ∈ Finset.range N, f c
  | 0 => rfl
  | N + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f N,
      Finset.sum_range_succ]
    simp

/-- One step on packed counts: the counts at the states i, i + 1, ..., i + m - 1 (the digits of
V) move to the successors of each state. -/
def stepV (N : ℕ) (T : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | m + 1, i, V => ((List.range N).map (fun c => V % B * B ^ T i c)).sum + stepV N T m (i + 1) (V / B)

lemma stepV_eq (N : ℕ) (T : ℕ → ℕ → ℕ) : ∀ (m i : ℕ) (n : ℕ → ℕ), (∀ j, n j < B) →
    stepV N T m i (∑ j ∈ Finset.range m, n (i + j) * B ^ j) =
      ∑ j ∈ Finset.range m, n (i + j) * ∑ c ∈ Finset.range N, B ^ T (i + j) c
  | 0, i, n, _ => by simp [stepV]
  | m + 1, i, n, h => by
    obtain ⟨h1, h2⟩ := digits_succ (fun j => n (i + j)) (fun j => h _) m
    rw [add_zero] at h1
    have e1 : ∑ j ∈ Finset.range m, n (i + (j + 1)) * B ^ j =
        ∑ j ∈ Finset.range m, n (i + 1 + j) * B ^ j :=
      Finset.sum_congr rfl (fun j _ => by rw [show i + (j + 1) = i + 1 + j by omega])
    have e2 : ∑ j ∈ Finset.range m, n (i + (j + 1)) * ∑ c ∈ Finset.range N, B ^ T (i + (j + 1)) c =
        ∑ j ∈ Finset.range m, n (i + 1 + j) * ∑ c ∈ Finset.range N, B ^ T (i + 1 + j) c :=
      Finset.sum_congr rfl (fun j _ => by rw [show i + (j + 1) = i + 1 + j by omega])
    rw [stepV, h1, h2, e1, stepV_eq N T m (i + 1) n h, list_sum_range, Finset.sum_range_succ' _ m,
      e2, add_zero, ← Finset.mul_sum]
    ring

/-- The packed counts by state of the medians of length k, starting from state 0. -/
def layer (N L : ℕ) (T : ℕ → ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => stepV N T L 0 (layer N L T k)

/-- The sum of the digits of V at the states i, ..., i + m - 1 that are nonempty feasible
sets. -/
def readout (St : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | m + 1, i, V => (if St i = 0 then 0 else V % B) + readout St m (i + 1) (V / B)

lemma readout_eq (St : ℕ → ℕ) : ∀ (m i : ℕ) (n : ℕ → ℕ), (∀ j, n j < B) →
    readout St m i (∑ j ∈ Finset.range m, n (i + j) * B ^ j) =
      ∑ j ∈ Finset.range m, if St (i + j) = 0 then 0 else n (i + j)
  | 0, i, n, _ => by simp [readout]
  | m + 1, i, n, h => by
    obtain ⟨h1, h2⟩ := digits_succ (fun j => n (i + j)) (fun j => h _) m
    rw [add_zero] at h1
    have e1 : ∑ j ∈ Finset.range m, n (i + (j + 1)) * B ^ j =
        ∑ j ∈ Finset.range m, n (i + 1 + j) * B ^ j :=
      Finset.sum_congr rfl (fun j _ => by rw [show i + (j + 1) = i + 1 + j by omega])
    have e2 : (∑ j ∈ Finset.range m, if St (i + (j + 1)) = 0 then 0 else n (i + (j + 1))) =
        ∑ j ∈ Finset.range m, if St (i + 1 + j) = 0 then 0 else n (i + 1 + j) :=
      Finset.sum_congr rfl (fun j _ => by rw [show i + (j + 1) = i + 1 + j by omega])
    rw [readout, h1, h2, e1, readout_eq St m (i + 1) n h, Finset.sum_range_succ' _ m, e2, add_zero]
    ring

/-- The arrays y of length k by state. -/
def cnt (N : ℕ) (T : ℕ → ℕ → ℕ) (k i : ℕ) : ℕ :=
  (Finset.univ.filter (fun y : Fin k → Fin N => idx T (List.ofFn (fun j => (y j : ℕ))) = i)).card

lemma cnt_lt (N : ℕ) (T : ℕ → ℕ → ℕ) (k i : ℕ) (hk : N ^ k < B) : cnt N T k i < B := by
  unfold cnt
  refine lt_of_le_of_lt (Finset.card_filter_le _ _) ?_
  simpa using hk

/-- A sum over the arrays through their states. -/
lemma sum_by_state (N L : ℕ) (T : ℕ → ℕ → ℕ) (k : ℕ)
    (hin : ∀ y : Fin k → Fin N, idx T (List.ofFn (fun j => (y j : ℕ))) < L) (g : ℕ → ℕ) :
    ∑ y : Fin k → Fin N, g (idx T (List.ofFn (fun j => (y j : ℕ)))) =
      ∑ i ∈ Finset.range L, cnt N T k i * g i := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun y : Fin k → Fin N => idx T (List.ofFn (fun j => (y j : ℕ))))
    (t := Finset.range L) (fun y _ => Finset.mem_range.2 (hin y))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_congr rfl (fun y hy => by rw [(Finset.mem_filter.1 hy).2]), Finset.sum_const,
    smul_eq_mul]
  rfl

/-- The packed layers hold the counts by state. -/
theorem layer_eq (N L : ℕ) (St : ℕ → ℕ) (T : ℕ → ℕ → ℕ)
    (h0 : St 0 = 2 ^ (N * N) - 1) (hpos : 0 < L)
    (hT : ∀ i < L, ∀ c < N, T i c < L ∧ stepF N c (St i) = St (T i c)) :
    ∀ k, N ^ k < B → layer N L T k = ∑ i ∈ Finset.range L, cnt N T k i * B ^ i
  | 0, _ => by
    rw [layer, ← sum_by_state N L T 0 (fun y => by simp [idx, hpos]) (fun i => B ^ i)]
    simp [idx]
  | k + 1, hk => by
    have hin : ∀ (k : ℕ) (y : Fin k → Fin N), idx T (List.ofFn (fun j => (y j : ℕ))) < L :=
      fun k y => (idx_spec N L St T h0 hpos hT _ (fun c hc => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hc
        exact (y j).isLt)).1
    have hk' : N ^ k < B := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h
        have h1 : (0 : ℕ) ^ k ≤ 1 := by
          rcases k with _ | k <;> simp
        exact lt_of_le_of_lt h1 (by unfold B; norm_num)
      · exact lt_of_le_of_lt (Nat.pow_le_pow_right h (by omega)) hk
    have hs := stepV_eq N T L 0 (cnt N T k) (fun i => cnt_lt N T k i hk')
    simp only [zero_add] at hs
    rw [layer, layer_eq N L St T h0 hpos hT k hk', hs,
      ← sum_by_state N L T k (hin k) (fun i => ∑ c ∈ Finset.range N, B ^ T i c),
      ← sum_by_state N L T (k + 1) (hin (k + 1)) (fun i => B ^ i)]
    rw [(Fintype.sum_equiv (Fin.consEquiv fun _ => Fin N) _ _ (fun _ => rfl)).symm,
      Fintype.sum_prod_type, Finset.sum_comm, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun y _ => ?_))
    simp [Fin.consEquiv, List.ofFn_succ, idx]

/-- The count of the arrays of medians, through the packed layers. -/
theorem count_eq_readout (N L : ℕ) (St : ℕ → ℕ) (T : ℕ → ℕ → ℕ)
    (h0 : St 0 = 2 ^ (N * N) - 1) (hpos : 0 < L)
    (hT : ∀ i < L, ∀ c < N, T i c < L ∧ stepF N c (St i) = St (T i c)) (k : ℕ) (hk : N ^ k < B) :
    ∑ y : Fin k → Fin N, (if feas N (List.ofFn (fun j => (y j : ℕ))) = 0 then 0 else 1) =
      readout St L 0 (layer N L T k) := by
  have hsp : ∀ y : Fin k → Fin N, idx T (List.ofFn (fun j => (y j : ℕ))) < L ∧
      St (idx T (List.ofFn (fun j => (y j : ℕ)))) = feas N (List.ofFn (fun j => (y j : ℕ))) :=
    fun y => idx_spec N L St T h0 hpos hT _ (fun c hc => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hc
      exact (y j).isLt)
  have hr := readout_eq St L 0 (cnt N T k) (fun i => cnt_lt N T k i hk)
  simp only [zero_add] at hr
  rw [Finset.sum_congr rfl (fun y _ => by rw [← (hsp y).2]),
    sum_by_state N L T k (fun y => (hsp y).1) (fun i => if St i = 0 then 0 else 1),
    layer_eq N L St T h0 hpos hT k hk, hr]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp

/-! ### The entry's arrays -/

lemma medians_iff {n : ℕ} (x : Fin 9 → Fin (n + 1)) (y : Fin 7 → Fin (n + 1)) :
    medians x = y ↔ realizes (fun j => (x j : ℕ)) (fun i => (y i : ℕ)) := by
  rw [funext_iff]
  refine forall_congr' (fun i => ?_)
  rw [Fin.ext_iff, medians, med_map Fin.val_strictMono.monotone]
  rfl

/-- The count through the feasible sets, values below n + 1. -/
lemma a_feas (n : ℕ) : a n = ∑ y : Fin 7 → Fin (n + 1),
    if feas (n + 1) (List.ofFn (fun i => (y i : ℕ))) = 0 then 0 else 1 := by
  rw [a, Finset.card_filter]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have h : (∃ x : Fin 9 → Fin (n + 1), medians x = y) ↔
      feas (n + 1) (List.ofFn (fun i => (y i : ℕ))) ≠ 0 := by
    rw [← realizable_iff]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨fun j => (x j : ℕ), fun j => (x j).isLt, (medians_iff x y).1 hx⟩
    · rintro ⟨x, hx, hr⟩
      exact ⟨fun j => ⟨x j, hx j⟩, (medians_iff _ y).2 hr⟩
  by_cases hf : feas (n + 1) (List.ofFn (fun i => (y i : ℕ))) = 0
  · rw [if_pos hf, if_neg (fun hx => (h.1 hx) hf)]
  · rw [if_neg hf, if_pos (h.2 hf)]

/-- The count through a verified table of L feasible sets (entries of StP, 64 bits each) and
their successors (entries of TrP, 8 bits each, the successor of state i under the median c at
position i * N + c). -/
lemma a_dp (n L StP TrP : ℕ) (h0 : entry 64 StP 0 = 2 ^ ((n + 1) * (n + 1)) - 1) (hpos : 0 < L)
    (hT : ∀ i < L, ∀ c < n + 1, entry 8 TrP (i * (n + 1) + c) < L ∧
      stepF (n + 1) c (entry 64 StP i) = entry 64 StP (entry 8 TrP (i * (n + 1) + c)))
    (hk : (n + 1) ^ 7 < B) :
    a n = readout (entry 64 StP) L 0 (layer (n + 1) L (fun i c => entry 8 TrP (i * (n + 1) + c)) 7) := by
  rw [a_feas, count_eq_readout (n + 1) L (entry 64 StP) (fun i c => entry 8 TrP (i * (n + 1) + c))
    h0 hpos hT 7 hk]

/-- The transitions of the states i, ..., i + m - 1 of a packed table, checked as booleans:
each successor index is below L and is the successor. -/
def chk (N L StP TrP : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | m + 1, i => (List.range N).all (fun c => decide (entry 8 TrP (i * N + c) < L) &&
      decide (stepF N c (entry 64 StP i) = entry 64 StP (entry 8 TrP (i * N + c)))) &&
    chk N L StP TrP m (i + 1)

lemma chk_spec (N L StP TrP : ℕ) : ∀ m i, chk N L StP TrP m i = true →
    ∀ j < m, ∀ c < N, entry 8 TrP ((i + j) * N + c) < L ∧
      stepF N c (entry 64 StP (i + j)) = entry 64 StP (entry 8 TrP ((i + j) * N + c))
  | 0, _, _ => fun j hj => absurd hj (Nat.not_lt_zero j)
  | m + 1, i, h => by
    rw [chk, Bool.and_eq_true, List.all_eq_true] at h
    intro j hj c hc
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simpa using h.1 c (List.mem_range.2 hc)
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have := chk_spec N L StP TrP m (i + 1) h.2 j' (by omega) c hc
      rwa [show i + 1 + j' = i + (j' + 1) by omega] at this

/-- The 1 feasible sets reached for values 0..0 (index 0: all pairs), 64 bits each. -/
def StP1 : ℕ := 0x1

/-- Their successors under the medians c = 0..0, 8 bits each at position i * 1 + c. -/
def TrP1 : ℕ := 0x0

/-- The transitions for values 0..0, checked by evaluation one block of states after
the other. -/
lemma cert1 : ∀ i < 1, ∀ c < 1, entry 8 TrP1 (i * 1 + c) < 1 ∧
    stepF 1 c (entry 64 StP1 i) = entry 64 StP1 (entry 8 TrP1 (i * 1 + c)) := by
  have c0 : chk 1 1 StP1 TrP1 1 0 = true := by decide +kernel
  intro i hi c hc
  have := chk_spec 1 1 StP1 TrP1 1 0 c0 (i - 0) (by omega) c hc
  rwa [show 0 + (i - 0) = i by omega] at this

lemma av0 : a 0 = 1 := by
  rw [a_dp 0 1 StP1 TrP1 (by decide +kernel) (by norm_num) cert1 (by decide +kernel)]
  decide +kernel

/-- The 12 feasible sets reached for values 0..1 (index 0: all pairs), 64 bits each. -/
def StP2 : ℕ := 0x8000000000000000100000000000000040000000000000005000000000000000a00000000000000020000000000000003000000000000000c000000000000000e0000000000000007000000000000000f

/-- Their successors under the medians c = 0..1, 8 bits each at position i * 2 + c. -/
def TrP2 : ℕ := 0xb0b060b0b070a050a010209080908070605020403010201

/-- The transitions for values 0..1, checked by evaluation one block of states after
the other. -/
lemma cert2 : ∀ i < 12, ∀ c < 2, entry 8 TrP2 (i * 2 + c) < 12 ∧
    stepF 2 c (entry 64 StP2 i) = entry 64 StP2 (entry 8 TrP2 (i * 2 + c)) := by
  have c0 : chk 2 12 StP2 TrP2 12 0 = true := by decide +kernel
  intro i hi c hc
  have := chk_spec 2 12 StP2 TrP2 12 0 c0 (i - 0) (by omega) c hc
  rwa [show 0 + (i - 0) = i by omega] at this

lemma av1 : a 1 = 88 := by
  rw [a_dp 1 12 StP2 TrP2 (by decide +kernel) (by norm_num) cert2 (by decide +kernel)]
  decide +kernel

/-- The 33 feasible sets reached for values 0..2 (index 0: all pairs), 64 bits each. -/
def StP3 : ℕ := 0x900000000000000002000000000000010000000000000000b0000000000000001a000000000000008000000000000000120000000000000000000000000000000100000000000000c000000000000000da000000000000000300000000000000080000000000000024000000000000004000000000000000480000000000000049000000000000012400000000000000200000000000000004000000000000018000000000000000b60000000000000006000000000000003e000000000000000500000000000001c00000000000000007000000000000014000000000000000f800000000000001e400000000000000fe000000000000004f00000000000001ff

/-- Their successors under the medians c = 0..2, 8 bits each at position i * 3 + c. -/
def TrP3 : ℕ := 0x1e0b191911180f19190c0b191916151e13191916181919191919101e130d1e020619111019201f171c181e0e0d1e1d0a1e1d01031c181b1a191214180f13190702181211181716151214100f130d1211100f0e0d0c0b0a030908070206050401030201

/-- The transitions for values 0..2, checked by evaluation one block of states after
the other. -/
lemma cert3 : ∀ i < 33, ∀ c < 3, entry 8 TrP3 (i * 3 + c) < 33 ∧
    stepF 3 c (entry 64 StP3 i) = entry 64 StP3 (entry 8 TrP3 (i * 3 + c)) := by
  have c0 : chk 3 33 StP3 TrP3 33 0 = true := by decide +kernel
  intro i hi c hc
  have := chk_spec 3 33 StP3 TrP3 33 0 c0 (i - 0) (by omega) c hc
  rwa [show 0 + (i - 0) = i by omega] at this

lemma av2 : a 2 = 1071 := by
  rw [a_dp 2 33 StP3 TrP3 (by decide +kernel) (by norm_num) cert3 (by decide +kernel)]
  decide +kernel

/-- The 66 feasible sets reached for values 0..3 (index 0: all pairs), 64 bits each. -/
def StP4 : ℕ := 0x440000000000004400000000000000004000000000000000040000000000002220000000000000000200000000000080000000000000004c0000000000000022e00000000000000744000000000000400000000000000004440000000000000200000000000000003200000000000020000000000000002200000000000000002200000000000000000000000000000001000000000000700000000000000077440000000000000076000000000000000500000000000003000000000000000100000000000000088800000000000030000000000000003300000000000000333200000000000000030000000000000010000000000000008800000000000000cc00000000000010000000000000001100000000000000111000000000000011110000000000008888000000000000080000000000000000800000000000000008000000000000c0000000000000004ccc00000000000000c0000000000000000c000000000000a0000000000000006e0000000000000022ee000000000000000e0000000000000fcc00000000000000ba0000000000000009000000000000f00000000000000000fe000000000000000d000000000000b0000000000000007f00000000000000000f00000000000090000000000000005d0000000000000033f0000000000000f8880000000000007fcc00000000000033fe000000000000111f000000000000ffff

/-- Their successors under the medians c = 0..3, 8 bits each at position i * 4 + c. -/
def TrP4 : ℕ := 0x3026342f3b17303030323130301f232f3b3a123030301e2f1c3030301817303014131230302d2c2b3b283030302d342f30404130303025243b1b22303b3a21303030252f303030303030301d3b2822193b030c0b30262524301f231d3040413e30403f3e2e38342f3b1b22193b3a21153b3a020830301e1d30303d3c272a342f2726342f3b1b1a193b3a16153b3a39113b3a39010438342f37363030333531302029232f1c2830300d03342f33323130201f232f1c1b2230181721300a09022f201f1e2f2e2d2c2b272a25242029231d1c28221927262524201f231d1c1b221918172115201f1e1d1c1b1a19181716151413121104100f0e0d030c0b0a0902080706050104030201

/-- The transitions for values 0..3, checked by evaluation one block of states after
the other. -/
lemma cert4 : ∀ i < 66, ∀ c < 4, entry 8 TrP4 (i * 4 + c) < 66 ∧
    stepF 4 c (entry 64 StP4 i) = entry 64 StP4 (entry 8 TrP4 (i * 4 + c)) := by
  have c0 : chk 4 66 StP4 TrP4 30 0 = true := by decide +kernel
  have c1 : chk 4 66 StP4 TrP4 30 30 = true := by decide +kernel
  have c2 : chk 4 66 StP4 TrP4 6 60 = true := by decide +kernel
  intro i hi c hc
  by_cases h0 : i < 30
  · have := chk_spec 4 66 StP4 TrP4 30 0 c0 (i - 0) (by omega) c hc
    rwa [show 0 + (i - 0) = i by omega] at this
  by_cases h1 : i < 60
  · have := chk_spec 4 66 StP4 TrP4 30 30 c1 (i - 30) (by omega) c hc
    rwa [show 30 + (i - 30) = i by omega] at this
  have := chk_spec 4 66 StP4 TrP4 6 60 c2 (i - 60) (by omega) c hc
  rwa [show 60 + (i - 60) = i by omega] at this

lemma av3 : a 3 = 6130 := by
  rw [a_dp 3 66 StP4 TrP4 (by decide +kernel) (by norm_num) cert4 (by decide +kernel)]
  decide +kernel

/-- The 111 feasible sets reached for values 0..4 (index 0: all pairs), 64 bits each. -/
def StP5 : ℕ := 0x210800000000000001080000000000840000000000000000200000000000000001000000000000000008000000000000008400000000004210000000000000000080000000000000000400000000002108400000000000000002000000000100000000000000008c000000000000004270000000000000210bc0000000000007a10800000000008000000000000000042108000000000002000000000000000100000000000000001c84000000000040000000000000004200000000000000001084000000000000080000000000000000620000000000200000000000000021000000000000002108000000000000000042000000000000000000000000000000010000000000f000000000000000f7a1080000000000003d8c000000000000016a00000000000000090000000000038000000000000001800000000000000080000000000000084210000000000070000000000000007380000000000000739c8400000000000000e600000000000000050000000000000c00000000000000040000000000000042100000000000006318000000000030000000000000003180000000000000318c000000000000318c620000000000000003000000000000002000000000000002100000000000000318000000000000039c0000000000100000000000000010800000000000001084000000000000108420000000000010842100000000010842100000000000080000000000000000400000000000000002000000000000000010000000000180000000000000008c631800000000000060000000000000000300000000000000001800000000014000000000000000ce0000000000000042739c0000000000000380000000000000001c00000000012000000000000000ad000000000000006378000000000000210bde000000000000001e00000000000fe3180000000000005e94000000000000027200000000000000110000000001f000000000000000007f9c000000000000037a000000000000001900000000017000000000000000ff800000000000000003fe000000000000001d00000000013000000000000000bd8000000000000073fc00000000000000001f000000000110000000000000009c8000000000000052f4000000000000318fe00000000001f842100000000000ffe318000000000073ff9c0000000000318ffe000000000010843f0000000001ffffff

/-- Their successors under the medians c = 0..4, 8 bits each at position i * 5 + c. -/
def TrP5 : ℕ := 0x4f4359544e4f3a3f544e62274f4f4f4f57564f4f4f5255504f4f313e364e4f4f39544e6261214f4f4f4f51504f4f4f30364e6261601b4f4f4f4f2f4e2d4f4f4f4f28274f4f4f2322214f4f1e1d1c1b4f4f4c4b4a4962454f4f4f4f4c59544e4f6c6e4f4f4f6c6b6d4f4f4f424140622c3d4f4f62613c4f4f4f4f42544e4f4f67684f4f4f4f3837622c2b354f626126344f626160334f4f4f4f384e4f4f4f4f4f4f4f4f4f2e62453d352962041413124f434241404f3a3f38374f313e362e4f6c6e6d694f6c6b6d694f6c6b6a694d5e59544e622c3d352962613c34246261030f0e4f4f3938374f4f30362e4f4f6768654f4f676665444859544e444359544e622c2b35296261263424626160331f626160020a4f4f4f2f2e4f4f4f64633b473f544e3b3a3f544e3b3a39544e622c2b2a296261262524626160201f6261605f1a6261605f01055e59544e5d5c4f4f4f585b564f4f535a55504f32463e364e2d454f4f4f150459544e5857564f4f535255504f32313e364e2d2c3d4f4f28273c4f4f111003544e535251504f323130364e2d2c2b354f282726344f232221334f0d0c0b024e3231302f4e4d4c4b4a4944484241403b473f383732463e362e2d453d352944434241403b3a3f383732313e362e2d2c3d352928273c34243b3a393837323130362e2d2c2b35292827263424232221331f3231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a051918171615041413121110030f0e0d0c0b020a09080706010504030201

/-- The transitions for values 0..4, checked by evaluation one block of states after
the other. -/
lemma cert5 : ∀ i < 111, ∀ c < 5, entry 8 TrP5 (i * 5 + c) < 111 ∧
    stepF 5 c (entry 64 StP5 i) = entry 64 StP5 (entry 8 TrP5 (i * 5 + c)) := by
  have c0 : chk 5 111 StP5 TrP5 24 0 = true := by decide +kernel
  have c1 : chk 5 111 StP5 TrP5 24 24 = true := by decide +kernel
  have c2 : chk 5 111 StP5 TrP5 24 48 = true := by decide +kernel
  have c3 : chk 5 111 StP5 TrP5 24 72 = true := by decide +kernel
  have c4 : chk 5 111 StP5 TrP5 15 96 = true := by decide +kernel
  intro i hi c hc
  by_cases h0 : i < 24
  · have := chk_spec 5 111 StP5 TrP5 24 0 c0 (i - 0) (by omega) c hc
    rwa [show 0 + (i - 0) = i by omega] at this
  by_cases h1 : i < 48
  · have := chk_spec 5 111 StP5 TrP5 24 24 c1 (i - 24) (by omega) c hc
    rwa [show 24 + (i - 24) = i by omega] at this
  by_cases h2 : i < 72
  · have := chk_spec 5 111 StP5 TrP5 24 48 c2 (i - 48) (by omega) c hc
    rwa [show 48 + (i - 48) = i by omega] at this
  by_cases h3 : i < 96
  · have := chk_spec 5 111 StP5 TrP5 24 72 c3 (i - 72) (by omega) c hc
    rwa [show 72 + (i - 72) = i by omega] at this
  have := chk_spec 5 111 StP5 TrP5 15 96 c4 (i - 96) (by omega) c hc
  rwa [show 96 + (i - 96) = i by omega] at this

lemma av4 : a 4 = 23627 := by
  rw [a_dp 4 111 StP5 TrP5 (by decide +kernel) (by norm_num) cert5 (by decide +kernel)]
  decide +kernel

/-- The 168 feasible sets reached for values 0..5 (index 0: all pairs), 64 bits each. -/
def StP6 : ℕ := 0x4104100000000000010410000000000000041000000004100000000000000000400000000000000001000000000000000004000000000000000010000000000000820800000000000002080000000208200000000000000000800000000000000002000000000000000008000000000000010400000001041040000000000000000100000000000000000400000000820820800000000000000002000000080000000000000004300000000000000208e00000000000010413c0000000000082082f80000000001f4104100000000400000000000000001041041000000000080000000000000004000000000000000200000000000000003c82080000000200000000000000020800000000000000002082080000000000100000000000000008000000000000000071040000000100000000000000010400000000000001041000000000000000004104000000000000200000000000000000c2000000008000000000000000820000000000000082080000000000008208200000000000000000820000000000000000000000000000000100000007c000000000000007df41041000000000007d8618000000000001751400000000000004d20000000000000011000000000f000000000000000700000000000000030000000000000001000000000000002082082000000003c000000000000003cf00000000000003cf3c8208000000000000f30c00000000000002ca000000000000000900000000001c000000000000000c0000000000000004000000000000008208200000000000c30c3000000001c000000000000001c700000000000001c71c000000000001c71c710400000000000001c600000000000000050000000000003000000000000000100000000000000208200000000000030c300000000000038e3800000000c000000000000000c300000000000000c30c000000000000c30c300000000000c30c30c20000000000000003000000000000004000000000000008200000000000000c300000000000000e380000000000000f3c0000000040000000000000004100000000000000410400000000000041041000000000004104104000000000410410410000000820820820000000002000000000000000008000000000000000020000000000000000080000000000000000200000000c000000000000000430c30c300000000000c0000000000000000300000000000000000c0000000000000000300000000a0000000000000006380000000000000208e38e3800000000000380000000000000000e00000000000000003800000009000000000000000534000000000000030cf00000000000010413cf3c0000000000000f00000000000000003c000000088000000000000004b2000000000000028ae8000000000001861be0000000000082082fbe000000000000003e000000003fc30c300000000000be8a28000000000002792400000000000008e200000000000000210000000fc00000000000000000ff8e380000000000037d340000000000000cf200000000000000310000000bc000000000000007ff000000000000000003ff3c0000000000000efa000000000000003900000009c000000000000005f700000000000003cffc00000000000000000ffe000000000000003d00000008c000000000000004f300000000000002cbec000000000001c71ff000000000000000003f000000084000000000000004710000000000000249e40000000000014517d00000000000c30c3fc00000000fe082082000000007ffc30c3000000003cfff8e3800000001c71fff3c00000000c30c3ffe000000004104107f0000000fffffffff

/-- Their successors under the medians c = 0..5, 8 bits each at position i * 6 + c. -/
def TrP6 : ℕ := 0x766888827c75765d63827c75765262587c75933b767676767686857676767680847e7676767a837d7776764761574d7576765c827c75767651587c7593923476767676767f7e76767676797d7776767646574d75767676507c759392912d7676767676787776767676454d759392919026767676767644754276767676763c3b76767676363534767676302f2e2d76762a292827267676737271706f936a76767676767388827c7576a4a776767676a4a3a6767676a4a3a2a57676766766656493416076767693925f767676767667827c7576769d9f767676769d9c9e767676765b5a5993414056767693923a5576769392915476767676765b7c75767676989976767676764f4e9341403f4c7693923a394b76939291334a76939291904976767676764f75767676767676767676767643936a60564c3d93051e1d1c1b766867666564765d635b5a59765262584f4e764761574d4376a4a7a6a5a076a4a3a6a5a076a4a3a2a5a076a4a3a2a1a0748e88827c75934160564c3d93925f554b3793920418171676765c5b5a59767651584f4e767646574d4376769d9f9e9a76769d9c9e9a76769d9c9b9a696e88827c75696888827c75934140564c3d93923a554b37939291544a31939291031211767676504f4e767676454d437676769899967676769897965e6d63827c755e5d63827c755e5d5c827c759341403f4c3d93923a394b37939291334a3193929190492b93929190020c767676764443767676769594536c62587c75535262587c75535251587c75535251507c759341403f3e3d93923a393837939291333231939291902c2b939291908f25939291908f01068e88827c758d8c76767676878b85767676818a847e76767b89837d7776486b61574d75426a767676761f0588827c758786857676768180847e76767b7a837d7776484761574d754241607676763c3b5f7676761a1904827c7581807f7e76767b7a797d7776484746574d754241405676763c3b3a557676363534547676151413037c757b7a79787776484746454d754241403f4c763c3b3a394b76363534334a76302f2e2d4976100f0e0d027548474645447574737271706f696e676665645e6d635b5a59536c62584f4e486b61574d43426a60564c3d6968676665645e5d635b5a59535262584f4e484761574d43424160564c3d3c3b5f554b375e5d5c5b5a59535251584f4e484746574d43424140564c3d3c3b3a554b37363534544a31535251504f4e484746454d434241403f4c3d3c3b3a394b37363534334a31302f2e2d492b4847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a29282726250624232221201f051e1d1c1b1a1904181716151413031211100f0e0d020c0b0a09080701060504030201

/-- The transitions for values 0..5, checked by evaluation one block of states after
the other. -/
lemma cert6 : ∀ i < 168, ∀ c < 6, entry 8 TrP6 (i * 6 + c) < 168 ∧
    stepF 6 c (entry 64 StP6 i) = entry 64 StP6 (entry 8 TrP6 (i * 6 + c)) := by
  have c0 : chk 6 168 StP6 TrP6 20 0 = true := by decide +kernel
  have c1 : chk 6 168 StP6 TrP6 20 20 = true := by decide +kernel
  have c2 : chk 6 168 StP6 TrP6 20 40 = true := by decide +kernel
  have c3 : chk 6 168 StP6 TrP6 20 60 = true := by decide +kernel
  have c4 : chk 6 168 StP6 TrP6 20 80 = true := by decide +kernel
  have c5 : chk 6 168 StP6 TrP6 20 100 = true := by decide +kernel
  have c6 : chk 6 168 StP6 TrP6 20 120 = true := by decide +kernel
  have c7 : chk 6 168 StP6 TrP6 20 140 = true := by decide +kernel
  have c8 : chk 6 168 StP6 TrP6 8 160 = true := by decide +kernel
  intro i hi c hc
  by_cases h0 : i < 20
  · have := chk_spec 6 168 StP6 TrP6 20 0 c0 (i - 0) (by omega) c hc
    rwa [show 0 + (i - 0) = i by omega] at this
  by_cases h1 : i < 40
  · have := chk_spec 6 168 StP6 TrP6 20 20 c1 (i - 20) (by omega) c hc
    rwa [show 20 + (i - 20) = i by omega] at this
  by_cases h2 : i < 60
  · have := chk_spec 6 168 StP6 TrP6 20 40 c2 (i - 40) (by omega) c hc
    rwa [show 40 + (i - 40) = i by omega] at this
  by_cases h3 : i < 80
  · have := chk_spec 6 168 StP6 TrP6 20 60 c3 (i - 60) (by omega) c hc
    rwa [show 60 + (i - 60) = i by omega] at this
  by_cases h4 : i < 100
  · have := chk_spec 6 168 StP6 TrP6 20 80 c4 (i - 80) (by omega) c hc
    rwa [show 80 + (i - 80) = i by omega] at this
  by_cases h5 : i < 120
  · have := chk_spec 6 168 StP6 TrP6 20 100 c5 (i - 100) (by omega) c hc
    rwa [show 100 + (i - 100) = i by omega] at this
  by_cases h6 : i < 140
  · have := chk_spec 6 168 StP6 TrP6 20 120 c6 (i - 120) (by omega) c hc
    rwa [show 120 + (i - 120) = i by omega] at this
  by_cases h7 : i < 160
  · have := chk_spec 6 168 StP6 TrP6 20 140 c7 (i - 140) (by omega) c hc
    rwa [show 140 + (i - 140) = i by omega] at this
  have := chk_spec 6 168 StP6 TrP6 8 160 c8 (i - 160) (by omega) c hc
  rwa [show 160 + (i - 160) = i by omega] at this

lemma av5 : a 5 = 71278 := by
  rw [a_dp 5 168 StP6 TrP6 (by decide +kernel) (by norm_num) cert6 (by decide +kernel)]
  decide +kernel

/-- The 237 feasible sets reached for values 0..6 (index 0: all pairs), 64 bits each. -/
def StP7 : ℕ := 0x20408102000000000040810200000000000081020000000000000102000008100000000000000000200000000000000000400000000000000000800000000000000001000000000000000002000000000020408100000000000040810000000000000081000004081000000000000000002000000000000000004000000000000000008000000000000000010000000000002040800000000000004080000204081000000000000000002000000000000000004000000000000000008000000000000020400001020408100000000000000000200000000000000000400000810204081000000000000000002000100000000000000008300000000000000408700000000000020408f00000000001020409f0000000008102040bf00000001fa0408102000008000000000000000010204081020000000800000000000000040000000000000002000000000000000100000000000000001f20408100000400000000000000040800000000000000001020408100000000080000000000000004000000000000000200000000000000001e20408000020000000000000002040000000000000204080000000000000000102040800000000008000000000000000400000000000000001c2040000100000000000000010200000000000001020400000000000102040800000000000000001020400000000000080000000000000000182000008000000000000000810000000000000081020000000000008102040000000000810204080000000000000000102000000000000000000000000000000010000fc00000000000000fdfa0408102000000003f60c18300000000005ea1428000000000009d22400000000000011a20000000000000021000000f8000000000000007800000000000000380000000000000018000000000000000800000000000002040810204000007c000000000000007cf80000000000007cf9f20408100000000003e60c18000000000005ca140000000000000992000000000000001100000000f00000000000000070000000000000003000000000000000100000000000000408102040000000060c18306000003c000000000000003c780000000000003c78f000000000003c78f1e20408000000000003c60c000000000000058a00000000000000090000000000e00000000000000060000000000000002000000000000008102040000000000c183060000000000e1c387000001c000000000000001c380000000000001c387000000000001c3870e0000000001c3870e1c20400000000000003860000000000000005000000000000c00000000000000040000000000000102040000000000018306000000000001c387000000000001e3c7800000c000000000000000c180000000000000c183000000000000c183060000000000c183060c00000000c183060c182000000000000000300000000000000800000000000002040000000000000306000000000000038700000000000003c780000000000003e7c000004000000000000000408000000000000040810000000000004081020000000000408102040000000040810204080000004081020408100010204081020400000020000000000000000040000000000000000080000000000000000100000000000000000200000000000000000400001800000000000000083060c1830600000000600000000000000000c00000000000000001800000000000000003000000000000000006000014000000000000000c38000000000000040870e1c3870000000000e00000000000000001c00000000000000003800000000000000007000012000000000000000a34000000000000060c780000000000020408f1e3c7800000000001e00000000000000003c00000000000000007800011000000000000000932000000000000050a74000000000003060cf80000000001020409f3e7c0000000000003e00000000000000007c000108000000000000008b1000000000000048972000000000002850af4000000000183060df8000000008102040bf7e000000000000007e000003fe0c18306000000005fa1428500000000009f22448000000000011e24400000000000021c200000000000000410001fc000000000000000007fe1c3870000000000dfa3468000000000019f26400000000000031e2000000000000006100017c00000000000000fff800000000000000000ffe3c7800000000001dfa7400000000000039f2000000000000007100013c00000000000000bf780000000000007cfff000000000000000001ffe7c0000000000003dfa000000000000007900011c000000000000009f380000000000005cbf7000000000003c78ffe000000000000000003ffe000000000000007d00010c000000000000008f180000000000004c9f3000000000002c58bf60000000001c3870ffc000000000000000007f000104000000000000008708000000000000448f10000000000024489f2000000000142850bf400000000c183060ff800001fe04081020400000fffe0c18306000007cfffe1c387000003c78fffe3c7800001c3870fffe7c00000c183060fffe00000408102040ff0001ffffffffffff

/-- Their successors under the medians c = 0..6, 8 bits each at position i * 7 + c. -/
def TrP7 : ℕ := 0xa595c1bab3aca4a5888fbab3aca4a57b8e82b3aca4a56e8d8175aca4ce53a5a5a5a5a5a5bfbea5a5a5a5a5b8bdb6a5a5a5a5b1bcb5aea5a5a5aabbb4ada6a5a5618c807468a4a5a587bab3aca4a5a57a82b3aca4a5a56d8175aca4cecd4ba5a5a5a5a5a5b7b6a5a5a5a5a5b0b5aea5a5a5a5a9b4ada6a5a5a560807468a4a5a5a579b3aca4a5a5a56c75aca4cecdcc43a5a5a5a5a5a5afaea5a5a5a5a5a8ada6a5a5a5a55f7468a4a5a5a5a56baca4cecdcccb3ba5a5a5a5a5a5a7a6a5a5a5a5a55e68a4cecdcccbca33a5a5a5a5a5a55da45ba5a5a5a5a5a55453a5a5a5a5a54d4c4ba5a5a5a546454443a5a5a53f3e3d3c3ba5a5383736353433a5a5a2a1a09f9e9dce97a5a5a5a5a5a5a2c1bab3aca4a5e8eca5a5a5a5a5e8e7eba5a5a5a5e8e7e6eaa5a5a5e8e7e6e5e9a5a5a59493929190ce5a8ba5a5a5a5cecd8aa5a5a5a5a5a594bab3aca4a5a5dfe2a5a5a5a5a5dfdee1a5a5a5a5dfdedde0a5a5a5a586858483ce5a597fa5a5a5cecd527ea5a5a5cecdcc7da5a5a5a5a5a586b3aca4a5a5a5d8daa5a5a5a5a5d8d7d9a5a5a5a5a5787776ce5a595873a5a5cecd525172a5a5cecdcc4a71a5a5cecdcccb70a5a5a5a5a5a578aca4a5a5a5a5d3d4a5a5a5a5a5a56a69ce5a59585767a5cecd52515066a5cecdcc4a4965a5cecdcccb4264a5cecdcccbca63a5a5a5a5a5a56aa4a5a5a5a5a5a5a5a5a5a5a5a5a55cce978b7f736755ce062a29282726a5959493929190a5888f86858483a57b8e82787776a56e8d81756a69a5618c8074685ca5e8ecebeae9e3a5e8e7ebeae9e3a5e8e7e6eae9e3a5e8e7e6e5e9e3a5e8e7e6e5e4e3a3c8c1bab3aca4ce5a8b7f736755cecd8a7e72664ececd0523222120a5a58786858483a5a57a82787776a5a56d81756a69a5a5608074685ca5a5dfe2e1e0dba5a5dfdee1e0dba5a5dfdedde0dba5a5dfdedddcdb969cc1bab3aca49695c1bab3aca4ce5a597f736755cecd527e72664ececdcc7d716547cecdcc041c1b1aa5a5a579787776a5a5a56c756a69a5a5a55f74685ca5a5a5d8dad9d5a5a5a5d8d7d9d5a5a5a5d8d7d6d5899b8fbab3aca489888fbab3aca4898887bab3aca4ce5a5958736755cecd525172664ececdcc4a716547cecdcccb706440cecdcccb031514a5a5a5a56b6a69a5a5a5a55e685ca5a5a5a5d3d4d1a5a5a5a5d3d2d17c9a8e82b3aca47c7b8e82b3aca47c7b7a82b3aca47c7b7a79b3aca4ce5a5958576755cecd525150664ececdcc4a496547cecdcccb426440cecdcccbca6339cecdcccbca020ea5a5a5a5a55d5ca5a5a5a5a5d0cf6f998d8175aca46f6e8d8175aca46f6e6d8175aca46f6e6d6c75aca46f6e6d6c6baca4ce5a5958575655cecd5251504f4ececdcc4a494847cecdcccb424140cecdcccbca3a39cecdcccbcac932cecdcccbcac90107c8c1bab3aca4c7c6a5a5a5a5a5c0c5bea5a5a5a5b9c4bdb6a5a5a5b2c3bcb5aea5a5abc2bbb4ada6a562988c807468a45b97a5a5a5a5a52b06c1bab3aca4c0bfbea5a5a5a5b9b8bdb6a5a5a5b2b1bcb5aea5a5abaabbb4ada6a562618c807468a45b5a8ba5a5a5a554538aa5a5a5a5252405bab3aca4b9b8b7b6a5a5a5b2b1b0b5aea5a5abaaa9b4ada6a5626160807468a45b5a597fa5a5a55453527ea5a5a54d4c4b7da5a5a51f1e1d04b3aca4b2b1b0afaea5a5abaaa9a8ada6a56261605f7468a45b5a595873a5a55453525172a5a54d4c4b4a71a5a54645444370a5a51918171603aca4abaaa9a8a7a6a56261605f5e68a45b5a59585767a5545352515066a54d4c4b4a4965a5464544434264a53f3e3d3c3b63a5131211100f02a46261605f5e5da4a3a2a1a09f9e9d969c9493929190899b8f868584837c9a8e827877766f998d81756a6962988c8074685c5b978b7f7367559695949392919089888f868584837c7b8e827877766f6e8d81756a6962618c8074685c5b5a8b7f73675554538a7e72664e898887868584837c7b7a827877766f6e6d81756a696261608074685c5b5a597f7367555453527e72664e4d4c4b7d7165477c7b7a797877766f6e6d6c756a696261605f74685c5b5a59587367555453525172664e4d4c4b4a716547464544437064406f6e6d6c6b6a696261605f5e685c5b5a59585767555453525150664e4d4c4b4a496547464544434264403f3e3d3c3b63396261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a39383736353433320731302f2e2d2c2b062a29282726252405232221201f1e1d041c1b1a19181716031514131211100f020e0d0c0b0a09080107060504030201

/-- The transitions for values 0..6, checked by evaluation one block of states after
the other. -/
lemma cert7 : ∀ i < 237, ∀ c < 7, entry 8 TrP7 (i * 7 + c) < 237 ∧
    stepF 7 c (entry 64 StP7 i) = entry 64 StP7 (entry 8 TrP7 (i * 7 + c)) := by
  have c0 : chk 7 237 StP7 TrP7 17 0 = true := by decide +kernel
  have c1 : chk 7 237 StP7 TrP7 17 17 = true := by decide +kernel
  have c2 : chk 7 237 StP7 TrP7 17 34 = true := by decide +kernel
  have c3 : chk 7 237 StP7 TrP7 17 51 = true := by decide +kernel
  have c4 : chk 7 237 StP7 TrP7 17 68 = true := by decide +kernel
  have c5 : chk 7 237 StP7 TrP7 17 85 = true := by decide +kernel
  have c6 : chk 7 237 StP7 TrP7 17 102 = true := by decide +kernel
  have c7 : chk 7 237 StP7 TrP7 17 119 = true := by decide +kernel
  have c8 : chk 7 237 StP7 TrP7 17 136 = true := by decide +kernel
  have c9 : chk 7 237 StP7 TrP7 17 153 = true := by decide +kernel
  have c10 : chk 7 237 StP7 TrP7 17 170 = true := by decide +kernel
  have c11 : chk 7 237 StP7 TrP7 17 187 = true := by decide +kernel
  have c12 : chk 7 237 StP7 TrP7 17 204 = true := by decide +kernel
  have c13 : chk 7 237 StP7 TrP7 16 221 = true := by decide +kernel
  intro i hi c hc
  by_cases h0 : i < 17
  · have := chk_spec 7 237 StP7 TrP7 17 0 c0 (i - 0) (by omega) c hc
    rwa [show 0 + (i - 0) = i by omega] at this
  by_cases h1 : i < 34
  · have := chk_spec 7 237 StP7 TrP7 17 17 c1 (i - 17) (by omega) c hc
    rwa [show 17 + (i - 17) = i by omega] at this
  by_cases h2 : i < 51
  · have := chk_spec 7 237 StP7 TrP7 17 34 c2 (i - 34) (by omega) c hc
    rwa [show 34 + (i - 34) = i by omega] at this
  by_cases h3 : i < 68
  · have := chk_spec 7 237 StP7 TrP7 17 51 c3 (i - 51) (by omega) c hc
    rwa [show 51 + (i - 51) = i by omega] at this
  by_cases h4 : i < 85
  · have := chk_spec 7 237 StP7 TrP7 17 68 c4 (i - 68) (by omega) c hc
    rwa [show 68 + (i - 68) = i by omega] at this
  by_cases h5 : i < 102
  · have := chk_spec 7 237 StP7 TrP7 17 85 c5 (i - 85) (by omega) c hc
    rwa [show 85 + (i - 85) = i by omega] at this
  by_cases h6 : i < 119
  · have := chk_spec 7 237 StP7 TrP7 17 102 c6 (i - 102) (by omega) c hc
    rwa [show 102 + (i - 102) = i by omega] at this
  by_cases h7 : i < 136
  · have := chk_spec 7 237 StP7 TrP7 17 119 c7 (i - 119) (by omega) c hc
    rwa [show 119 + (i - 119) = i by omega] at this
  by_cases h8 : i < 153
  · have := chk_spec 7 237 StP7 TrP7 17 136 c8 (i - 136) (by omega) c hc
    rwa [show 136 + (i - 136) = i by omega] at this
  by_cases h9 : i < 170
  · have := chk_spec 7 237 StP7 TrP7 17 153 c9 (i - 153) (by omega) c hc
    rwa [show 153 + (i - 153) = i by omega] at this
  by_cases h10 : i < 187
  · have := chk_spec 7 237 StP7 TrP7 17 170 c10 (i - 170) (by omega) c hc
    rwa [show 170 + (i - 170) = i by omega] at this
  by_cases h11 : i < 204
  · have := chk_spec 7 237 StP7 TrP7 17 187 c11 (i - 187) (by omega) c hc
    rwa [show 187 + (i - 187) = i by omega] at this
  by_cases h12 : i < 221
  · have := chk_spec 7 237 StP7 TrP7 17 204 c12 (i - 204) (by omega) c hc
    rwa [show 204 + (i - 204) = i by omega] at this
  have := chk_spec 7 237 StP7 TrP7 16 221 c13 (i - 221) (by omega) c hc
  rwa [show 221 + (i - 221) = i by omega] at this

lemma av6 : a 6 = 181885 := by
  rw [a_dp 6 237 StP7 TrP7 (by decide +kernel) (by norm_num) cert7 (by decide +kernel)]
  decide +kernel

/-! ### The pattern counts -/

/-- y(0..6) is the array of medians of three adjacent elements of some array of naturals. -/
def good (y : Fin 7 → ℕ) : Prop := ∃ x : Fin 9 → ℕ, realizes x y

noncomputable instance : DecidablePred good := Classical.decPred _

/-- A strictly monotone map of ℕ has a monotone left inverse. -/
lemma left_inv (f : ℕ → ℕ) (hf : StrictMono f) :
    ∃ g : ℕ → ℕ, Monotone g ∧ ∀ t, g (f t) = t := by
  refine ⟨fun s => Nat.findGreatest (fun t => f t ≤ s) s, fun s s' hs => ?_, fun t => ?_⟩
  · show Nat.findGreatest (fun t => f t ≤ s) s ≤ Nat.findGreatest (fun t => f t ≤ s') s'
    rcases Nat.eq_zero_or_pos (Nat.findGreatest (fun t => f t ≤ s) s) with h | h
    · rw [h]
      exact Nat.zero_le _
    · have h1 := (Nat.findGreatest_eq_iff.1 rfl).2.1 h.ne'
      exact Nat.le_findGreatest ((Nat.findGreatest_le s).trans hs) (h1.trans hs)
  · show Nat.findGreatest (fun u => f u ≤ f t) (f t) = t
    rw [Nat.findGreatest_eq_iff]
    exact ⟨hf.id_le t, fun _ => le_refl _, fun u hu _ => not_le.2 (hf hu)⟩

/-- Arrays of medians stay arrays of medians under strictly monotone relabeling, and back
through a monotone left inverse. -/
lemma inv : Invariant good := by
  intro f hf y
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨g, hg, hgf⟩ := left_inv f hf
    refine ⟨fun j => g (x j), fun i => ?_⟩
    rw [← med_map hg, hx i]
    exact hgf (y i)
  · rintro ⟨x, hx⟩
    refine ⟨fun j => f (x j), fun i => ?_⟩
    show med (f _) (f _) (f _) = f (y i)
    rw [← med_map hf.monotone, hx i]

/-- The count is the general count of the property: a realizing array can be cut at n. -/
lemma ha (n : ℕ) : a n = count good n := by
  unfold a count
  congr 1
  apply Finset.filter_congr
  intro y _
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨fun j => (x j : ℕ), (medians_iff x y).1 hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨fun j => ⟨min (x j) n, by omega⟩, (medians_iff _ y).2 (fun i => ?_)⟩
    have hmono : Monotone (fun t : ℕ => min t n) := fun s t h => min_le_min_right n h
    show med (min (x _) n) (min (x _) n) (min (x _) n) = (y i : ℕ)
    rw [← med_map hmono, hx i]
    exact min_eq_left (Nat.lt_succ_iff.1 (y i).isLt)

lemma lin (p : ℕ → ℕ) (h0 : p 0 = 0) (e0 : 1 = ∑ j ∈ Finset.range (7 + 1), (0 + 1).choose j * p j)
    (e1 : 88 = ∑ j ∈ Finset.range (7 + 1), (1 + 1).choose j * p j) (e2 : 1071 = ∑ j ∈ Finset.range
    (7 + 1), (2 + 1).choose j * p j) (e3 : 6130 = ∑ j ∈ Finset.range (7 + 1), (3 + 1).choose j * p
    j) (e4 : 23627 = ∑ j ∈ Finset.range (7 + 1), (4 + 1).choose j * p j) (e5 : 71278 = ∑ j ∈
    Finset.range (7 + 1), (5 + 1).choose j * p j) (e6 : 181885 = ∑ j ∈ Finset.range (7 + 1), (6 +
    1).choose j * p j) : p 0 = 0 ∧ p 1 = 1 ∧ p 2 = 86 ∧ p 3 = 810 ∧ p 4 = 2370 ∧ p 5 = 2812 ∧ p 6 =
    1360 ∧ p 7 = 200 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e0 e1 e2 e3 e4 e5 e6
  norm_num [Nat.choose] at e0 e1 e2 e3 e4 e5 e6
  omega

lemma pcv : pc good 0 = 0 ∧ pc good 1 = 1 ∧ pc good 2 = 86 ∧ pc good 3 = 810 ∧ pc good 4 = 2370 ∧ pc
    good 5 = 2812 ∧ pc good 6 = 1360 ∧ pc good 7 = 200 :=
  lin (pc good) (pc_zero (by norm_num)) ((av0).symm.trans ((ha 0).trans (count_eq inv 0)))
    ((av1).symm.trans ((ha 1).trans (count_eq inv 1))) ((av2).symm.trans ((ha 2).trans (count_eq inv
    2))) ((av3).symm.trans ((ha 3).trans (count_eq inv 3))) ((av4).symm.trans ((ha 4).trans
    (count_eq inv 4))) ((av5).symm.trans ((ha 5).trans (count_eq inv 5))) ((av6).symm.trans ((ha
    6).trans (count_eq inv 6)))

lemma ch2 (n : ℕ) : ((n + 1).choose 2 : ℚ) = (n + 1) * n / 2 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 2 = (m + 1).choose 1 + (m + 1).choose 2 :=
      Nat.choose_succ_succ' (m + 1) 1
    rw [h, Nat.cast_add, ih, Nat.choose_one_right]
    push_cast
    ring

lemma ch3 (n : ℕ) : ((n + 1).choose 3 : ℚ) = (n + 1) * n * (n - 1) / 6 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 3 = (m + 1).choose 2 + (m + 1).choose 3 :=
      Nat.choose_succ_succ' (m + 1) 2
    rw [h, Nat.cast_add, ih, ch2]
    push_cast
    ring

lemma ch4 (n : ℕ) : ((n + 1).choose 4 : ℚ) = (n + 1) * n * (n - 1) * (n - 2) / 24 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 4 = (m + 1).choose 3 + (m + 1).choose 4 :=
      Nat.choose_succ_succ' (m + 1) 3
    rw [h, Nat.cast_add, ih, ch3]
    push_cast
    ring

lemma ch5 (n : ℕ) : ((n + 1).choose 5 : ℚ) = (n + 1) * n * (n - 1) * (n - 2) * (n - 3) / 120 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 5 = (m + 1).choose 4 + (m + 1).choose 5 :=
      Nat.choose_succ_succ' (m + 1) 4
    rw [h, Nat.cast_add, ih, ch4]
    push_cast
    ring

lemma ch6 (n : ℕ) : ((n + 1).choose 6 : ℚ) = (n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 720 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 6 = (m + 1).choose 5 + (m + 1).choose 6 :=
      Nat.choose_succ_succ' (m + 1) 5
    rw [h, Nat.cast_add, ih, ch5]
    push_cast
    ring

lemma ch7 (n : ℕ) : ((n + 1).choose 7 : ℚ) = (n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) / 5040 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 7 = (m + 1).choose 6 + (m + 1).choose 7 :=
      Nat.choose_succ_succ' (m + 1) 6
    rw [h, Nat.cast_add, ih, ch6]
    push_cast
    ring

/-- The closed form a(n) = Sum_j c_j binomial(n+1, j). -/
lemma a_eq (n : ℕ) : (a n : ℚ) = 1 * (n + 1) + 86 * ((n + 1) * n / 2) + 810 * ((n + 1) * n * (n -
    1) / 6) + 2370 * ((n + 1) * n * (n - 1) * (n - 2) / 24) + 2812 * ((n + 1) * n * (n - 1) * (n -
    2) * (n - 3) / 120) + 1360 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 720) + 200 *
    ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) / 5040) := by
  rw [ha, count_eq inv n]
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := pcv
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, p0, p1, p2, p3, p4, p5, p6, p7]
  push_cast
  simp only [ch2, ch3, ch4, ch5, ch6, ch7]
  simp
  ring

/-- Hardin's empirical formula, for all n. -/
theorem empirical (n : ℕ) : (a n : ℚ) = (5 / 126) * n ^ 7 + (4 / 3) * n ^ 6 + (829 / 90) * n ^ 5 +
    (93 / 4) * n ^ 4 + (509 / 18) * n ^ 3 + (221 / 12) * n ^ 2 + (453 / 70) * n + 1 := by
  rw [a_eq]
  ring

/-- Controls: the entry's data a(1..26). -/
theorem controls : a 1 = 88 ∧ a 2 = 1071 ∧ a 3 = 6130 ∧ a 4 = 23627 ∧ a 5 = 71278 ∧ a 6 = 181885 ∧ a
    7 = 410828 ∧ a 8 = 845517 ∧ a 9 = 1617004 ∧ a 10 = 2913955 ∧ a 11 = 4999182 ∧ a 12 = 8228935 ∧ a
    13 = 13075154 ∧ a 14 = 20150881 ∧ a 15 = 30239032 ∧ a 16 = 44324729 ∧ a 17 = 63631392 ∧ a 18 =
    89660791 ∧ a 19 = 124237258 ∧ a 20 = 169556259 ∧ a 21 = 228237526 ∧ a 22 = 303382949 ∧ a 23 =
    398639428 ∧ a 24 = 518266885 ∧ a 25 = 667211636 ∧ a 26 = 851185323 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩ <;>
  · rw [← Nat.cast_inj (R := ℚ), a_eq]
    norm_num

/-- The patterns with more than 7 values fail the property. -/
lemma hD : ∀ j, 7 < j → pc good j = 0 := fun j hj => pc_eq_zero j hj

/-- Barker's recurrence, from the general recurrence of order 8. -/
theorem recurrence' (n : ℕ) (hn : 8 < n) :
    (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) -
      28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 8 := ⟨n - 8, by omega⟩
  have h := recurrence inv 7 hD q
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero] at h
  norm_num [Nat.choose] at h
  simp only [show q + 8 - 1 = q + 7 by omega, show q + 8 - 2 = q + 6 by omega, show q + 8 - 3 = q +
    5 by omega, show q + 8 - 4 = q + 4 by omega, show q + 8 - 5 = q + 3 by omega, show q + 8 - 6 =
    q + 2 by omega, show q + 8 - 7 = q + 1 by omega, show q + 8 - 8 = q by omega, ha]
  linarith

/-- Barker's g.f., from the general g.f. -/
theorem gf' : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      X * (88 + 367 * X + 26 * X ^ 2 - 353 * X ^ 3 + 86 * X ^ 4 - 21 * X ^ 5 + 8 * X ^ 6 - X ^ 7) := by
  rw [show (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) =
      (fun n => if n = 0 then (0 : ℤ) else (count good n : ℤ)) from funext fun n => by rw [ha],
    gf_offset inv 7 hD, count_zero inv (by norm_num)]
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := pcv
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, p0, p1, p2, p3, p4, p5, p6, p7]
  push_cast
  ring

/-- Both of Barker's conjectures: the g.f. and the recurrence. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      X * (88 + 367 * X + 26 * X ^ 2 - 353 * X ^ 3 + 86 * X ^ 4 - 21 * X ^ 5 + 8 * X ^ 6 - X ^ 7) ∧
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) :=
  ⟨gf', recurrence'⟩

end OMA.S_oeis_a228744

theorem OMA.solution : type_of% @OMA.S_oeis_a228744.main :=
  OMA.S_oeis_a228744.conjecture
