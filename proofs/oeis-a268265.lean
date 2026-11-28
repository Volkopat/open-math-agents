import OMAStatements.S_oeis_a268265

namespace OMA.S_oeis_a268265

open PowerSeries






section Patterns

variable {k : ℕ} (P : (Fin k → ℕ) → Prop) [DecidablePred P]

/-- The number of surjective patterns g : Fin k → Fin j with the property. -/
def pc (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun g : Fin k → Fin j => Function.Surjective g ∧ P (fun i => (g i : ℕ)))).card

variable {P}

/-- The arrays with image S correspond to the surjective patterns onto Fin S.card. -/
theorem fiber_card (hP : ∀ (m : ℕ) (e₁ e₂ : Fin m ↪o ℕ) (g : Fin k → Fin m),
      P (fun i => e₁ (g i)) ↔ P (fun i => e₂ (g i)))
    {n : ℕ} (S : Finset (Fin (n + 1))) :
    ((Finset.univ.filter (fun x : Fin k → Fin (n + 1) => P (fun i => (x i : ℕ)))).filter
      (fun x => Finset.univ.image x = S)).card = pc P S.card := by
  symm
  unfold pc
  apply Finset.card_bij (fun g _ => fun i => S.orderEmbOfFin rfl (g i))
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨hs, hp⟩ := hg
    refine ⟨?_, ?_⟩
    · have h := hP S.card ((S.orderEmbOfFin rfl).trans (Fin.valOrderEmb (n + 1)))
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
      · have h := hP S.card ((S.orderEmbOfFin rfl).trans (Fin.valOrderEmb (n + 1)))
          (Fin.valOrderEmb S.card) (fun i => (S.orderIsoOfFin rfl).symm ⟨x i, hmem i⟩)
        simp only [RelEmbedding.trans_apply, Fin.valOrderEmb_apply, hx_eq] at h
        exact h.1 hp
    · funext i
      exact hx_eq i

/-- The count of arrays as a sum over pattern sizes. -/
theorem count_eq (hP : ∀ (m : ℕ) (e₁ e₂ : Fin m ↪o ℕ) (g : Fin k → Fin m),
      P (fun i => e₁ (g i)) ↔ P (fun i => e₂ (g i))) (n : ℕ) :
    (Finset.univ.filter (fun x : Fin k → Fin (n + 1) => P (fun i => (x i : ℕ)))).card =
      ∑ j ∈ Finset.range (k + 1), (n + 1).choose j * pc P j := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin k → Fin (n + 1) => Finset.univ.image x)
    (t := Finset.univ) (by intro x _; simp)]
  refine (Finset.sum_congr rfl (fun S _ => fiber_card hP S)).trans ?_
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card (f := pc P)]
  simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hz : ∀ j, k < j → pc P j = 0 := by
    intro j hj
    unfold pc
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hs, -⟩
    have := Fintype.card_le_of_surjective g hs
    simp only [Fintype.card_fin] at this
    omega
  have e1 : ∑ m ∈ Finset.range (n + 1 + 1), (n + 1).choose m * pc P m =
      ∑ m ∈ Finset.range (n + k + 2), (n + 1).choose m * pc P m := by
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro m _ hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  have e2 : ∑ m ∈ Finset.range (k + 1), (n + 1).choose m * pc P m =
      ∑ m ∈ Finset.range (n + k + 2), (n + 1).choose m * pc P m := by
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro m _ hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [hz m (by omega), mul_zero]
  rw [e1, e2]

end Patterns

section Head

variable {k : ℕ} (P : (Fin (k + 1) → ℕ) → Prop) [DecidablePred P]

/-- Splitting a count of functions on Fin (k + 1) by the value at 0. -/
theorem card_by_head {j : ℕ} (Q : (Fin (k + 1) → Fin j) → Prop) [DecidablePred Q] :
    (Finset.univ.filter Q).card =
      ∑ v : Fin j, (Finset.univ.filter (fun h : Fin k → Fin j => Q (Fin.cons v h))).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g : Fin (k + 1) → Fin j => g 0) (t := Finset.univ)
    (by intro x _; simp)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  symm
  apply Finset.card_bij (fun h _ => (Fin.cons v h : Fin (k + 1) → Fin j))
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    exact ⟨hh, by simp⟩
  · intro h₁ _ h₂ _ e
    simpa using congrArg Fin.tail e
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨hq, h0⟩ := hg
    refine ⟨Fin.tail g, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← h0, Fin.cons_self_tail]
      exact hq
    · show Fin.cons v (Fin.tail g) = g
      rw [← h0, Fin.cons_self_tail]

/-- The number of surjective patterns g : Fin (k + 1) → Fin j with the property and g 0 = v. -/
def pcs (j : ℕ) (v : Fin j) : ℕ :=
  (Finset.univ.filter (fun h : Fin k → Fin j =>
    Function.Surjective (Fin.cons v h : Fin (k + 1) → Fin j) ∧
      P (fun i => ((Fin.cons v h : Fin (k + 1) → Fin j) i : ℕ)))).card

theorem pc_succ (j : ℕ) : pc P j = ∑ v : Fin j, pcs P j v := by
  unfold pc pcs
  exact card_by_head (fun g : Fin (k + 1) → Fin j => Function.Surjective g ∧ P (fun i => (g i : ℕ)))

end Head

section RGSCount

/-- f 0 + ... + f (n - 1), by recursion on n. -/
def sumN (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumN f n + f n

lemma sumN_eq (f : ℕ → ℕ) (n : ℕ) : sumN f n = ∑ v ∈ Finset.range n, f v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumN, ih, Finset.sum_range_succ]

/-- okG p m l: after an entry p, with the values 0..m-1 introduced as repeated values, the
repeated values of p :: l keep the sequential order. -/
def okG : ℕ → ℕ → List ℕ → Bool
  | _, _, [] => true
  | p, m, v :: t => if v = p then (decide (v ≤ m) && okG v (max m (v + 1)) t) else okG v m t

lemma okG_iff : ∀ (l : List ℕ) (p m : ℕ), okG p m l = rgsB m (repsL (p :: l))
  | [], p, m => by simp [okG, repsL, rgsB]
  | v :: t, p, m => by
    have ih := okG_iff t
    by_cases h : v = p
    · subst h
      simp only [okG, if_true, repsL, rgsB, ih]
    · have h' : p ≠ v := fun e => h e.symm
      simp only [okG, if_neg h, repsL, if_neg h', ih]

/-- The number of h : Fin L → Fin N continuing an entry p with m values introduced that pass okG.
The kernel evaluates each value once. -/
def dpG (N : ℕ) : (L p m : ℕ) → ℕ
  | 0, _, _ => 1
  | L + 1, p, m => sumN (fun v =>
      if v = p then (if v ≤ m then dpG N L v (max m (v + 1)) else 0) else dpG N L v m) N

theorem dpG_eq (N : ℕ) : ∀ (L p m : ℕ), dpG N L p m =
    (Finset.univ.filter (fun h : Fin L → Fin N => okG p m (List.ofFn (fun i => (h i : ℕ))) = true)).card
  | 0, p, m => by
    rw [dpG]
    have hu : (Finset.univ : Finset (Fin 0 → Fin N)) = {Fin.elim0} := by
      ext g
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i
      exact i.elim0
    rw [hu, Finset.filter_singleton]
    simp [okG]
  | L + 1, p, m => by
    rw [dpG, sumN_eq, ← Fin.sum_univ_eq_sum_range (fun v => if v = p then (if v ≤ m then
      dpG N L v (max m (v + 1)) else 0) else dpG N L v m) N, card_by_head]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have e : ∀ h : Fin L → Fin N, List.ofFn (fun i => ((Fin.cons v h : Fin (L + 1) → Fin N) i : ℕ)) =
        (v : ℕ) :: List.ofFn (fun i => (h i : ℕ)) := fun h => by
      rw [List.ofFn_succ]
      simp
    by_cases hv : (v : ℕ) = p
    · rw [if_pos hv]
      by_cases hr : (v : ℕ) ≤ m
      · rw [if_pos hr, dpG_eq N L v (max m (v + 1))]
        congr 1
        ext h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, e, okG, if_pos hv, hr,
          decide_true, Bool.true_and]
      · rw [if_neg hr]
        symm
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro h _ hc
        simp only [e, okG, if_pos hv, Bool.and_eq_true, decide_eq_true_eq] at hc
        exact hr hc.1
    · rw [if_neg hv, dpG_eq N L v m]
      congr 1
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, e, okG, if_neg hv]

/-- The arrays whose repeated values are introduced in sequential order, through dpG, split by the
first entry. -/
theorem count_eq_dpG (k n : ℕ) :
    (Finset.univ.filter (fun x : Fin (k + 1) → Fin (n + 1) =>
      rgsB 0 (repsL (List.ofFn (fun i => (x i : ℕ)))) = true)).card =
      sumN (fun v => dpG (n + 1) k v 0) (n + 1) := by
  rw [sumN_eq, ← Fin.sum_univ_eq_sum_range (fun v => dpG (n + 1) k v 0) (n + 1), card_by_head]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [dpG_eq]
  congr 1
  ext h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [List.ofFn_succ, okG_iff]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-! The count does not depend on the values themselves, only on how each compares with the
number m of values introduced: below m (0), equal to m (1) or above (2). -/

def ty (v m : ℕ) : ℕ := if v < m then 0 else if v = m then 1 else 2

/-- The same count for values 0..n, by type, as an integer polynomial in n. -/
def fZ (n : ℤ) : (L t m : ℕ) → ℤ
  | 0, _, _ => 1
  | L + 1, t, m =>
      (if t = 0 then fZ n L 0 m else if t = 1 then fZ n L 0 (m + 1) else 0) +
      ((m : ℤ) - (if t = 0 then 1 else 0)) * fZ n L 0 m +
      (1 - (if t = 1 then 1 else 0)) * fZ n L 1 m +
      (n - m - (if t = 2 then 1 else 0)) * fZ n L 2 m

lemma sum_ty (g : ℕ → ℤ) (m n : ℕ) (hm : m ≤ n) :
    ∑ v ∈ Finset.range (n + 1), g (ty v m) = m * g 0 + g 1 + ((n : ℤ) - m) * g 2 := by
  induction n, hm using Nat.le_induction with
  | base =>
    rw [Finset.sum_range_succ]
    have h0 : ∑ v ∈ Finset.range m, g (ty v m) = ∑ v ∈ Finset.range m, g 0 :=
      Finset.sum_congr rfl (fun v hv => by
        rw [Finset.mem_range] at hv
        simp [ty, hv])
    rw [h0, Finset.sum_const, Finset.card_range]
    simp [ty]
  | succ n hmn ih =>
    rw [Finset.sum_range_succ, ih]
    have : ty (n + 1) m = 2 := by
      simp only [ty]
      rw [if_neg (by omega), if_neg (by omega)]
    rw [this]
    push_cast
    ring

theorem dpG_fZ (n : ℕ) : ∀ (L p m : ℕ), p ≤ n → m + L ≤ n →
    (dpG (n + 1) L p m : ℤ) = fZ n L (ty p m) m
  | 0, p, m, _, _ => by simp [dpG, fZ]
  | L + 1, p, m, hp, hm => by
    rw [dpG, sumN_eq]
    have hsplit : ∀ g : ℕ → ℕ, ∑ v ∈ Finset.range (n + 1), (if v = p then g v else dpG (n + 1) L v m) =
        g p + ∑ v ∈ Finset.range (n + 1), dpG (n + 1) L v m - dpG (n + 1) L p m := by
      intro g
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 (by omega : p < n + 1)),
        ← Finset.add_sum_erase _ _ (Finset.mem_range.2 (by omega : p < n + 1)), if_pos rfl]
      rw [Finset.sum_congr rfl (fun v hv => if_neg (Finset.ne_of_mem_erase hv))]
      omega
    rw [hsplit (fun v => if v ≤ m then dpG (n + 1) L v (max m (v + 1)) else 0)]
    have hle : dpG (n + 1) L p m ≤ ∑ v ∈ Finset.range (n + 1), dpG (n + 1) L v m :=
      Finset.single_le_sum (f := fun v => dpG (n + 1) L v m) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (show p < n + 1 by omega))
    push_cast [Nat.cast_sub (le_add_left hle)]
    rw [Finset.sum_congr rfl (fun v hv => dpG_fZ n L v m (by rw [Finset.mem_range] at hv; omega)
      (by omega)), dpG_fZ n L p m hp (by omega)]
    rw [show (∑ v ∈ Finset.range (n + 1), fZ n L (ty v m) m) =
      m * fZ n L 0 m + fZ n L 1 m + ((n : ℤ) - m) * fZ n L 2 m from
      sum_ty (fun t => fZ n L t m) m n (by omega)]
    rw [fZ]
    by_cases h0 : p < m
    · have ht : ty p m = 0 := by simp [ty, h0]
      rw [if_pos h0.le, show max m (p + 1) = m by omega, dpG_fZ n L p m hp (by omega), ht]
      simp
      ring
    · by_cases h1 : p = m
      · subst h1
        have ht : ty p p = 1 := by simp [ty]
        have ht' : ty p (p + 1) = 0 := by simp [ty]
        rw [if_pos le_rfl, show max p (p + 1) = p + 1 by omega, dpG_fZ n L p (p + 1) hp (by omega),
          ht, ht']
        simp
        ring
      · have ht : ty p m = 2 := by
          simp only [ty]
          rw [if_neg h0, if_neg h1]
        rw [if_neg (by omega), ht]
        simp
        ring

end RGSCount

lemma a_dp (n : ℕ) : a n = sumN (fun v => dpG (n + 1) 6 v 0) (n + 1) := by
  unfold a good
  exact count_eq_dpG 6 n

theorem a_fZ (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℤ) = fZ n 6 1 0 + n * fZ n 6 2 0 := by
  rw [a_dp, sumN_eq]
  push_cast
  rw [Finset.sum_congr rfl (fun v hv => dpG_fZ n 6 v 0 (by rw [Finset.mem_range] at hv; omega)
    (by omega)), sum_ty (fun t => fZ n 6 t 0) 0 n (Nat.zero_le _)]
  push_cast
  ring

/-- Hardin's polynomial, for n ≥ 6. -/
theorem poly_large (n : ℕ) (hn : 6 ≤ n) : (a n : ℤ) = (n : ℤ) ^ 7 + (n : ℤ) ^ 6 + 6 * (n : ℤ) ^ 5 + 5 * (n : ℤ) ^ 4 + 20 * (n : ℤ) ^ 3 + 12 * (n : ℤ) ^ 2 + 20 * (n : ℤ) + 5 := by
  rw [a_fZ n hn]
  simp [fZ]
  ring

/-- The values a(0..T), from the recursion. -/
theorem small : a 0 = 1 ∧ a 1 = 65 ∧ a 2 = 717 ∧ a 3 = 5492 ∧ a 4 = 29461 ∧ a 5 = 118530 ∧ a 6 =
    384605 ∧ a 7 = 1061632 ∧ a 8 = 2587557 ∧ a 9 = 5717246 ∧ a 10 = 11671405 ∧ a 11 = 22326540 ∧ a
    12 = 40450997 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [a_dp]; decide +kernel)

/-- Hardin's polynomial, for n ≥ 2. -/
theorem poly_all (n : ℕ) (hn : 2 ≤ n) : (a n : ℤ) = (n : ℤ) ^ 7 + (n : ℤ) ^ 6 + 6 * (n : ℤ) ^ 5 + 5 * (n : ℤ) ^ 4 + 20 * (n : ℤ) ^ 3 + 12 * (n : ℤ) ^ 2 + 20 * (n : ℤ) + 5 := by
  rcases Nat.lt_or_ge n 6 with h | h
  · obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := small
    interval_cases n <;> simp only [v2, v3, v4, v5] <;> norm_num
  · exact poly_large n h

/-- Barker's recurrence, for n > 9. -/
theorem recurrence (n : ℕ) (hn : 9 < n) :
    (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 10 := ⟨n - 10, by omega⟩
  simp only [show q + 10 - 1 = q + 9 by omega, show q + 10 - 2 = q + 8 by omega, show q + 10 - 3 =
    q + 7 by omega, show q + 10 - 4 = q + 6 by omega, show q + 10 - 5 = q + 5 by omega, show q +
    10 - 6 = q + 4 by omega, show q + 10 - 7 = q + 3 by omega, show q + 10 - 8 = q + 2 by omega]
  rw [poly_all (q + 10) (by omega), poly_all (q + 9) (by omega), poly_all (q + 8) (by omega),
    poly_all (q + 7) (by omega), poly_all (q + 6) (by omega), poly_all (q + 5) (by omega), poly_all
    (q + 4) (by omega), poly_all (q + 3) (by omega), poly_all (q + 2) (by omega)]
  push_cast
  ring

/-- Barker's g.f., as A(x) (1 - x)^8 = N(x) in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
    X * (65 + 197 * X + 1576 * X ^ 2 + 1961 * X ^ 3 + 1016 * X ^ 4 + 271 * X ^ 5 - 76 * X ^ 6 + 35 * X ^ 7 - 5 * X ^ 8) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 8 =
      A - C 8 * (A * X ^ 1) + C 28 * (A * X ^ 2) - C 56 * (A * X ^ 3) + C 70 * (A * X ^ 4) - C 56 *
        (A * X ^ 5) + C 28 * (A * X ^ 6) - C 8 * (A * X ^ 7) + A * X ^ 8 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (65 + 197 * X + 1576 * X ^ 2 + 1961 * X ^ 3 + 1016 * X ^ 4 + 271 * X ^ 5 - 76 * X ^ 6 + 35 * X ^ 7 - 5 * X ^ 8) : ℤ⟦X⟧) =
      X ^ 1 * C 65 + X ^ 2 * C 197 + X ^ 3 * C 1576 + X ^ 4 * C 1961 + X ^ 5 * C 1016 + X ^ 6 * C
        271 - X ^ 7 * C 76 + X ^ 8 * C 35 - X ^ 9 * C 5 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v := small
  rcases Nat.lt_or_ge n 10 with hn | hn
  · interval_cases n <;> simp_all
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 10 := ⟨n - 10, by omega⟩
    have h := recurrence (q + 10) (by omega)
    simp only [show q + 10 - 1 = q + 9 by omega, show q + 10 - 2 = q + 8 by omega, show q + 10 - 3 =
      q + 7 by omega, show q + 10 - 4 = q + 6 by omega, show q + 10 - 5 = q + 5 by omega, show q +
      10 - 6 = q + 4 by omega, show q + 10 - 7 = q + 3 by omega, show q + 10 - 8 = q + 2 by omega]
      at h ⊢
    simp only [show ¬ q + 10 = 0 by omega, show ¬ q + 9 = 0 by omega, show ¬ q + 8 = 0 by omega,
      show ¬ q + 7 = 0 by omega, show ¬ q + 6 = 0 by omega, show ¬ q + 5 = 0 by omega, show ¬ q +
      4 = 0 by omega, show ¬ q + 3 = 0 by omega, show ¬ q + 2 = 0 by omega, show 1 ≤ q + 10 by
      omega, show 2 ≤ q + 10 by omega, show 3 ≤ q + 10 by omega, show 4 ≤ q + 10 by omega, show 5 ≤
      q + 10 by omega, show 6 ≤ q + 10 by omega, show 7 ≤ q + 10 by omega, show 8 ≤ q + 10 by omega,
      show ¬ q + 10 = 1 by omega, show ¬ q + 10 = 2 by omega, show ¬ q + 10 = 3 by omega, show ¬ q +
      10 = 4 by omega, show ¬ q + 10 = 5 by omega, show ¬ q + 10 = 6 by omega, show ¬ q + 10 = 7 by
      omega, show ¬ q + 10 = 8 by omega, show ¬ q + 10 = 9 by omega, if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's terms a(1..12). -/
theorem controls : a 1 = 65 ∧ a 2 = 717 ∧ a 3 = 5492 ∧ a 4 = 29461 ∧ a 5 = 118530 ∧ a 6 = 384605 ∧ a
    7 = 1061632 ∧ a 8 = 2587557 ∧ a 9 = 5717246 ∧ a 10 = 11671405 ∧ a 11 = 22326540 ∧ a 12 =
    40450997 := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := small
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 9 < n →
      (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      X * (65 + 197 * X + 1576 * X ^ 2 + 1961 * X ^ 3 + 1016 * X ^ 4 + 271 * X ^ 5 - 76 * X ^ 6 + 35 * X ^ 7 - 5 * X ^ 8) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a268265

theorem OMA.solution : type_of% @OMA.S_oeis_a268265.main :=
  OMA.S_oeis_a268265.conjecture
