import OMAStatements.S_oeis_a066897

namespace OMA.S_oeis_a066897

open Finset

private theorem range_list_sum {R : Type} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  rw [sum_eq_multiset_sum]
  rfl

private theorem sum_by_rows {R : Type} [AddCommMonoid R] (D : YoungDiagram) (f : ℕ × ℕ → R) :
    (∑ c ∈ D.cells, f c) =
      ∑ i ∈ range (D.colLen 0), ∑ j ∈ range (D.rowLen i), f (i, j) := by
  have hm : ∀ c ∈ D.cells, c.1 ∈ range (D.colLen 0) := by
    rintro ⟨i, j⟩ h
    exact mem_range.mpr (YoungDiagram.mem_iff_lt_colLen.mp
      (D.up_left_mem (show i ≤ i from le_rfl) (Nat.zero_le j) h))
  calc
    _ = ∑ i ∈ range (D.colLen 0), ∑ c ∈ D.row i, f c :=
      (sum_fiberwise_of_maps_to hm f).symm
    _ = _ := by
      apply sum_congr rfl
      intro i _
      rw [YoungDiagram.row_eq_prod, Finset.sum_product]
      simp

private theorem sum_by_columns {R : Type} [AddCommMonoid R] (D : YoungDiagram) (f : ℕ × ℕ → R) :
    (∑ c ∈ D.cells, f c) =
      ∑ j ∈ range (D.rowLen 0), ∑ i ∈ range (D.colLen j), f (i, j) := by
  have hm : ∀ c ∈ D.cells, c.2 ∈ range (D.rowLen 0) := by
    rintro ⟨i, j⟩ h
    exact mem_range.mpr (YoungDiagram.mem_iff_lt_rowLen.mp
      (D.up_left_mem (Nat.zero_le i) (show j ≤ j from le_rfl) h))
  calc
    _ = ∑ j ∈ range (D.rowLen 0), ∑ c ∈ D.col j, f c :=
      (sum_fiberwise_of_maps_to hm f).symm
    _ = _ := by
      apply sum_congr rfl
      intro j _
      rw [YoungDiagram.col_eq_prod, Finset.sum_product]
      simp

private theorem cell_count (D : YoungDiagram) : D.cells.card = D.rowLens.sum := by
  rw [YoungDiagram.rowLens, range_list_sum]
  simpa using sum_by_rows D (fun _ => (1 : ℕ))

private theorem sorted_parts_order {n : ℕ} (p : Nat.Partition n) : (sortedParts p).SortedGE :=
  (Multiset.pairwise_sort _ _).sortedGE

private noncomputable def diagram {n : ℕ} (p : Nat.Partition n) : YoungDiagram :=
  YoungDiagram.ofRowLens (sortedParts p) (sorted_parts_order p)

private theorem diagram_rows {n : ℕ} (p : Nat.Partition n) :
    (diagram p).rowLens = sortedParts p := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro x hx
  exact p.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp hx)

private theorem diagram_card {n : ℕ} (p : Nat.Partition n) : (diagram p).cells.card = n := by
  rw [cell_count, diagram_rows]
  change ((sortedParts p : Multiset ℕ).sum) = n
  rw [sortedParts, Multiset.sort_eq, p.parts_sum]

private noncomputable def conjugate {n : ℕ} (p : Nat.Partition n) : Nat.Partition n where
  parts := ((diagram p).transpose.rowLens : Multiset ℕ)
  parts_pos := fun {_} h => (diagram p).transpose.pos_of_mem_rowLens _ h
  parts_sum := by
    change (diagram p).transpose.rowLens.sum = n
    rw [← cell_count]
    simpa [YoungDiagram.transpose] using diagram_card p

private theorem conjugate_rows {n : ℕ} (p : Nat.Partition n) :
    sortedParts (conjugate p) = (diagram p).transpose.rowLens := by
  unfold sortedParts
  change ((diagram p).transpose.rowLens : Multiset ℕ).sort (· ≥ ·) =
    (diagram p).transpose.rowLens
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (diagram p).transpose.rowLens_sorted.pairwise

private theorem conjugate_involutive {n : ℕ} : Function.Involutive (@conjugate n) := by
  intro p
  have he : diagram (conjugate p) = (diagram p).transpose := by
    apply YoungDiagram.equivListRowLens.injective
    apply Subtype.ext
    exact (diagram_rows (conjugate p)).trans (conjugate_rows p)
  apply Nat.Partition.ext
  change ((diagram (conjugate p)).transpose.rowLens : Multiset ℕ) = p.parts
  rw [he, YoungDiagram.transpose_transpose, diagram_rows, sortedParts, Multiset.sort_eq]

private theorem range_alt_sum (n : ℕ) (f : ℕ → ℕ) :
    altSum ((List.range n).map f) = ∑ i ∈ range n, (-1 : ℤ) ^ i * (f i : ℤ) := by
  induction n generalizing f with
  | zero => simp [altSum]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, altSum, ih, sum_range_succ']
    simp only [Function.comp_apply, pow_zero, one_mul, pow_succ]
    rw [sub_eq_neg_add, ← sum_neg_distrib]
    congr 1
    apply sum_congr rfl
    intro i _
    ring

private theorem sum_sign (m : ℕ) :
    (∑ i ∈ range m, (-1 : ℤ) ^ i) = if m % 2 = 1 then 1 else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    by_cases h : m % 2 = 1
    · have hsign : (-1 : ℤ) ^ m = -1 := (Nat.odd_iff.mpr h).neg_one_pow
      have he : (m + 1) % 2 = 0 := by omega
      norm_num [h, hsign, he]
    · have he : m % 2 = 0 := by omega
      have hsign : (-1 : ℤ) ^ m = 1 := (Nat.even_iff.mpr he).neg_one_pow
      have ho : (m + 1) % 2 = 1 := by omega
      norm_num [h, hsign, ho]

private theorem odd_count_list (l : List ℕ) :
    (l.filter (fun x => x % 2 == 1)).length = (l.map (fun x => if x % 2 = 1 then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x % 2 = 1 <;> simp [h, ih, Nat.add_comm]

private theorem alternating_columns (D : YoungDiagram) :
    altSum D.rowLens = (((D.transpose.rowLens.filter (fun x => x % 2 == 1)).length : ℕ) : ℤ) := by
  calc
    altSum D.rowLens = ∑ i ∈ range (D.colLen 0), (-1 : ℤ) ^ i * (D.rowLen i : ℤ) := by
      exact range_alt_sum _ _
    _ = ∑ c ∈ D.cells, (-1 : ℤ) ^ c.1 := by
      rw [sum_by_rows]
      apply sum_congr rfl
      intro i _
      simp [mul_comm]
    _ = ∑ j ∈ range (D.rowLen 0), if D.colLen j % 2 = 1 then (1 : ℤ) else 0 := by
      rw [sum_by_columns]
      exact sum_congr rfl (fun _ _ => sum_sign _)
    _ = _ := by
      rw [odd_count_list]
      simp only [YoungDiagram.rowLens, YoungDiagram.colLen_transpose, List.map_map,
        Function.comp_apply, YoungDiagram.rowLen_transpose, range_list_sum, Nat.cast_sum]
      apply sum_congr rfl
      intro i _
      split_ifs <;> norm_num

end OMA.S_oeis_a066897

open Finset OMA.S_oeis_a066897 in
theorem OMA.solution : type_of% @OMA.S_oeis_a066897.main := by
  intro n _
  let e : Nat.Partition n ≃ Nat.Partition n :=
    ⟨conjugate, conjugate, conjugate_involutive, conjugate_involutive⟩
  unfold totalOddParts
  rw [Nat.cast_sum]
  refine Fintype.sum_equiv e _ _ (fun p => ?_)
  rw [← diagram_rows p, alternating_columns]
  change _ = ((Multiset.filter (fun x => x % 2 = 1)
    ((diagram p).transpose.rowLens : Multiset ℕ)).card : ℤ)
  have he : (fun x : ℕ => x % 2 == 1) = (fun x => decide (x % 2 = 1)) := by
    funext x
    by_cases h : x % 2 = 1 <;> simp [h]
  rw [he, Multiset.filter_coe, Multiset.coe_card]
