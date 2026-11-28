import OMAStatements.S_oeis_a346310

namespace OMA.P_oeis_a346310

open OMA.S_oeis_a346310

lemma mem_vectors_length {L : ℕ} {v : List Bool} (h : v ∈ vectors L) : v.length = L := by
  simp only [vectors, List.mem_map] at h
  obtain ⟨j, -, rfl⟩ := h
  simp

lemma wordsUpTo_succ (N : ℕ) : wordsUpTo (N + 1) = wordsUpTo N ++ vectors (N + 1) := by
  simp [wordsUpTo, List.range'_concat, add_comm]

lemma wordsUpTo_length (N : ℕ) : (wordsUpTo N).length + 2 = 2 ^ (N + 1) := by
  induction N with
  | zero => simp [wordsUpTo]
  | succ N ih =>
    rw [wordsUpTo_succ, List.length_append]
    simp only [vectors, List.length_map, List.length_range]
    rw [pow_succ 2 (N + 1)]
    omega

lemma key (N : ℕ) : ∀ i (hi : i < (wordsUpTo N).length),
    ((wordsUpTo N)[i]).length = Nat.log 2 (i + 2) := by
  induction N with
  | zero => intro i hi; simp [wordsUpTo] at hi
  | succ N ih =>
    intro i hi
    have hlen := wordsUpTo_length N
    have hlen' := wordsUpTo_length (N + 1)
    simp only [wordsUpTo_succ] at hi ⊢
    by_cases h : i < (wordsUpTo N).length
    · rw [List.getElem_append_left h]
      exact ih i h
    · replace h := not_lt.mp h
      rw [List.getElem_append_right h]
      rw [mem_vectors_length (List.getElem_mem _)]
      rw [wordsUpTo_succ, List.length_append] at hlen'
      symm
      rw [Nat.log_eq_iff (by norm_num)]
      constructor
      · omega
      · rw [List.length_append] at hi
        rw [pow_succ 2 (N + 1)]
        omega

lemma w_length (n : ℕ) (hn : 1 ≤ n) : (w n).length = Nat.log 2 (n + 1) := by
  have hlen := wordsUpTo_length n
  have h2 : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  have hi : n - 1 < (wordsUpTo n).length := by omega
  rw [w, List.getD_eq_getElem _ _ hi, key n (n - 1) hi]
  congr 1
  omega

lemma evenPos_iff (n : ℕ) : EvenPos n ↔ 1 ≤ n ∧ Even (Nat.log 2 (n + 1)) := by
  unfold EvenPos
  constructor
  · rintro ⟨hn, he⟩
    refine ⟨hn, ?_⟩
    rw [← w_length n hn, ← List.count_false_add_count_true (w n)]
    rw [← Int.even_coe_nat]
    push_cast
    rw [Int.even_add]
    rwa [Int.even_sub] at he
  · rintro ⟨hn, he⟩
    refine ⟨hn, ?_⟩
    rw [← w_length n hn, ← List.count_false_add_count_true (w n)] at he
    rw [← Int.even_coe_nat] at he
    push_cast at he
    rw [Int.even_add] at he
    rwa [Int.even_sub]

/-- The predicate of A053738. -/
def Q (k : ℕ) : Prop := Odd (Nat.digits 2 k).length

lemma not_Q_zero : ¬ Q 0 := by simp [Q]

lemma Q_succ (m : ℕ) : Q (m + 1) ↔ (m = 0 ∨ EvenPos m) := by
  rw [Q, Nat.length_digits 2 (m + 1) (by norm_num) (by omega), evenPos_iff, Nat.odd_add_one,
    Nat.not_odd_iff_even]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · constructor
    · intro h; exact Or.inr ⟨hm, h⟩
    · rintro (h | ⟨-, h⟩)
      · omega
      · exact h

instance : DecidablePred EvenPos := fun n => by unfold EvenPos; infer_instance

/-- The shifted predicate `R i ↔ Q (i + 1)`. -/
def R (i : ℕ) : Prop := i = 0 ∨ EvenPos i

instance : DecidablePred R := fun n => by unfold R; infer_instance

lemma evenPos_infinite : (Set.ofPred EvenPos).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  refine ⟨4 ^ (a + 1) - 1, ?_, ?_⟩
  · show EvenPos _
    have h4 : 1 ≤ 4 ^ (a + 1) := Nat.one_le_pow _ _ (by norm_num)
    have h4' : (4 : ℕ) ^ (a + 1) = 2 ^ (2 * (a + 1)) := by
      rw [pow_mul]; norm_num
    rw [evenPos_iff, Nat.sub_add_cancel h4, h4', Nat.log_pow (by norm_num)]
    refine ⟨?_, even_two_mul _⟩
    have : 2 ≤ 2 ^ (2 * (a + 1)) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * (a + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have h1 : a + 1 < 2 ^ (a + 1) := Nat.lt_two_pow_self
    have h2 : 2 ^ (a + 1) ≤ 4 ^ (a + 1) := Nat.pow_le_pow_left (by norm_num) _
    omega

lemma Q_infinite : (Set.ofPred Q).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨b, hb, hab⟩ := evenPos_infinite.exists_gt a
  exact ⟨b + 1, (Q_succ b).mpr (Or.inr hb), by omega⟩

lemma count_R (m : ℕ) (hm : 1 ≤ m) : Nat.count R m = Nat.count EvenPos m + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.count_succ', Nat.count_succ']
  have h0 : R 0 := Or.inl rfl
  have h0' : ¬ EvenPos 0 := fun h => by have := h.1; omega
  have hfun : (fun i => R (i + 1)) = (fun i => EvenPos (i + 1)) := by
    funext i
    apply propext
    simp [R]
  simp only [h0, h0', if_true, if_false, add_zero]
  simp only [hfun]

end OMA.P_oeis_a346310

open OMA.P_oeis_a346310 in
theorem OMA.solution : type_of% @OMA.S_oeis_a346310.main := by
  intro n hn
  unfold OMA.S_oeis_a346310.a OMA.S_oeis_a346310.A053738
  rw [show n + 1 - 1 = n by omega]
  have hQ : (fun k => Odd (Nat.digits 2 k).length) = Q := rfl
  rw [hQ]
  have hne : Nat.nth Q n ≠ 0 := by
    intro h
    have := Nat.nth_mem_of_infinite Q_infinite n
    rw [h] at this
    exact not_Q_zero this
  rw [← Nat.nth_add_one_eq_sub not_Q_zero hne]
  have hR : (fun i => Q (i + 1)) = R := by
    funext i; exact propext (Q_succ i)
  rw [hR]
  set m := Nat.nth OMA.S_oeis_a346310.EvenPos (n - 1) with hm
  have hmem : OMA.S_oeis_a346310.EvenPos m := Nat.nth_mem_of_infinite evenPos_infinite _
  have hcount : Nat.count OMA.S_oeis_a346310.EvenPos m = n - 1 :=
    Nat.count_nth_of_infinite evenPos_infinite _
  have hRm : R m := Or.inr hmem
  have hcR : Nat.count R m = n := by
    rw [count_R m hmem.1, hcount]; omega
  rw [← hcR, Nat.nth_count hRm]
