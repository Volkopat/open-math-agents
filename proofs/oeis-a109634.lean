import OMAStatements.S_oeis_a109634

-- Count ternary words by their number of isolated ones to obtain the sum conjectured by R. J. Mathar.

namespace OMA.A109634

def good {n : ℕ} (f : Fin n → Fin 3) : Prop :=
  ∀ i j : Fin n, j.val = i.val + 1 → ¬ (f i = 1 ∧ f j = 1)

def ones {n : ℕ} (f : Fin n → Fin 3) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => f i = 1)).card

def count (n k : ℕ) : ℕ := by
  letI (f : Fin n → Fin 3) : Decidable (good f) := by unfold good; infer_instance
  exact (Finset.univ.filter (fun f : Fin n → Fin 3 => good f ∧ ones f = k)).card

end OMA.A109634

namespace OMA.A109634

open scoped Classical

private theorem good_cons {n : ℕ} (x : Fin 3) (f : Fin n → Fin 3) :
    good (Fin.cons x f) ↔ good f ∧ (∀ i : Fin n, i.val = 0 → ¬ (x = 1 ∧ f i = 1)) := by
  constructor
  · intro h
    exact ⟨fun i j hij => h i.succ j.succ (by simpa using hij),
      fun i hi => h 0 i.succ (by simpa using hi)⟩
  · rintro ⟨h, h₀⟩ i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases (by simp) (fun j => ?_) j
      simpa using h₀ j
    · refine Fin.cases (by simp) (fun j => ?_) j
      simpa using h i j

private theorem good_cons_cons {n : ℕ} (x y : Fin 3) (f : Fin n → Fin 3) :
    good (Fin.cons x (Fin.cons y f)) ↔ good (Fin.cons y f) ∧ ¬ (x = 1 ∧ y = 1) := by
  rw [good_cons]
  refine and_congr_right fun _ => ⟨fun h => h 0 rfl, ?_⟩
  intro h i hi
  have : i = 0 := Fin.ext hi
  simpa [this] using h

private theorem ones_cons {n : ℕ} (x : Fin 3) (f : Fin n → Fin 3) :
    ones (Fin.cons x f) = (if x = 1 then 1 else 0) + ones f := by
  have h {m : ℕ} (g : Fin m → Fin 3) :
      ones g = ∑ i, if g i = 1 then 1 else 0 := by simp [ones]
  rw [h, h, Fin.sum_univ_succ]
  rfl

private theorem sum_words {n : ℕ} (F : (Fin (n+1) → Fin 3) → ℕ) :
    (∑ f, F f) = (∑ t, F (Fin.cons 0 t)) + (∑ t, F (Fin.cons 1 t)) +
      (∑ t, F (Fin.cons 2 t)) := by
  let e := Fin.consEquiv (fun _ : Fin (n+1) => Fin 3)
  rw [← e.sum_comp F, Fintype.sum_prod_type]
  simp [e, Fin.consEquiv, Fin.sum_univ_succ, add_assoc]

private noncomputable def weight {n : ℕ} (k : ℕ) (f : Fin n → Fin 3) : ℕ :=
  if good f ∧ ones f = k then 1 else 0

private theorem sum_weight (n k : ℕ) : (∑ f : Fin n → Fin 3, weight k f) = count n k := by
  simp [weight, count]
  congr 1
  ext f
  simp

private theorem weight_cons_other {n : ℕ} (k : ℕ) (x : Fin 3) (hx : x ≠ 1) (f : Fin n → Fin 3) :
    weight k (Fin.cons x f) = weight k f := by
  simp [weight, good_cons, ones_cons, hx]

private theorem weight_one_other {n : ℕ} (k : ℕ) (x : Fin 3) (hx : x ≠ 1) (f : Fin n → Fin 3) :
    weight (k+1) (Fin.cons 1 (Fin.cons x f)) = weight k f := by
  unfold weight
  rw [good_cons_cons, good_cons, ones_cons, ones_cons]
  simp [hx, Nat.add_comm 1]

private theorem weight_one_one {n : ℕ} (k : ℕ) (f : Fin n → Fin 3) :
    weight k (Fin.cons 1 (Fin.cons 1 f)) = 0 := by
  simp [weight, good_cons_cons]

theorem count_step (n k : ℕ) :
    count (n+2) (k+1) = 2*count (n+1) (k+1) + 2*count n k := by
  rw [← sum_weight, sum_words]
  simp_rw [weight_cons_other _ 0 (by decide), weight_cons_other _ 2 (by decide)]
  rw [sum_weight, sum_words (fun t => weight (k+1) (Fin.cons 1 t))]
  simp_rw [weight_one_other _ 0 (by decide), weight_one_other _ 2 (by decide), weight_one_one]
  simp [sum_weight]
  omega

end OMA.A109634

namespace OMA.A109634

theorem count_no_ones (n : ℕ) : count n 0 = 2^n := by
  classical
  have h (f : Fin n → Fin 3) : good f ∧ ones f = 0 ↔ ∀ i, f i ≠ 1 := by
    have z : ones f = 0 ↔ ∀ i, f i ≠ 1 := by
      simp [ones, Finset.filter_eq_empty_iff]
    rw [z]
    exact ⟨And.right, fun hn => ⟨fun i _ _ p => hn i p.1, hn⟩⟩
  unfold count
  simp_rw [h]
  rw [← Fintype.card_subtype]
  let e : {f : Fin n → Fin 3 // ∀ i, f i ≠ 1} ≃ (Fin n → {c : Fin 3 // c ≠ 1}) :=
    Equiv.subtypePiEquivPi (β := fun _ : Fin n => Fin 3) (p := fun _ c => c ≠ 1)
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]
  congr 1

theorem count_above {n k : ℕ} (hn : n < k) : count n k = 0 := by
  classical
  unfold count
  apply Finset.card_eq_zero.mpr
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro ⟨_, hk⟩
  have h : ones f ≤ n := by
    simpa [ones] using (Finset.card_filter_le Finset.univ (fun i : Fin n => f i = 1))
  omega

theorem count_empty (k : ℕ) : count 0 k = if k = 0 then 1 else 0 := by
  cases k with
  | zero => decide
  | succ k => simp [count_above]

theorem count_one (k : ℕ) : count 1 k = if k = 0 then 2 else if k = 1 then 1 else 0 := by
  rcases k with _ | _ | k
  · decide
  · decide
  · simp [count_above (by omega : 1 < k + 2)]

end OMA.A109634

namespace OMA.A109634

theorem count_closed (n k : ℕ) : count n k = (n + 1 - k).choose k * 2 ^ (n - k) := by
  induction n using Nat.twoStepInduction generalizing k with
  | zero =>
    cases k with
    | zero => simp [count_empty]
    | succ k =>
      rw [count_empty, if_neg (Nat.succ_ne_zero _), Nat.choose_eq_zero_of_lt (by omega)]
      simp
  | one =>
    rcases k with _ | _ | k
    · simp [count_one]
    · simp [count_one]
    · rw [count_one, if_neg (by omega), if_neg (by omega), Nat.choose_eq_zero_of_lt (by omega)]
      simp
  | more n ih ih' =>
    cases k with
    | zero => simp [count_no_ones]
    | succ k =>
      rw [count_step, ih', ih]
      by_cases hk : k ≤ n
      · rw [show n + 2 + 1 - (k + 1) = (n + 1 - k) + 1 by omega,
          Nat.choose_succ_succ, show n + 1 + 1 - (k + 1) = n + 1 - k by omega,
          show n + 1 - (k + 1) = n - k by omega,
          show 2 ^ (n + 1 - k) = 2 ^ (n - k) * 2 by rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]]
        ring
      · rw [Nat.choose_eq_zero_of_lt (show n + 1 + 1 - (k + 1) < k + 1 by omega),
          Nat.choose_eq_zero_of_lt (show n + 1 - k < k by omega),
          Nat.choose_eq_zero_of_lt (show n + 2 + 1 - (k + 1) < k + 1 by omega)]
        simp

end OMA.A109634

namespace OMA.A109634

open S_oeis_a109634

-- In the fiber of words containing k ones, every word contributes exactly k.
lemma a_eq_sum_count (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n + 1), count n k * k := by
  classical
  let words := Finset.univ.filter (good (n := n))
  have ha : a n = ∑ f ∈ words, ones f := by
    unfold a
    apply Finset.sum_congr
    · ext f
      simp [words, good]
    · intro f _
      rfl
  rw [ha]
  have hbound (f : Fin n → Fin 3) : ones f ≤ n := by
    simpa [ones] using Finset.card_filter_le Finset.univ (fun i => f i = 1)
  have hmap (f) (_ : f ∈ words) : ones f ∈ Finset.range (n + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound f))
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun f => ones f)]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc
    _ = ∑ _f ∈ words.filter (fun f => ones f = k), k :=
      Finset.sum_congr rfl fun f hf => (Finset.mem_filter.mp hf).2
    _ = count n k * k := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      unfold count
      apply congrArg Finset.card
      ext f
      simp [words]

end OMA.A109634

open OMA.A109634 OMA.S_oeis_a109634

theorem OMA.solution : type_of% @OMA.S_oeis_a109634.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_eq_sum_count, Finset.sum_range_succ', Nat.mul_zero, Nat.add_zero]
  simp only [Nat.add_sub_cancel, b]
  calc
    _ = ∑ k ∈ Finset.range (m + 1),
        (m - k + 1) * (m - k).choose k * 2 ^ (m - k) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkm : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [count_closed, show m + 1 + 1 - (k + 1) = m - k + 1 by omega,
        show m + 1 - (k + 1) = m - k by omega, Nat.add_one_mul_choose_eq]
      ac_rfl
    _ = _ := by
      symm
      apply Finset.sum_subset
      · apply Finset.range_mono
        omega
      · intro k hk hk'
        simp only [Finset.mem_range] at hk hk'
        rw [Nat.choose_eq_zero_of_lt (show m - k < k by omega)]
        simp
