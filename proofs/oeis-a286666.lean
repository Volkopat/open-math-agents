import OMAStatements.S_oeis_a286666
import Mathlib

/-!
Proof of the A286666 conjecture: a(n)/n tends to 1 + sqrt(2).

A prefix of A286665 is the {0->01}-transform of a prefix of the Pell word, followed by at most
one 0. The prefix that ends at the n-th 0 must end with that extra 0 (a transformed word ends
in 1), so a(n) = j + n where the Pell prefix of length j has n - 1 zeros. As for A286667, every
prefix of length m of the Pell word with Z zeros has |m - sqrt 2 Z| ≤ 2, so j/n tends to sqrt 2.
-/

namespace OMA.P286666

open OMA.S_oeis_a286666

lemma len_flatMap_pell (l : List ℕ) :
    (l.flatMap pellMorph).length = l.length + 2 * l.count 0 := by
  induction l with
  | nil => simp
  | cons b t ih =>
    cases b with
    | zero => simp [List.flatMap_cons, pellMorph, ih]; ring
    | succ n => simp [List.flatMap_cons, pellMorph, ih]; ring

lemma count0_flatMap_pell (l : List ℕ) :
    (l.flatMap pellMorph).count 0 = l.length + l.count 0 := by
  induction l with
  | nil => simp
  | cons b t ih =>
    cases b with
    | zero => simp [List.flatMap_cons, pellMorph, ih]; ring
    | succ n => simp [List.flatMap_cons, pellMorph, ih]; ring

lemma len_flatMap_psi (l : List ℕ) :
    (l.flatMap psi).length = l.length + l.count 0 := by
  induction l with
  | nil => simp
  | cons b t ih =>
    cases b with
    | zero => simp [List.flatMap_cons, psi, ih]; ring
    | succ n => simp [List.flatMap_cons, psi, ih]; ring

lemma count1_flatMap_psi (l : List ℕ) :
    (l.flatMap psi).count 1 = l.length := by
  induction l with
  | nil => simp
  | cons b t ih =>
    cases b with
    | zero => simp [List.flatMap_cons, psi, ih]
    | succ n => simp [List.flatMap_cons, psi, ih]

lemma flatMap_psi_concat (l : List ℕ) (hl : l ≠ []) :
    ∃ X : List ℕ, l.flatMap psi = X ++ [1] := by
  obtain ⟨t, b, rfl⟩ := List.eq_nil_or_concat l |>.resolve_left hl
  cases b with
  | zero => exact ⟨t.flatMap psi ++ [0], by simp [List.flatMap_append, psi]⟩
  | succ n => exact ⟨t.flatMap psi, by simp [List.flatMap_append, psi]⟩

lemma prefix_flatMap {l₁ l₂ : List ℕ} (f : ℕ → List ℕ) (h : l₁ <+: l₂) :
    l₁.flatMap f <+: l₂.flatMap f := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t.flatMap f, by rw [List.flatMap_append]⟩

lemma pellIter_prefix_succ (k : ℕ) : pellIter k <+: pellIter (k + 1) := by
  induction k with
  | zero => exact ⟨[0, 1], rfl⟩
  | succ k ih =>
    show (pellIter k).flatMap pellMorph <+: (pellIter (k + 1)).flatMap pellMorph
    exact prefix_flatMap pellMorph ih

lemma pellIter_prefix {j k : ℕ} (h : j ≤ k) : pellIter j <+: pellIter k := by
  induction k, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k _ ih => exact ih.trans (pellIter_prefix_succ k)

lemma count0_pellIter_pos (k : ℕ) : 1 ≤ (pellIter k).count 0 := by
  induction k with
  | zero => simp [pellIter]
  | succ k ih =>
    show 1 ≤ ((pellIter k).flatMap pellMorph).count 0
    rw [count0_flatMap_pell]; omega

lemma pellIter_length (k : ℕ) : k + 1 ≤ (pellIter k).length := by
  induction k with
  | zero => simp [pellIter]
  | succ k ih =>
    show k + 1 + 1 ≤ ((pellIter k).flatMap pellMorph).length
    rw [len_flatMap_pell]
    have := count0_pellIter_pos k
    omega

lemma wIter_prefix {j k : ℕ} (h : j ≤ k) : wIter j <+: wIter k :=
  prefix_flatMap psi (pellIter_prefix h)

lemma wIter_length (k : ℕ) : k + 1 ≤ (wIter k).length := by
  unfold wIter
  rw [len_flatMap_psi]
  have := pellIter_length k
  omega

lemma getD_of_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  have hi2 : i < l₂.length := lt_of_lt_of_le hi h.length_le
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi2]
  exact h.getElem hi

lemma w_eq (k i : ℕ) (hi : i < (wIter k).length) : w i = (wIter k).getD i 0 := by
  unfold w
  rcases le_total (i + 1) k with h | h
  · exact getD_of_prefix (wIter_prefix h) (by have := wIter_length (i + 1); omega)
  · exact (getD_of_prefix (wIter_prefix h) hi).symm

lemma take_pellMorph (b m : ℕ) (hm : m < (pellMorph b).length) :
    (pellMorph b).take m = List.replicate m 0 := by
  cases b with
  | zero =>
    simp only [pellMorph, List.length_cons, List.length_nil] at hm
    interval_cases m <;> rfl
  | succ n =>
    simp only [pellMorph, List.length_cons, List.length_nil] at hm
    interval_cases m
    rfl

lemma pellMorph_length_le (b : ℕ) : (pellMorph b).length ≤ 3 := by
  cases b <;> simp [pellMorph]

/-- A prefix of the image of `l` is the image of a prefix of `l` followed by at most two zeros. -/
lemma decomp (l : List ℕ) : ∀ m, m ≤ (l.flatMap pellMorph).length →
    ∃ j ≤ l.length, ∃ r ≤ 2,
      (l.flatMap pellMorph).take m = (l.take j).flatMap pellMorph ++ List.replicate r 0 := by
  induction l with
  | nil =>
    intro m hm
    simp at hm
    subst hm
    exact ⟨0, le_refl _, 0, by norm_num, by simp⟩
  | cons b t ih =>
    intro m hm
    rw [List.flatMap_cons] at hm ⊢
    by_cases hlt : m < (pellMorph b).length
    · refine ⟨0, Nat.zero_le _, m, ?_, ?_⟩
      · have := pellMorph_length_le b
        omega
      · rw [List.take_append_of_le_length (le_of_lt hlt), take_pellMorph b m hlt]
        simp
    · rw [not_lt] at hlt
      obtain ⟨k, rfl⟩ : ∃ k, m = (pellMorph b).length + k := ⟨m - (pellMorph b).length, by omega⟩
      rw [List.length_append] at hm
      obtain ⟨j, hj, r, hr, h⟩ := ih k (by omega)
      refine ⟨j + 1, by simp; omega, r, hr, ?_⟩
      rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left, h,
        List.take_succ_cons, List.flatMap_cons, List.append_assoc]

/-- Zeros among the first m letters: |m - sqrt 2 * count| ≤ 2 on every prefix of every S(K). -/
lemma bound (K : ℕ) : ∀ m, m ≤ (pellIter K).length →
    |(m : ℝ) - Real.sqrt 2 * (((pellIter K).take m).count 0 : ℝ)| ≤ 2 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs1 : 1 < Real.sqrt 2 := by nlinarith
  have hs2 : Real.sqrt 2 < 3 / 2 := by nlinarith
  induction K with
  | zero =>
    intro m hm
    simp only [pellIter, List.length_cons, List.length_nil] at hm
    interval_cases m
    · simp
    · simp only [pellIter, List.take_succ_cons, List.take_zero, List.count_singleton_self]
      rw [abs_le]
      constructor <;> push_cast <;> linarith
  | succ K ih =>
    intro m hm
    have hm' : m ≤ ((pellIter K).flatMap pellMorph).length := hm
    obtain ⟨j, hj, r, hr, h⟩ := decomp (pellIter K) m hm'
    have hcount : ((pellIter (K + 1)).take m).count 0 =
        j + ((pellIter K).take j).count 0 + r := by
      show (((pellIter K).flatMap pellMorph).take m).count 0 = _
      rw [h, List.count_append, count0_flatMap_pell, List.count_replicate_self, List.length_take,
        min_eq_left hj]
    have hlen : m = j + 2 * ((pellIter K).take j).count 0 + r := by
      have := congrArg List.length h
      rw [List.length_take, min_eq_left hm', List.length_append, len_flatMap_pell,
        List.length_replicate, List.length_take, min_eq_left hj] at this
      omega
    have hj' := ih j hj
    rw [hcount]
    set c := ((pellIter K).take j).count 0 with hc
    have hm_real : (m : ℝ) = j + 2 * c + r := by rw [hlen]; push_cast; ring
    rw [hm_real]
    push_cast
    have key : (j : ℝ) + 2 * c + r - Real.sqrt 2 * (j + c + r) =
        (1 - Real.sqrt 2) * (((j : ℝ) - Real.sqrt 2 * c) + r) := by
      linear_combination (-(c : ℝ)) * hs
    rw [key, abs_mul, abs_of_neg (by linarith : 1 - Real.sqrt 2 < 0)]
    have hr' : (r : ℝ) ≤ 2 := by exact_mod_cast hr
    have hr0 : (0 : ℝ) ≤ r := by positivity
    have h1 : |((j : ℝ) - Real.sqrt 2 * c) + r| ≤ 4 := by
      calc |((j : ℝ) - Real.sqrt 2 * c) + r| ≤ |(j : ℝ) - Real.sqrt 2 * c| + |(r : ℝ)| :=
            abs_add_le _ _
        _ ≤ 2 + 2 := by
            rw [abs_of_nonneg hr0]
            linarith
        _ = 4 := by norm_num
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ Real.sqrt 2 - 1)]


lemma count_eq (c : ℕ) (U : List ℕ) (hU : ∀ i < U.length, w i = U.getD i 0) :
    ∀ m ≤ U.length, Nat.count (fun i => w i = c) m = (U.take m).count c := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [Nat.count_succ, ih (by omega), List.take_add_one, List.count_append, hU m (by omega),
      List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
    simp [List.count_singleton]

lemma count0_flatMap_psi (l : List ℕ) : (l.flatMap psi).count 0 = l.count 0 := by
  induction l with
  | nil => simp
  | cons b t ih =>
    cases b with
    | zero => simp [List.flatMap_cons, psi, ih]
    | succ n => simp [List.flatMap_cons, psi, ih]

lemma count0_pellIter_ge (k : ℕ) : k + 1 ≤ (pellIter k).count 0 := by
  induction k with
  | zero => simp [pellIter]
  | succ k ih =>
    show k + 1 + 1 ≤ ((pellIter k).flatMap pellMorph).count 0
    rw [count0_flatMap_pell]
    have := pellIter_length k
    omega

lemma zeros_infinite : {i | w i = 0}.Infinite := by
  intro hfin
  have hle := Nat.count_le_card hfin (wIter hfin.toFinset.card).length
  rw [count_eq 0 _ (fun i hi => w_eq _ i hi) _ le_rfl, List.take_length] at hle
  unfold wIter at hle
  rw [count0_flatMap_psi] at hle
  exact Nat.not_succ_le_self _ (le_trans (count0_pellIter_ge hfin.toFinset.card) hle)

lemma take_psi (b m : ℕ) (hm : m < (psi b).length) : (psi b).take m = List.replicate m 0 := by
  cases b with
  | zero =>
    simp only [psi, List.length_cons, List.length_nil] at hm
    interval_cases m <;> rfl
  | succ n =>
    simp only [psi, List.length_cons, List.length_nil] at hm
    interval_cases m
    rfl

lemma psi_length_le (b : ℕ) : (psi b).length ≤ 2 := by
  cases b <;> simp [psi]

/-- A prefix of the transform of `l` is the transform of a prefix of `l`, then at most one 0. -/
lemma decomp_psi (l : List ℕ) : ∀ m, m ≤ (l.flatMap psi).length →
    ∃ j ≤ l.length, ∃ r ≤ 1,
      (l.flatMap psi).take m = (l.take j).flatMap psi ++ List.replicate r 0 := by
  induction l with
  | nil =>
    intro m hm
    simp at hm
    subst hm
    exact ⟨0, le_refl _, 0, by norm_num, by simp⟩
  | cons b t ih =>
    intro m hm
    rw [List.flatMap_cons] at hm ⊢
    by_cases hlt : m < (psi b).length
    · refine ⟨0, Nat.zero_le _, m, ?_, ?_⟩
      · have := psi_length_le b
        omega
      · rw [List.take_append_of_le_length (le_of_lt hlt), take_psi b m hlt]
        simp
    · rw [not_lt] at hlt
      obtain ⟨k, rfl⟩ : ∃ k, m = (psi b).length + k := ⟨m - (psi b).length, by omega⟩
      rw [List.length_append] at hm
      obtain ⟨j, hj, r, hr, h⟩ := ih k (by omega)
      refine ⟨j + 1, by simp; omega, r, hr, ?_⟩
      rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left, h,
        List.take_succ_cons, List.flatMap_cons, List.append_assoc]

/-- The n-th 0 of A286665 is at position j + n, where the Pell prefix of length j has n - 1
zeros. -/
lemma a_eq (n : ℕ) (hn : 1 ≤ n) : ∃ j Z : ℕ, a n = j + n ∧ Z + 1 = n ∧
    |(j : ℝ) - Real.sqrt 2 * (Z : ℝ)| ≤ 2 := by
  set p := Nat.nth (fun i => w i = 0) (n - 1) with hp
  have hwp : w p = 0 := Nat.nth_mem_of_infinite zeros_infinite (n - 1)
  have hcp : Nat.count (fun i => w i = 0) p = n - 1 :=
    Nat.count_nth_of_infinite zeros_infinite (n - 1)
  have hlenK : p + 1 ≤ (wIter (p + 1)).length := by
    have := wIter_length (p + 1)
    omega
  obtain ⟨j, hj, r, hr, h⟩ := decomp_psi (pellIter (p + 1)) (p + 1) hlenK
  have hcount : ((wIter (p + 1)).take (p + 1)).count 0 = n := by
    rw [← count_eq 0 _ (fun i hi => w_eq _ i hi) _ hlenK, Nat.count_succ, hcp]
    simp [hwp]
    omega
  have hlast : (wIter (p + 1)).take (p + 1) = (wIter (p + 1)).take p ++ [0] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
    have := w_eq (p + 1) p (by omega)
    rw [List.getD_eq_getElem _ _ (by omega), hwp] at this
    rw [← this]
    rfl
  have hr1 : r = 1 := by
    by_contra hr1
    have hr0 : r = 0 := by omega
    have h' : (wIter (p + 1)).take (p + 1) = ((pellIter (p + 1)).take j).flatMap psi := by
      rw [show (wIter (p + 1)) = (pellIter (p + 1)).flatMap psi from rfl, h, hr0,
        List.replicate_zero, List.append_nil]
    have hne : (pellIter (p + 1)).take j ≠ [] := by
      intro he
      rw [he] at h'
      have := congrArg List.length h'
      rw [List.length_take, min_eq_left hlenK] at this
      simp at this
    obtain ⟨X, hX⟩ := flatMap_psi_concat _ hne
    rw [hX, hlast] at h'
    have := congrArg List.getLast? h'
    simp at this
  rw [hr1] at h
  have h2 : (wIter (p + 1)).take (p + 1) = ((pellIter (p + 1)).take j).flatMap psi ++ [0] := h
  set u := (pellIter (p + 1)).take j with hu
  have hulen : u.length = j := by
    rw [hu, List.length_take]
    omega
  have hZ : u.count 0 + 1 = n := by
    have := congrArg (List.count 0) h2
    rw [hcount, List.count_append, count0_flatMap_psi] at this
    simp at this
    omega
  have hlen2 : p + 1 = j + n := by
    have := congrArg List.length h2
    rw [List.length_take, min_eq_left hlenK, List.length_append, len_flatMap_psi, hulen] at this
    simp at this
    omega
  refine ⟨j, u.count 0, ?_, hZ, ?_⟩
  · unfold a
    rw [← hp]
    omega
  · exact bound (p + 1) j hj

theorem sol : type_of% @OMA.S_oeis_a286666.main := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 < 2 := by nlinarith
  have key : ∀ n : ℕ, 1 ≤ n → |(a n : ℝ) / n - (1 + Real.sqrt 2)| ≤ 4 / n := by
    intro n hn
    obtain ⟨j, Z, ha, hZ, hb⟩ := a_eq n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hZr : (Z : ℝ) = n - 1 := by
      have : ((Z + 1 : ℕ) : ℝ) = n := by exact_mod_cast hZ
      push_cast at this
      linarith
    rw [ha]
    have e1 : ((j + n : ℕ) : ℝ) / n - (1 + Real.sqrt 2) =
        ((j : ℝ) - Real.sqrt 2 * Z - Real.sqrt 2) / n := by
      rw [hZr]
      push_cast
      field_simp
      ring
    rw [e1, abs_div, abs_of_pos hnpos]
    gcongr
    calc |(j : ℝ) - Real.sqrt 2 * Z - Real.sqrt 2|
        ≤ |(j : ℝ) - Real.sqrt 2 * Z| + |Real.sqrt 2| := abs_sub _ _
      _ ≤ 2 + 2 := by
          rw [abs_of_nonneg hs0]
          linarith
      _ = 4 := by norm_num
  have h0 : Filter.Tendsto (fun n : ℕ => (a n : ℝ) / n - (1 + Real.sqrt 2))
      Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat 4)
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs]
    exact key n hn
  have h1 := h0.add_const (1 + Real.sqrt 2)
  simpa using h1

end OMA.P286666

theorem OMA.solution : type_of% @OMA.S_oeis_a286666.main := OMA.P286666.sol

