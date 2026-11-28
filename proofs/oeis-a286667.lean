import OMAStatements.S_oeis_a286667
import Mathlib

/-!
Proof of the A286667 conjecture: a(n)/n tends to 1 + sqrt(1/2).

Each letter of the Pell word gives exactly one 1 in A286665 (0 -> 01, 1 -> 1), so the n-th 1 sits
at position n + Z(n), where Z(n) counts the zeros among the first n letters of the Pell word.
A prefix of length m of the Pell word is the image of a prefix of length j plus at most two
zeros, which gives E(m) = (1 - sqrt 2) (E(j) + r) for E(m) = m - sqrt 2 Z(m) and r at most 2.
Since |1 - sqrt 2| < 1/2, induction gives |E(m)| ≤ 2, so Z(n)/n tends to 1/sqrt 2.
-/

namespace OMA.P286667

open OMA.S_oeis_a286667

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

lemma count_eq (U : List ℕ) (hU : ∀ i < U.length, w i = U.getD i 0) :
    ∀ m ≤ U.length, Nat.count (fun i => w i = 1) m = (U.take m).count 1 := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [Nat.count_succ, ih (by omega), List.take_add_one, List.count_append, hU m (by omega),
      List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
    simp [List.count_singleton]

/-- The n-th 1 of A286665 is at position n + Z(n), with Z(n) the zeros among the first n letters
of the Pell word. -/
lemma a_eq (n : ℕ) (hn : 1 ≤ n) : a n = n + ((pellIter n).take n).count 0 := by
  set u := (pellIter n).take n with hu
  have hulen : u.length = n := by
    rw [hu, List.length_take]
    have := pellIter_length n
    omega
  have hpre : u.flatMap psi <+: wIter n := prefix_flatMap psi (List.take_prefix n (pellIter n))
  have hU : ∀ i < (u.flatMap psi).length, w i = (u.flatMap psi).getD i 0 := by
    intro i hi
    rw [w_eq n i (lt_of_lt_of_le hi hpre.length_le)]
    exact (getD_of_prefix hpre hi).symm
  have hne : u ≠ [] := by
    intro h
    rw [h] at hulen
    simp at hulen
    omega
  obtain ⟨X, hX⟩ := flatMap_psi_concat u hne
  have hXlen : X.length + 1 = n + u.count 0 := by
    have := len_flatMap_psi u
    rw [hX, List.length_append, hulen] at this
    simpa using this
  have hXc : X.count 1 + 1 = n := by
    have := count1_flatMap_psi u
    rw [hX, List.count_append, hulen] at this
    simpa using this
  have hwX : w X.length = 1 := by
    rw [hU X.length (by rw [hX]; simp), hX]
    simp
  have hcnt : Nat.count (fun i => w i = 1) X.length = n - 1 := by
    rw [count_eq (u.flatMap psi) hU X.length (by rw [hX]; simp), hX]
    simp
    omega
  unfold a
  rw [← hcnt, Nat.nth_count (p := fun i => w i = 1) hwX]
  omega

theorem sol : type_of% @OMA.S_oeis_a286667.main := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 < 2 := by nlinarith
  have hL : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
    rw [show (1 : ℝ) / 2 = (Real.sqrt 2 / 2) ^ 2 by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num]
    exact Real.sqrt_sq (by positivity)
  have key : ∀ n : ℕ, 1 ≤ n → |(a n : ℝ) / n - (1 + Real.sqrt (1 / 2))| ≤ 2 / n := by
    intro n hn
    have hb := bound n n (by have := pellIter_length n; omega)
    rw [a_eq n hn, hL]
    set Z := ((pellIter n).take n).count 0 with hZ
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have e1 : ((n + Z : ℕ) : ℝ) / n - (1 + Real.sqrt 2 / 2) =
        ((Z : ℝ) - Real.sqrt 2 * n / 2) / n := by
      push_cast
      field_simp
      ring
    have e2 : (Z : ℝ) - Real.sqrt 2 * n / 2 = Real.sqrt 2 / 2 * (Real.sqrt 2 * Z - n) := by
      linear_combination (-(Z : ℝ) / 2) * hs
    rw [e1, abs_div, abs_of_pos hnpos]
    gcongr
    rw [e2, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 2 / 2)]
    have h3 : |Real.sqrt 2 * (Z : ℝ) - n| ≤ 2 := by
      rw [abs_sub_comm]
      exact hb
    nlinarith [abs_nonneg (Real.sqrt 2 * (Z : ℝ) - n)]
  have h0 : Filter.Tendsto (fun n : ℕ => (a n : ℝ) / n - (1 + Real.sqrt (1 / 2)))
      Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat 2)
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs]
    exact key n hn
  have h1 := h0.add_const (1 + Real.sqrt (1 / 2))
  simpa using h1

end OMA.P286667

theorem OMA.solution : type_of% @OMA.S_oeis_a286667.main := OMA.P286667.sol

