import OMAStatements.S_oeis_a223764

-- Problem: A223764: Number of n X 2 0..1 arrays with rows, columns and antidiagonals unimodal and
-- diagonals nondecreasing.
-- Credit: @EmadY (the owner of the agent is credited as the solver)
--
-- Proof idea (transfer matrix). Rows and antidiagonals have at most two cells, so they are always
-- unimodal. A binary column is unimodal exactly when, read from the top, it passes the automaton
-- with phases U (it may still rise), D (it may only fall) and Z (zeros only from here on). The
-- diagonal condition says that below a 1 in column 0 there is a 1 in column 1; that 1 is pending
-- exactly when column 0 is in phase D. Scanning the rows with the pair of column phases, the
-- numbers of completions of length n solve to polynomials in n, and
--   24 a(n) = n^4 + 6 n^3 + 35 n^2 + 30 n + 24.
-- Both of Barker's conjectures follow from this closed form.

namespace OMA.S_oeis_a223764

open PowerSeries

lemma fin2 (x : Fin 2) : x = 0 ∨ x = 1 := by fin_cases x <;> simp

lemma le_one' (x : Fin 2) : x ≤ 1 := by fin_cases x <;> decide

/-! ### Unimodal binary lists -/

lemma uni_pair (x y : Fin 2) : Unimodal [x, y] :=
  ⟨[x], [y], rfl, List.pairwise_singleton _ _, List.pairwise_singleton _ _⟩

lemma uni_zero (l : List (Fin 2)) : Unimodal (0 :: l) ↔ Unimodal l := by
  constructor
  · rintro ⟨l₁, l₂, h, h1, h2⟩
    cases l₁ with
    | nil =>
      rw [List.nil_append] at h
      subst h
      exact ⟨[], l, rfl, List.Pairwise.nil, (List.pairwise_cons.1 h2).2⟩
    | cons b l₁ =>
      rw [List.cons_append, List.cons.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨l₁, l₂, rfl, (List.pairwise_cons.1 h1).2, h2⟩
  · rintro ⟨l₁, l₂, rfl, h1, h2⟩
    exact ⟨0 :: l₁, l₂, rfl,
      List.pairwise_cons.2 ⟨fun y _ => by fin_cases y <;> decide, h1⟩, h2⟩

lemma uni_one (l : List (Fin 2)) : Unimodal (1 :: l) ↔ l.Pairwise (· ≥ ·) := by
  constructor
  · rintro ⟨l₁, l₂, h, h1, h2⟩
    cases l₁ with
    | nil =>
      rw [List.nil_append] at h
      subst h
      exact (List.pairwise_cons.1 h2).2
    | cons b l₁ =>
      rw [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hone : ∀ y ∈ l₁, y = 1 := fun y hy =>
        le_antisymm (le_one' y) ((List.pairwise_cons.1 h1).1 y hy)
      rw [List.pairwise_append]
      refine ⟨List.pairwise_of_forall_mem_list fun x hx y _ => ?_, h2, fun x hx y _ => ?_⟩
      · have := hone x hx
        subst this
        exact le_one' y
      · have := hone x hx
        subst this
        exact le_one' y
  · intro h
    exact ⟨[], 1 :: l, rfl, List.Pairwise.nil, List.pairwise_cons.2 ⟨fun y _ => le_one' y, h⟩⟩

/-- Column phases while reading from the top: `U` may still rise, `D` may only fall, `Z` must
stay at 0. -/
inductive Ph
  | U
  | D
  | Z
  deriving DecidableEq

/-- The next entry is allowed in the phase. -/
def okp : Ph → Fin 2 → Bool
  | .Z, x => decide (x = 0)
  | _, _ => true

/-- The phase after reading an entry. -/
def nx : Ph → Fin 2 → Ph
  | .U, x => if x = 0 then .U else .D
  | .D, x => if x = 0 then .Z else .D
  | .Z, _ => .Z

/-- The automaton accepts the rest of a column from a phase. -/
def acc : Ph → List (Fin 2) → Bool
  | _, [] => true
  | s, x :: l => okp s x && acc (nx s x) l

lemma accZ (l : List (Fin 2)) : acc .Z l = true ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp [acc]
  | cons x l ih => simp [acc, okp, nx, ih]

lemma accD (l : List (Fin 2)) : acc .D l = true ↔ l.Pairwise (· ≥ ·) := by
  induction l with
  | nil => simp [acc]
  | cons x l ih =>
    rcases fin2 x with rfl | rfl
    · simp only [acc, okp, nx, ↓reduceIte, Bool.true_and, accZ, List.pairwise_cons]
      constructor
      · intro h
        refine ⟨fun y hy => ?_, List.pairwise_of_forall_mem_list fun u hu v hv => ?_⟩
        · rw [h y hy]
        · rw [h u hu, h v hv]
      · rintro ⟨h, -⟩ y hy
        exact le_antisymm (h y hy) (by fin_cases y <;> decide)
    · simp [acc, okp, nx, ih, le_one']

lemma accU (l : List (Fin 2)) : acc .U l = true ↔ Unimodal l := by
  induction l with
  | nil =>
    simp only [acc, true_iff]
    exact ⟨[], [], rfl, List.Pairwise.nil, List.Pairwise.nil⟩
  | cons x l ih =>
    rcases fin2 x with rfl | rfl
    · simp [acc, okp, nx, ih, uni_zero]
    · simp [acc, okp, nx, accD, uni_one]

/-! ### Scanning the rows -/

/-- A row of the array. -/
abbrev Row := Fin 2 → Fin 2

/-- The diagonal condition along the rest of the array; `b` records a 1 in column 0 of the row
above. -/
def dg : Bool → List Row → Bool
  | _, [] => true
  | b, r :: L => (!b || decide (r 1 = 1)) && dg (decide (r 0 = 1)) L

lemma dg_iff (b : Bool) (L : List Row) : dg b L = true ↔
    (b = true → ∀ r ∈ L.head?, r 1 = 1) ∧ L.IsChain (fun r r' => r 0 ≤ r' 1) := by
  induction L generalizing b with
  | nil => simp [dg]
  | cons r L ih =>
    rw [dg, Bool.and_eq_true, ih, List.isChain_cons]
    rcases L with _ | ⟨r', L'⟩
    · cases b <;> simp
    · have key : (r 0 = 1 → r' 1 = 1) ↔ r 0 ≤ r' 1 := by
        rcases fin2 (r 0) with h | h <;> rcases fin2 (r' 1) with h' | h' <;> simp [h, h'] <;>
          decide
      cases b <;> simp [key]

/-- The joint scan: phases of both columns, with the diagonal condition pending in phase `D`
of column 0. -/
def W : Ph → Ph → List Row → Bool
  | _, _, [] => true
  | s, t, r :: L => okp s (r 0) && okp t (r 1) && (decide (s ≠ .D) || decide (r 1 = 1)) &&
      W (nx s (r 0)) (nx t (r 1)) L

lemma W_iff (s t : Ph) (L : List Row) : W s t L = true ↔
    acc s (L.map fun r => r 0) = true ∧ acc t (L.map fun r => r 1) = true ∧
      dg (decide (s = .D)) L = true := by
  induction L generalizing s t with
  | nil => simp [W, acc, dg]
  | cons r L ih =>
    simp only [W, List.map_cons, acc, dg, Bool.and_eq_true, ih]
    rcases fin2 (r 0) with h0 | h0 <;> rcases fin2 (r 1) with h1 | h1 <;>
      cases s <;> cases t <;> simp [h0, h1, okp, nx] <;> tauto

lemma valid_iff {n : ℕ} (A : Fin n → Row) : Valid A ↔ W .U .U (List.ofFn A) = true := by
  rw [W_iff, accU, accU, dg_iff, List.isChain_ofFn, List.map_ofFn, List.map_ofFn]
  have hrow : ∀ i, Unimodal (List.ofFn (A i)) := fun i => by
    simpa [List.ofFn_succ] using uni_pair (A i 0) (A i 1)
  have hdiag : (∀ i i' : Fin n, i'.val = i.val + 1 → A i 0 ≤ A i' 1) ↔
      ∀ (i : ℕ) (hi : i + 1 < n), A ⟨i, by omega⟩ 0 ≤ A ⟨i + 1, hi⟩ 1 := by
    constructor
    · intro H i hi
      exact H _ _ rfl
    · rintro H ⟨i, hi⟩ ⟨i', hi'⟩ h
      simp only at h
      subst h
      exact H i hi'
  constructor
  · rintro ⟨-, hcol, -, hd⟩
    exact ⟨hcol 0, hcol 1, fun h => absurd h (by decide), hdiag.1 hd⟩
  · rintro ⟨h0, h1, -, hd⟩
    refine ⟨hrow, ?_, fun i i' _ => uni_pair _ _, hdiag.2 hd⟩
    intro j
    fin_cases j
    · exact h0
    · exact h1

/-! ### Counting -/

/-- The number of arrays with `n` rows that pass a Boolean test. -/
def cnt (n : ℕ) (P : List Row → Bool) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Row => P (List.ofFn x) = true).card

lemma cnt_zero (P : List Row → Bool) : cnt 0 P = if P [] = true then 1 else 0 := by
  unfold cnt
  rw [Finset.card_filter]
  simp

lemma cnt_succ (n : ℕ) (P : List Row → Bool) :
    cnt (n + 1) P = ∑ r : Row, cnt n (fun l => P (r :: l)) := by
  unfold cnt
  simp only [Finset.card_filter]
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => Row)) _ _
    (fun q => by simp [Fin.consEquiv, List.ofFn_succ])).symm

lemma cnt_false (n : ℕ) : cnt n (fun _ => false) = 0 := by simp [cnt]

lemma sum_row (g : Row → ℕ) :
    ∑ r : Row, g r = g ![0, 0] + g ![0, 1] + g ![1, 0] + g ![1, 1] := by
  rw [← (finTwoArrowEquiv (Fin 2)).symm.sum_comp g, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, finTwoArrowEquiv, add_assoc]

lemma step (n : ℕ) (s t : Ph) : cnt (n + 1) (W s t) =
    cnt n (fun L => W s t (![0, 0] :: L)) + cnt n (fun L => W s t (![0, 1] :: L)) +
      cnt n (fun L => W s t (![1, 0] :: L)) + cnt n (fun L => W s t (![1, 1] :: L)) := by
  rw [cnt_succ, sum_row]

lemma CZZ (n : ℕ) : cnt n (W .Z .Z) = 1 := by
  induction n with
  | zero => simp [cnt_zero, W]
  | succ n ih =>
    rw [step]
    simp [W, okp, nx, cnt_false, ih]

lemma CZD (n : ℕ) : cnt n (W .Z .D) = n + 1 := by
  induction n with
  | zero => simp [cnt_zero, W]
  | succ n ih =>
    rw [step]
    simp [W, okp, nx, cnt_false, ih, CZZ]
    try omega

lemma CZU (n : ℕ) : 2 * cnt n (W .Z .U) = n ^ 2 + n + 2 := by
  induction n with
  | zero => simp [cnt_zero, W]
  | succ n ih =>
    rw [step]
    simp [W, okp, nx, cnt_false, CZD]
    nlinarith [ih]

lemma CDZ (n : ℕ) : cnt (n + 1) (W .D .Z) = 0 := by
  rw [step]
  simp [W, okp, nx, cnt_false]

lemma CDD (n : ℕ) : 2 * cnt n (W .D .D) = n ^ 2 + n + 2 := by
  induction n with
  | zero => simp [cnt_zero, W]
  | succ n ih =>
    rw [step]
    simp [W, okp, nx, cnt_false, CZD]
    nlinarith [ih]

lemma CDU (n : ℕ) : cnt n (W .D .U) = cnt n (W .D .D) := by
  cases n with
  | zero => simp [cnt_zero, W]
  | succ n =>
    rw [step, step]
    simp [W, okp, nx, cnt_false]

lemma CUZ (n : ℕ) : cnt (n + 1) (W .U .Z) = 2 := by
  induction n with
  | zero =>
    rw [step]
    simp [W, okp, nx, cnt_false, cnt_zero]
  | succ n ih =>
    rw [step]
    simp [W, okp, nx, cnt_false, ih, CDZ]

lemma CUZDZ (n : ℕ) : cnt n (W .U .Z) + cnt n (W .D .Z) = 2 := by
  cases n with
  | zero => simp [cnt_zero, W]
  | succ n => rw [CUZ, CDZ]

lemma CUD (n : ℕ) : 6 * cnt n (W .U .D) = n ^ 3 + 17 * n + 6 := by
  induction n with
  | zero => simp [cnt_zero, W]
  | succ n ih =>
    rw [step]
    simp [W, okp, nx, cnt_false]
    nlinarith [ih, CUZDZ n, CDD n]

lemma CUU (n : ℕ) : 24 * cnt n (W .U .U) = n ^ 4 + 6 * n ^ 3 + 35 * n ^ 2 + 30 * n + 24 := by
  induction n with
  | zero => simp [cnt_zero, W]
  | succ n ih =>
    rw [step]
    simp [W, okp, nx, cnt_false, CDU]
    nlinarith [ih, CUD n, CDD n]

lemma a_eq (n : ℕ) : a n = cnt n (W .U .U) := by
  classical
  unfold a cnt
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact congrArg Finset.card (Finset.filter_congr fun A _ => valid_iff A)

lemma a_formula (n : ℕ) : 24 * a n = n ^ 4 + 6 * n ^ 3 + 35 * n ^ 2 + 30 * n + 24 := by
  rw [a_eq]
  exact CUU n

lemma a_q (n : ℕ) :
    (a n : ℚ) = ((n : ℚ) ^ 4 + 6 * n ^ 3 + 35 * n ^ 2 + 30 * n + 24) / 24 := by
  have h := congrArg (Nat.cast : ℕ → ℚ) (a_formula n)
  push_cast at h
  linarith

theorem recurrence (n : ℕ) (hn : 5 < n) : (a n : ℤ) =
    5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have h : ∀ k : ℕ, (24 : ℤ) * a k = (k : ℤ) ^ 4 + 6 * k ^ 3 + 35 * k ^ 2 + 30 * k + 24 :=
    fun k => by exact_mod_cast a_formula k
  rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
    show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
    show m + 6 - 5 = m + 1 by omega]
  have h6 := h (m + 6)
  have h5 := h (m + 5)
  have h4 := h (m + 4)
  have h3 := h (m + 3)
  have h2 := h (m + 2)
  have h1 := h (m + 1)
  push_cast at h6 h5 h4 h3 h2 h1
  linarith

theorem gf_eq : gf = X * (2 - 2 * X + X ^ 2) ^ 2 * ((1 - X) ^ 5)⁻¹ := by
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  have e1 : gf * (1 - X) ^ 5 = gf - C 5 * (gf * X ^ 1) + C 10 * (gf * X ^ 2) -
      C 10 * (gf * X ^ 3) + C 5 * (gf * X ^ 4) - gf * X ^ 5 := by
    simp only [map_ofNat]
    ring
  have e2 : (X : ℚ⟦X⟧) * (2 - 2 * X + X ^ 2) ^ 2 =
      C 4 * X ^ 1 - C 8 * X ^ 2 + C 8 * X ^ 3 - C 4 * X ^ 4 + X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k gf = if k = 0 then (0 : ℚ) else (a k : ℚ) := fun k => by
    rw [gf, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_mul_X_pow', hc, coeff_C]
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> simp [a_q] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
      show m + 6 - 5 = m + 1 by omega, show ¬ m + 6 = 0 by omega,
      show ¬ m + 5 = 0 by omega, show ¬ m + 4 = 0 by omega, show ¬ m + 3 = 0 by omega,
      show ¬ m + 2 = 0 by omega, show ¬ m + 1 = 0 by omega, show 1 ≤ m + 6 by omega,
      show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega, show 4 ≤ m + 6 by omega,
      show 5 ≤ m + 6 by omega, show ¬ m + 6 = 1 by omega, show ¬ m + 6 = 2 by omega,
      show ¬ m + 6 = 3 by omega, show ¬ m + 6 = 4 by omega, show ¬ m + 6 = 5 by omega,
      if_true, if_false]
    rw [a_q, a_q, a_q, a_q, a_q, a_q]
    push_cast
    ring

theorem conjecture :
    gf = X * (2 - 2 * X + X ^ 2) ^ 2 * ((1 - X) ^ 5)⁻¹ ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) =
      5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) :=
  ⟨gf_eq, recurrence⟩

end OMA.S_oeis_a223764

theorem OMA.solution : type_of% @OMA.S_oeis_a223764.main :=
  OMA.S_oeis_a223764.conjecture
