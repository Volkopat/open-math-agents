import OMAStatements.S_oeis_a211839

/-!
OEIS A211839 (R. H. Hardin, Apr 21 2012): Number of nonnegative integer arrays of length n+6 with new values 0 upwards introduced in order, no three adjacent elements equal, and containing the value n+1.
Conjectures from Colin Barker, Jul 20 2018: G.f.: x*(664 - 3355*x + 9383*x^2 - 15720*x^3 + 16980*x^4 - 11983*x^5 + 5367*x^6 - 1390*x^7 + 159*x^8) / (1 - x)^9. a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>9.

Proof. Prefixes of length m + 1 are counted by their number b of values and whether their last two
entries are equal (`P`); appending an entry with Fin.snoc (`rgs_snoc`, `no3_snoc`, `nb_snoc`,
`fl_snoc`) gives P(m + 1, b, true) = P(m, b, false) and P(m + 1, b, false) = (b - 1)(P(m, b, false) 
+ P(m, b, true)) + P(m, b - 1, false) + P(m, b - 1, true) (`P_succ_true`, `P_succ_false`). With r
repeated positions, P(m, m + 1 - r, f) is a polynomial in m for m >= r (`Q0`, `Q1`, ...). An array
that introduces its values in order contains n + 1 exactly when it has at least n + 2 values
(`contains_iff`), so a(n) is the sum of these polynomials for r <= 4 at m = n + 5 (`a_eq`,
`a_poly`); the g.f. and the recurrence follow by comparing coefficients.
-/

namespace OMA.S_oeis_a211839

open PowerSeries Finset


instance {L N : ℕ} : DecidablePred (@newInOrder L N) := fun x => by unfold newInOrder; infer_instance

instance {L N : ℕ} : DecidablePred (@noThree L N) := fun x => by unfold noThree; infer_instance

/-- One more than the largest entry (0 for the empty array): the number of values of an array
that introduces them in order. -/
def nb {L N : ℕ} (y : Fin L → Fin N) : ℕ := univ.sup (fun i => (y i : ℕ) + 1)

lemma le_nb {L N : ℕ} (y : Fin L → Fin N) (i : Fin L) : (y i : ℕ) + 1 ≤ nb y :=
  Finset.le_sup (f := fun i => (y i : ℕ) + 1) (mem_univ i)

lemma lt_nb {L N : ℕ} (y : Fin L → Fin N) (c : ℕ) (h : c < nb y) : ∃ i, c < (y i : ℕ) + 1 := by
  obtain ⟨i, -, hi⟩ := Finset.lt_sup_iff.mp h
  exact ⟨i, hi⟩

/-- The last two entries are equal. -/
def fl {L N : ℕ} (x : Fin L → Fin N) : Prop :=
  ∃ i : Fin L, ∃ j : Fin L, (i : ℕ) + 1 = j ∧ (j : ℕ) + 1 = L ∧ x i = x j

instance {L N : ℕ} : DecidablePred (@fl L N) := fun x => by unfold fl; infer_instance

lemma snoc_lt {m N : ℕ} (y : Fin (m + 1) → Fin N) (w : Fin N) (j : ℕ) (hj : j < m + 2) (h : j < m + 1) :
    (Fin.snoc y w : Fin (m + 2) → Fin N) ⟨j, hj⟩ = y ⟨j, h⟩ := by
  simp [Fin.snoc, h]

lemma nb_snoc {m N : ℕ} (y : Fin (m + 1) → Fin N) (w : Fin N) :
    nb (Fin.snoc y w : Fin (m + 2) → Fin N) = max (nb y) ((w : ℕ) + 1) := by
  apply le_antisymm
  · unfold nb
    rw [Finset.sup_le_iff]
    intro i _
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp only [Fin.snoc_castSucc]; exact le_max_of_le_left (le_nb y i)
  · apply max_le
    · show univ.sup (fun i => (y i : ℕ) + 1) ≤ _
      apply Finset.sup_le
      intro i _
      have := le_nb (Fin.snoc y w : Fin (m + 2) → Fin N) i.castSucc
      rw [Fin.snoc_castSucc] at this
      exact this
    · have := le_nb (Fin.snoc y w : Fin (m + 2) → Fin N) (Fin.last _)
      rw [Fin.snoc_last] at this
      exact this

lemma rgs_snoc {m N : ℕ} (y : Fin (m + 1) → Fin N) (w : Fin N) :
    newInOrder (Fin.snoc y w : Fin (m + 2) → Fin N) ↔ newInOrder y ∧ (w : ℕ) ≤ nb y := by
  unfold newInOrder
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · rcases h i.castSucc with h0 | ⟨j, hj, hv⟩
      · left
        simpa using h0
      · right
        obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr (Fin.ne_last_of_lt hj)
        refine ⟨j', Fin.castSucc_lt_castSucc_iff.mp hj, ?_⟩
        simpa using hv
    · rcases h (Fin.last _) with h0 | ⟨j, hj, hv⟩
      · rw [Fin.snoc_last] at h0
        rw [h0]
        exact Nat.zero_le _
      · rw [Fin.snoc_last] at hv
        obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr (Fin.ne_last_of_lt hj)
        rw [Fin.snoc_castSucc] at hv
        exact le_trans hv (le_nb y j')
  · rintro ⟨h, hw⟩ i
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last]
      rcases Nat.eq_zero_or_pos (w : ℕ) with h0 | h0
      · exact Or.inl h0
      · obtain ⟨j, hj⟩ := lt_nb y ((w : ℕ) - 1) (by omega)
        exact Or.inr ⟨j.castSucc, Fin.castSucc_lt_last j, by rw [Fin.snoc_castSucc]; omega⟩
    | cast i =>
      rcases h i with h0 | ⟨j, hj, hv⟩
      · left
        simpa using h0
      · right
        exact ⟨j.castSucc, Fin.castSucc_lt_castSucc_iff.mpr hj, by simpa using hv⟩

lemma fl_snoc {m N : ℕ} (y : Fin (m + 1) → Fin N) (w : Fin N) :
    fl (Fin.snoc y w : Fin (m + 2) → Fin N) ↔ y (Fin.last m) = w := by
  unfold fl
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩, hij, hjL, hv⟩
    simp only at hij hjL
    have e1 : (⟨j, hj⟩ : Fin (m + 2)) = Fin.last (m + 1) := Fin.ext (by simp; omega)
    have e2 : (⟨i, hi⟩ : Fin (m + 2)) = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
    rw [e1, e2, Fin.snoc_last, snoc_lt y w m (by omega) (by omega)] at hv
    exact hv
  · intro h
    refine ⟨⟨m, by omega⟩, Fin.last (m + 1), by simp, by simp, ?_⟩
    rw [snoc_lt y w m (by omega) (by omega), Fin.snoc_last]
    exact h

lemma no3_snoc {m N : ℕ} (y : Fin (m + 1) → Fin N) (w : Fin N) :
    noThree (Fin.snoc y w : Fin (m + 2) → Fin N) ↔ noThree y ∧ ¬ (fl y ∧ y (Fin.last m) = w) := by
  unfold noThree fl
  constructor
  · intro h
    refine ⟨fun ⟨i, hi⟩ h2 => ?_, ?_⟩
    · simp only at h2 ⊢
      have := h ⟨i, by omega⟩ (by simp only; omega)
      simp only at this
      rw [snoc_lt y w i (by omega) (by omega), snoc_lt y w (i + 1) (by omega) (by omega),
        snoc_lt y w (i + 2) (by omega) (by omega)] at this
      exact this
    · rintro ⟨⟨⟨i, hi⟩, ⟨j, hj⟩, hij, hjL, hv⟩, hw⟩
      simp only at hij hjL
      apply h ⟨i, by omega⟩ (by simp only; omega)
      simp only
      have e3 : (⟨i + 2, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) := Fin.ext (by simp; omega)
      rw [snoc_lt y w i (by omega) (by omega), snoc_lt y w (i + 1) (by omega) (by omega), e3,
        Fin.snoc_last]
      have e1 : (⟨i + 1, by omega⟩ : Fin (m + 1)) = ⟨j, hj⟩ := Fin.ext (by simp; omega)
      have e2 : (⟨j, hj⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp; omega)
      rw [e1]
      refine ⟨hv, ?_⟩
      rw [e2]
      exact hw
  · rintro ⟨h, hw⟩ ⟨i, hi⟩ h2
    simp only at h2 ⊢
    rcases Nat.lt_or_ge (i + 2) (m + 1) with hlt | hge
    · rw [snoc_lt y w i (by omega) (by omega), snoc_lt y w (i + 1) (by omega) (by omega),
        snoc_lt y w (i + 2) (by omega) (by omega)]
      exact h ⟨i, by omega⟩ (by simp only; omega)
    · have e3 : (⟨i + 2, h2⟩ : Fin (m + 2)) = Fin.last (m + 1) := Fin.ext (by simp; omega)
      rw [snoc_lt y w i (by omega) (by omega), snoc_lt y w (i + 1) (by omega) (by omega), e3,
        Fin.snoc_last]
      rintro ⟨h1, h3⟩
      apply hw
      have e2 : (⟨i + 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp; omega)
      rw [e2] at h1 h3
      exact ⟨⟨⟨i, by omega⟩, Fin.last m, by simp; omega, by simp, h1⟩, h3⟩

lemma val_le {L N : ℕ} (y : Fin L → Fin N) (hy : newInOrder y) (i : Fin L) : (y i : ℕ) ≤ i := by
  obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k := ⟨_, rfl⟩
  induction k using Nat.strong_induction_on generalizing i with
  | _ k ih =>
    rcases hy i with h | ⟨j, hj, hv⟩
    · omega
    · rw [Fin.lt_def] at hj
      have := ih j (by omega) j rfl
      omega

lemma nb_le_len {L N : ℕ} (y : Fin L → Fin N) (hy : newInOrder y) : nb y ≤ L :=
  Finset.sup_le (fun i _ => by have := val_le y hy i; have := i.isLt; omega)

lemma contains_iff {L N : ℕ} (x : Fin L → Fin N) (hx : newInOrder x) (c : ℕ) :
    (∃ i, (x i : ℕ) = c) ↔ c < nb x := by
  constructor
  · rintro ⟨i, hi⟩
    have := le_nb x i
    omega
  · intro h
    obtain ⟨i, hi⟩ := lt_nb x c h
    obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image (univ.filter (fun i => c ≤ (x i : ℕ)))
      (fun i => (i : ℕ)) ⟨i, by simp only [mem_filter, mem_univ, true_and]; omega⟩
    simp only [mem_filter, mem_univ, true_and] at hi0 hmin
    refine ⟨i0, ?_⟩
    rcases hx i0 with h0 | ⟨j, hj, hv⟩
    · omega
    · by_contra hne
      have hj' : ¬ (c ≤ (x j : ℕ)) := fun hc => by
        have := hmin j hc
        rw [Fin.lt_def] at hj
        omega
      omega

/-- The arrays of length m + 1 with entries in Fin N that introduce their values in order and have
no three adjacent equal entries, with b values, and with equal (f = true) or different last two
entries. -/
def P (N m b : ℕ) (f : Bool) : ℕ :=
  ((univ : Finset (Fin (m + 1) → Fin N)).filter (fun y => newInOrder y ∧ noThree y ∧ nb y = b ∧
    decide (fl y) = f)).card

lemma P_succ_true (N m b : ℕ) : P N (m + 1) b true = P N m b false := by
  unfold P
  refine card_bij' (fun x _ => Fin.init x) (fun y _ => Fin.snoc y (y (Fin.last m))) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq, decide_eq_false_iff_not] at hx ⊢
    obtain ⟨hr, hn, hb, hf⟩ := hx
    have e : x = Fin.snoc (Fin.init x) (x (Fin.last _)) := (Fin.snoc_init_self x).symm
    rw [e, fl_snoc] at hf
    rw [e, rgs_snoc] at hr
    rw [e, no3_snoc] at hn
    rw [e, nb_snoc, ← hf, max_eq_left (le_nb _ _)] at hb
    exact ⟨hr.1, hn.1, hb, fun h => hn.2 ⟨h, hf⟩⟩
  · intro y hy
    simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq, decide_eq_false_iff_not] at hy ⊢
    obtain ⟨hr, hn, hb, hf⟩ := hy
    refine ⟨(rgs_snoc y _).mpr ⟨hr, by have := le_nb y (Fin.last m); omega⟩,
      (no3_snoc y _).mpr ⟨hn, fun h => hf h.1⟩, ?_, (fl_snoc y _).mpr rfl⟩
    rw [nb_snoc, max_eq_left (le_nb y _), hb]
  · intro x hx
    simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq] at hx
    have hf := hx.2.2.2
    have e : x = Fin.snoc (Fin.init x) (x (Fin.last _)) := (Fin.snoc_init_self x).symm
    rw [e, fl_snoc] at hf
    rw [hf]
    exact Fin.snoc_init_self x
  · intro y _
    simp

lemma card_w (N b c v : ℕ) (hv : v < c) (hcN : c < N) :
    ((univ : Finset (Fin N)).filter
      (fun w : Fin N => (w : ℕ) ≤ c ∧ max c ((w : ℕ) + 1) = b ∧ v ≠ (w : ℕ))).card =
      if c = b then b - 1 else if c + 1 = b then 1 else 0 := by
  split_ifs with h1 h2
  · subst h1
    have e : (univ : Finset (Fin N)).filter
        (fun w : Fin N => (w : ℕ) ≤ c ∧ max c ((w : ℕ) + 1) = c ∧ v ≠ (w : ℕ)) =
        (Finset.Iio (⟨c, hcN⟩ : Fin N)).erase ⟨v, by omega⟩ := by
      ext w
      simp only [mem_filter, mem_univ, true_and, mem_erase, mem_Iio, ne_eq, Fin.ext_iff, Fin.lt_def]
      omega
    rw [e, card_erase_of_mem (by simp [Fin.lt_def]; omega), Fin.card_Iio]
  · rw [card_eq_one]
    refine ⟨⟨c, hcN⟩, ?_⟩
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]
    omega
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro w _
    omega

lemma split_fl (N m b : ℕ) :
    ((univ : Finset (Fin (m + 1) → Fin N)).filter (fun y => newInOrder y ∧ noThree y ∧ nb y = b)).card =
      P N m b false + P N m b true := by
  unfold P
  rw [card_eq_sum_card_fiberwise (f := fun y => decide (fl y)) (t := univ)
      (fun _ _ => Finset.mem_coe.mpr (mem_univ _)), Fintype.sum_bool,
    add_comm, filter_filter, filter_filter]
  congr 1 <;> (congr 1; ext y; simp only [mem_filter, mem_univ, true_and]; tauto)

lemma P_succ_false (N m b : ℕ) (hb : 1 ≤ b) (hN : m + 2 ≤ N) :
    P N (m + 1) b false =
      (b - 1) * (P N m b false + P N m b true) + (P N m (b - 1) false + P N m (b - 1) true) := by
  have step1 : P N (m + 1) b false = ∑ y : Fin (m + 1) → Fin N,
      if newInOrder y ∧ noThree y then
        ((univ : Finset (Fin N)).filter (fun w : Fin N => (w : ℕ) ≤ nb y ∧
          max (nb y) ((w : ℕ) + 1) = b ∧ (y (Fin.last m) : ℕ) ≠ (w : ℕ))).card else 0 := by
    unfold P
    rw [card_eq_sum_card_fiberwise (f := Fin.init) (t := univ) (by simp)]
    refine sum_congr rfl (fun y _ => ?_)
    split_ifs with hy
    · refine card_bij' (fun x _ => x (Fin.last _)) (fun w _ => Fin.snoc y w) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [mem_filter, mem_univ, true_and, decide_eq_false_iff_not] at hx ⊢
        obtain ⟨⟨hr, hn, hb', hf⟩, hinit⟩ := hx
        have e : x = Fin.snoc y (x (Fin.last _)) := by
          rw [← hinit]
          exact (Fin.snoc_init_self x).symm
        rw [e, rgs_snoc] at hr
        rw [e, nb_snoc] at hb'
        rw [e, fl_snoc] at hf
        exact ⟨hr.2, hb', fun h => hf (Fin.ext h)⟩
      · intro w hw
        simp only [mem_filter, mem_univ, true_and, decide_eq_false_iff_not] at hw ⊢
        obtain ⟨hle, hmax, hne⟩ := hw
        refine ⟨⟨(rgs_snoc y w).mpr ⟨hy.1, hle⟩,
          (no3_snoc y w).mpr ⟨hy.2, fun h => hne (congrArg Fin.val h.2)⟩,
          by rw [nb_snoc]; exact hmax, fun h => hne (congrArg Fin.val ((fl_snoc y w).mp h))⟩, by simp⟩
      · intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        rw [← hx.2]
        exact Fin.snoc_init_self x
      · intro w _
        simp
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro x hx hinit
      simp only [mem_filter, mem_univ, true_and] at hx
      obtain ⟨hr, hn, _, _⟩ := hx
      apply hy
      have e : x = Fin.snoc y (x (Fin.last _)) := by
        rw [← hinit]
        exact (Fin.snoc_init_self x).symm
      rw [e, rgs_snoc] at hr
      rw [e, no3_snoc] at hn
      exact ⟨hr.1, hn.1⟩
  have step2 : ∀ y : Fin (m + 1) → Fin N, (if newInOrder y ∧ noThree y then
        ((univ : Finset (Fin N)).filter (fun w : Fin N => (w : ℕ) ≤ nb y ∧
          max (nb y) ((w : ℕ) + 1) = b ∧ (y (Fin.last m) : ℕ) ≠ (w : ℕ))).card else 0) =
      (if newInOrder y ∧ noThree y ∧ nb y = b then b - 1 else 0) +
        (if newInOrder y ∧ noThree y ∧ nb y = b - 1 then 1 else 0) := by
    intro y
    by_cases hy : newInOrder y ∧ noThree y
    · rw [if_pos hy, card_w N b (nb y) (y (Fin.last m)) (le_nb y _)
        (by have := nb_le_len y hy.1; omega)]
      simp only [hy.1, hy.2, true_and]
      split_ifs <;> omega
    · rw [if_neg hy, if_neg (fun h => hy ⟨h.1, h.2.1⟩), if_neg (fun h => hy ⟨h.1, h.2.1⟩)]
  rw [step1, sum_congr rfl (fun y _ => step2 y), sum_add_distrib, ← split_fl, ← split_fl]
  simp only [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul]
  ring

lemma P_succ_false_q (N m b : ℕ) (hb : 1 ≤ b) (hN : m + 2 ≤ N) :
    (P N (m + 1) b false : ℚ) = ((b : ℚ) - 1) * ((P N m b false : ℚ) + P N m b true) +
      ((P N m (b - 1) false : ℚ) + P N m (b - 1) true) := by
  rw [P_succ_false N m b hb hN]
  push_cast [Nat.cast_sub hb]
  ring

lemma P_zero_b (N m : ℕ) (f : Bool) : P N m 0 f = 0 := by
  unfold P
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro y - ⟨_, _, hb, _⟩
  have := le_nb y 0
  omega

lemma P_big_b (N m b : ℕ) (f : Bool) (hb : m + 1 < b) : P N m b f = 0 := by
  unfold P
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro y - ⟨hr, _, hnb, _⟩
  have := nb_le_len y hr
  omega

lemma P_one_f (N : ℕ) (hN : 1 ≤ N) : P N 0 1 false = 1 := by
  unfold P
  rw [card_eq_one]
  refine ⟨fun _ => ⟨0, hN⟩, ?_⟩
  ext y
  simp only [mem_filter, mem_univ, true_and, mem_singleton, decide_eq_false_iff_not]
  constructor
  · rintro ⟨hr, -, -, -⟩
    funext i
    have := val_le y hr i
    have hi : (i : ℕ) = 0 := by have := i.isLt; omega
    ext
    simp only
    omega
  · rintro rfl
    refine ⟨fun i => Or.inl rfl, fun i h => by have := i.isLt; omega, ?_, ?_⟩
    · unfold nb
      simp
    · unfold fl
      rintro ⟨i, j, hij, hj, -⟩
      have := i.isLt
      omega

lemma P_one_t (N : ℕ) : P N 0 1 true = 0 := by
  unfold P
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro y - ⟨-, -, -, hf⟩
  simp only [decide_eq_true_eq] at hf
  unfold fl at hf
  obtain ⟨i, j, hij, hj, -⟩ := hf
  have := i.isLt
  omega

lemma Q0 (N m : ℕ) (hN : m + 1 ≤ N) : P N m (m + 1) false = 1 ∧ P N m (m + 1) true = 0 := by
  induction m with
  | zero => exact ⟨P_one_f N hN, P_one_t N⟩
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    refine ⟨?_, ?_⟩
    · rw [P_succ_false N m (m + 1 + 1) (by omega) (by omega), show m + 1 + 1 - 1 = m + 1 by omega, h1,
        h2, P_big_b N m (m + 1 + 1) false (by omega), P_big_b N m (m + 1 + 1) true (by omega)]
      ring
    · rw [P_succ_true, P_big_b N m (m + 1 + 1) false (by omega)]

lemma Q1 (N m : ℕ) (hm : 1 ≤ m) (hN : m + 1 ≤ N) :
    (P N m (m + 1 - 1) false : ℚ) = -1 + (1 / 2) * (m : ℚ) + (1 / 2) * (m : ℚ) ^ 2 ∧
      (P N m (m + 1 - 1) true : ℚ) = 1 := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [show 1 + 1 - 1 = 1 from rfl]
    refine ⟨?_, ?_⟩
    · rw [P_succ_false N 0 1 le_rfl (by omega), P_zero_b, P_zero_b]
      norm_num
    · rw [P_succ_true]
      exact_mod_cast (Q0 N 0 (by omega)).1
  | succ m hm ih =>
    obtain ⟨ihF, ihT⟩ := ih (by omega)
    have pF : (P N m (m + 1) false : ℚ) = 1 := by exact_mod_cast (Q0 N m (by omega)).1
    have pT : (P N m (m + 1) true : ℚ) = 0 := by exact_mod_cast (Q0 N m (by omega)).2
    rw [show m + 1 + 1 - 1 = m + 1 by omega]
    refine ⟨?_, ?_⟩
    · rw [P_succ_false_q N m (m + 1) (by omega) (by omega), show m + 1 - 1 = m + 1 - 1 by omega,
        pF, pT, ihF, ihT]
      push_cast [show 0 ≤ m + 1 by omega]
      ring
    · rw [P_succ_true, pF]

lemma Q2 (N m : ℕ) (hm : 2 ≤ m) (hN : m + 1 ≤ N) :
    (P N m (m + 1 - 2) false : ℚ) = 2 - (5 / 12) * (m : ℚ) - (5 / 8) * (m : ℚ) ^ 2 - (1 / 12) * (m : ℚ) ^ 3 + (1 / 8) * (m : ℚ) ^ 4 ∧
      (P N m (m + 1 - 2) true : ℚ) = -1 - (1 / 2) * (m : ℚ) + (1 / 2) * (m : ℚ) ^ 2 := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [show 2 + 1 - 2 = 1 from rfl]
    refine ⟨?_, ?_⟩
    · rw [P_succ_false N 1 1 le_rfl (by omega), P_zero_b, P_zero_b]
      norm_num
    · have h := (Q1 N 1 (le_refl _) (by omega)).1
      norm_num at h
      rw [P_succ_true, h]
      norm_num
  | succ m hm ih =>
    obtain ⟨ihF, ihT⟩ := ih (by omega)
    obtain ⟨pF, pT⟩ := Q1 N m (by omega) (by omega)
    rw [show m + 1 + 1 - 2 = m + 1 - 1 by omega]
    refine ⟨?_, ?_⟩
    · rw [P_succ_false_q N m (m + 1 - 1) (by omega) (by omega), show m + 1 - 1 - 1 = m + 1 - 2 by omega,
        pF, pT, ihF, ihT]
      push_cast [show 1 ≤ m + 1 by omega]
      ring
    · rw [P_succ_true, pF]
      push_cast
      ring

lemma Q3 (N m : ℕ) (hm : 3 ≤ m) (hN : m + 1 ≤ N) :
    (P N m (m + 1 - 3) false : ℚ) = -3 - (3 / 2) * (m : ℚ) + (35 / 24) * (m : ℚ) ^ 2 + (5 / 48) * (m : ℚ) ^ 3 + (1 / 48) * (m : ℚ) ^ 4 - (5 / 48) * (m : ℚ) ^ 5 + (1 / 48) * (m : ℚ) ^ 6 ∧
      (P N m (m + 1 - 3) true : ℚ) = 2 + (1 / 12) * (m : ℚ) + (3 / 8) * (m : ℚ) ^ 2 - (7 / 12) * (m : ℚ) ^ 3 + (1 / 8) * (m : ℚ) ^ 4 := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [show 3 + 1 - 3 = 1 from rfl]
    refine ⟨?_, ?_⟩
    · rw [P_succ_false N 2 1 le_rfl (by omega), P_zero_b, P_zero_b]
      norm_num
    · have h := (Q2 N 2 (le_refl _) (by omega)).1
      norm_num at h
      rw [P_succ_true, h]
      norm_num
  | succ m hm ih =>
    obtain ⟨ihF, ihT⟩ := ih (by omega)
    obtain ⟨pF, pT⟩ := Q2 N m (by omega) (by omega)
    rw [show m + 1 + 1 - 3 = m + 1 - 2 by omega]
    refine ⟨?_, ?_⟩
    · rw [P_succ_false_q N m (m + 1 - 2) (by omega) (by omega), show m + 1 - 2 - 1 = m + 1 - 3 by omega,
        pF, pT, ihF, ihT]
      push_cast [show 2 ≤ m + 1 by omega, show 1 ≤ m by omega]
      ring
    · rw [P_succ_true, pF]
      push_cast
      ring

lemma Q4 (N m : ℕ) (hm : 4 ≤ m) (hN : m + 1 ≤ N) :
    (P N m (m + 1 - 4) false : ℚ) = 2 + (123 / 40) * (m : ℚ) + (517 / 288) * (m : ℚ) ^ 2 - (75 / 32) * (m : ℚ) ^ 3 + (667 / 1152) * (m : ℚ) ^ 4 - (1 / 5) * (m : ℚ) ^ 5 + (71 / 576) * (m : ℚ) ^ 6 - (1 / 32) * (m : ℚ) ^ 7 + (1 / 384) * (m : ℚ) ^ 8 ∧
      (P N m (m + 1 - 4) true : ℚ) = -(29 / 6) * (m : ℚ) + (21 / 8) * (m : ℚ) ^ 2 - (23 / 16) * (m : ℚ) ^ 3 + (41 / 48) * (m : ℚ) ^ 4 - (11 / 48) * (m : ℚ) ^ 5 + (1 / 48) * (m : ℚ) ^ 6 := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [show 4 + 1 - 4 = 1 from rfl]
    refine ⟨?_, ?_⟩
    · rw [P_succ_false N 3 1 le_rfl (by omega), P_zero_b, P_zero_b]
      norm_num
    · have h := (Q3 N 3 (le_refl _) (by omega)).1
      norm_num at h
      rw [P_succ_true, h]
      norm_num
  | succ m hm ih =>
    obtain ⟨ihF, ihT⟩ := ih (by omega)
    obtain ⟨pF, pT⟩ := Q3 N m (by omega) (by omega)
    rw [show m + 1 + 1 - 4 = m + 1 - 3 by omega]
    refine ⟨?_, ?_⟩
    · rw [P_succ_false_q N m (m + 1 - 3) (by omega) (by omega), show m + 1 - 3 - 1 = m + 1 - 4 by omega,
        pF, pT, ihF, ihT]
      push_cast [show 3 ≤ m + 1 by omega, show 2 ≤ m by omega]
      ring
    · rw [P_succ_true, pF]
      push_cast
      ring

lemma a_eq (n : ℕ) : a n =
    (P (n + 6) (n + 5) (n + 6) false + P (n + 6) (n + 5) (n + 6) true) +
    (P (n + 6) (n + 5) (n + 5) false + P (n + 6) (n + 5) (n + 5) true) +
    (P (n + 6) (n + 5) (n + 4) false + P (n + 6) (n + 5) (n + 4) true) +
    (P (n + 6) (n + 5) (n + 3) false + P (n + 6) (n + 5) (n + 3) true) +
    (P (n + 6) (n + 5) (n + 2) false + P (n + 6) (n + 5) (n + 2) true) := by
  unfold a
  have hg : ∀ x : Fin (n + 6) → Fin (n + 6), good x ↔ newInOrder x ∧ noThree x ∧ n + 2 ≤ nb x := by
    intro x
    unfold good
    constructor
    · rintro ⟨hr, hn, hc⟩
      exact ⟨hr, hn, by have := (contains_iff x hr (n + 1)).mp hc; omega⟩
    · rintro ⟨hr, hn, hc⟩
      exact ⟨hr, hn, (contains_iff x hr (n + 1)).mpr (by omega)⟩
  rw [filter_congr (fun x _ => hg x)]
  rw [card_eq_sum_card_fiberwise (f := nb) (t := Icc (n + 2) (n + 6)) (by
    intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    simp only [coe_Icc, Set.mem_Icc]
    exact ⟨hx.2.2, nb_le_len x hx.1⟩)]
  have hs : ∀ b, n + 2 ≤ b →
      (((univ : Finset (Fin (n + 6) → Fin (n + 6))).filter
        (fun x => newInOrder x ∧ noThree x ∧ n + 2 ≤ nb x)).filter (fun x => nb x = b)).card =
        P (n + 6) (n + 5) b false + P (n + 6) (n + 5) b true := by
    intro b hb
    rw [filter_filter, ← split_fl]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨hr, hn, _⟩, hx⟩
      exact ⟨hr, hn, hx⟩
    · rintro ⟨hr, hn, hx⟩
      exact ⟨⟨hr, hn, by omega⟩, hx⟩
  rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), Icc_self, sum_singleton, hs (n + 6) (by omega), hs (n + 5) (by omega), hs (n + 4) (by omega), hs (n + 3) (by omega), hs (n + 2) (by omega)]
  ring

/-- a(n) as a polynomial in n. -/
lemma a_poly (n : ℕ) : (a n : ℚ) = 159 + (8973 / 40) * (n : ℚ) + (47569 / 288) * (n : ℚ) ^ 2 + (7763 / 96) * (n : ℚ) ^ 3 + (31603 / 1152) * (n : ℚ) ^ 4 + (499 / 80) * (n : ℚ) ^ 5 + (515 / 576) * (n : ℚ) ^ 6 + (7 / 96) * (n : ℚ) ^ 7 + (1 / 384) * (n : ℚ) ^ 8 := by
  have e0F : (P (n + 6) (n + 5) (n + 6) false : ℚ) = 1 := by
    have h := (Q0 (n + 6) (n + 5) (by omega)).1
    rw [show n + 5 + 1 = n + 6 by ring] at h
    exact_mod_cast h
  have e0T : (P (n + 6) (n + 5) (n + 6) true : ℚ) = 0 := by
    have h := (Q0 (n + 6) (n + 5) (by omega)).2
    rw [show n + 5 + 1 = n + 6 by ring] at h
    exact_mod_cast h
  obtain ⟨e1F, e1T⟩ := Q1 (n + 6) (n + 5) (by omega) (by omega)
  rw [show n + 5 + 1 - 1 = n + 5 by omega] at e1F e1T
  obtain ⟨e2F, e2T⟩ := Q2 (n + 6) (n + 5) (by omega) (by omega)
  rw [show n + 5 + 1 - 2 = n + 4 by omega] at e2F e2T
  obtain ⟨e3F, e3T⟩ := Q3 (n + 6) (n + 5) (by omega) (by omega)
  rw [show n + 5 + 1 - 3 = n + 3 by omega] at e3F e3T
  obtain ⟨e4F, e4T⟩ := Q4 (n + 6) (n + 5) (by omega) (by omega)
  rw [show n + 5 + 1 - 4 = n + 2 by omega] at e4F e4T
  rw [a_eq]
  push_cast
  rw [e0F, e0T, e1F, e1T, e2F, e2T, e3F, e3T, e4F, e4T]
  push_cast
  ring

/-- Barker's g.f. -/
theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (664 - 3355 * X + 9383 * X ^ 2 - 15720 * X ^ 3 + 16980 * X ^ 4 - 11983 * X ^ 5 + 5367 * X ^ 6 - 1390 * X ^ 7 + 159 * X ^ 8) := by
  have v1 : (a 1 : ℚ) = 664 := by rw [a_poly]; norm_num
  have v2 : (a 2 : ℚ) = 2621 := by rw [a_poly]; norm_num
  have v3 : (a 3 : ℚ) = 9068 := by rw [a_poly]; norm_num
  have v4 : (a 4 : ℚ) = 27312 := by rw [a_poly]; norm_num
  have v5 : (a 5 : ℚ) = 72840 := by rw [a_poly]; norm_num
  have v6 : (a 6 : ℚ) = 175475 := by rw [a_poly]; norm_num
  have v7 : (a 7 : ℚ) = 388512 := by rw [a_poly]; norm_num
  have v8 : (a 8 : ℚ) = 801674 := by rw [a_poly]; norm_num
  have v9 : (a 9 : ℚ) = 1558833 := by rw [a_poly]; norm_num
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 9 = A - C (9 : ℚ) * (A * X ^ 1) + C (36 : ℚ) * (A * X ^ 2) - C (84 : ℚ) * (A * X ^ 3) + C (126 : ℚ) * (A * X ^ 4) - C (126 : ℚ) * (A * X ^ 5) + C (84 : ℚ) * (A * X ^ 6) - C (36 : ℚ) * (A * X ^ 7) + C (9 : ℚ) * (A * X ^ 8) - A * X ^ 9 := by
    simp only [map_ofNat]
    ring
  have e2 : (X * (664 - 3355 * X + 9383 * X ^ 2 - 15720 * X ^ 3 + 16980 * X ^ 4 - 11983 * X ^ 5 + 5367 * X ^ 6 - 1390 * X ^ 7 + 159 * X ^ 8) : ℚ⟦X⟧) = X ^ 1 * C (664 : ℚ) - X ^ 2 * C (3355 : ℚ) + X ^ 3 * C (9383 : ℚ) - X ^ 4 * C (15720 : ℚ) + X ^ 5 * C (16980 : ℚ) - X ^ 6 * C (11983 : ℚ) + X ^ 7 * C (5367 : ℚ) - X ^ 8 * C (1390 : ℚ) + X ^ 9 * C (159 : ℚ) := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk,
    coeff_C_mul]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
  · simp
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v1]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v1, v2]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v1, v2, v3]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v1, v2, v3, v4]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v1, v2, v3, v4, v5]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v1, v2, v3, v4, v5, v6]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v1, v2, v3, v4, v5, v6, v7]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v1, v2, v3, v4, v5, v6, v7, v8]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v1, v2, v3, v4, v5, v6, v7, v8, v9]
    all_goals norm_num
  · simp only [show ¬ (m + 10 = 0) by omega,
      show 1 ≤ m + 10 by omega,
      show m + 10 - 1 = m + 9 by omega,
      show ¬ (m + 9 = 0) by omega,
      show 2 ≤ m + 10 by omega,
      show m + 10 - 2 = m + 8 by omega,
      show ¬ (m + 8 = 0) by omega,
      show 3 ≤ m + 10 by omega,
      show m + 10 - 3 = m + 7 by omega,
      show ¬ (m + 7 = 0) by omega,
      show 4 ≤ m + 10 by omega,
      show m + 10 - 4 = m + 6 by omega,
      show ¬ (m + 6 = 0) by omega,
      show 5 ≤ m + 10 by omega,
      show m + 10 - 5 = m + 5 by omega,
      show ¬ (m + 5 = 0) by omega,
      show 6 ≤ m + 10 by omega,
      show m + 10 - 6 = m + 4 by omega,
      show ¬ (m + 4 = 0) by omega,
      show 7 ≤ m + 10 by omega,
      show m + 10 - 7 = m + 3 by omega,
      show ¬ (m + 3 = 0) by omega,
      show 8 ≤ m + 10 by omega,
      show m + 10 - 8 = m + 2 by omega,
      show ¬ (m + 2 = 0) by omega,
      show 9 ≤ m + 10 by omega,
      show m + 10 - 9 = m + 1 by omega,
      show ¬ (m + 1 = 0) by omega,
      show ¬ (m + 10 = 1) by omega,
      show ¬ (m + 10 = 2) by omega,
      show ¬ (m + 10 = 3) by omega,
      show ¬ (m + 10 = 4) by omega,
      show ¬ (m + 10 = 5) by omega,
      show ¬ (m + 10 = 6) by omega,
      show ¬ (m + 10 = 7) by omega,
      show ¬ (m + 10 = 8) by omega,
      show ¬ (m + 10 = 9) by omega, if_true, if_false]
    rw [a_poly (m + 10), a_poly (m + 9), a_poly (m + 8), a_poly (m + 7), a_poly (m + 6), a_poly (m + 5), a_poly (m + 4), a_poly (m + 3), a_poly (m + 2), a_poly (m + 1)]
    push_cast
    ring

/-- Barker's recurrence. -/
theorem recur : ∀ n : ℕ, 9 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  rw [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega, show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega, show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega, show m + 10 - 7 = m + 3 by omega, show m + 10 - 8 = m + 2 by omega, show m + 10 - 9 = m + 1 by omega]
  have h : (a (m + 10) : ℚ) = 9 * a (m + 9) - 36 * a (m + 8) + 84 * a (m + 7) - 126 * a (m + 6) + 126 * a (m + 5) - 84 * a (m + 4) + 36 * a (m + 3) - 9 * a (m + 2) + a (m + 1) := by
    rw [a_poly (m + 10), a_poly (m + 9), a_poly (m + 8), a_poly (m + 7), a_poly (m + 6), a_poly (m + 5), a_poly (m + 4), a_poly (m + 3), a_poly (m + 2), a_poly (m + 1)]
    push_cast
    ring
  exact_mod_cast h

/-- Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (664 - 3355 * X + 9383 * X ^ 2 - 15720 * X ^ 3 + 16980 * X ^ 4 - 11983 * X ^ 5 + 5367 * X ^ 6 - 1390 * X ^ 7 + 159 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a211839

theorem OMA.solution : type_of% @OMA.S_oeis_a211839.main :=
  OMA.S_oeis_a211839.conjecture
