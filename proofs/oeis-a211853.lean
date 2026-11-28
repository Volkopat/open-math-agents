import OMAStatements.S_oeis_a211853

/-!
OEIS A211853 (R. H. Hardin, Apr 22 2012): Number of nonnegative integer arrays of length 2n+8 with new values 0 upwards introduced in order, no three adjacent elements all unequal, and containing the value n+1.
Conjectures from Colin Barker, Jul 20 2018: G.f.: x*(1731 - 5181*x + 9696*x^2 - 10295*x^3 + 6435*x^4 - 2210*x^5 + 323*x^6) / (1 - x)^7. a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.

Proof. Prefixes of length m + 1 are counted by their number b of values and whether their last two
entries differ (`P`); appending an entry with Fin.snoc (`rgs_snoc`, `nad_snoc`, `nb_snoc`,
`dl_snoc`) gives P(m + 1, b, false) = P(m, b, false) + P(m, b, true) and
P(m + 1, b, true) = (b - 1) P(m, b, false) + P(m, b - 1, false) + P(m, b, true) (`P_succ_false`,
`P_succ_true`): after two different entries only the last two values may follow. The excess
(m + 1) - 2b + 2 is never negative (`P_big2`), and for each excess e the counts
E_e(j) = P(2j + e - 1, j + 1, .) are polynomials in j (`E0`, `E1`, ...). An array that introduces
its values in order contains n + 1 exactly when it has at least n + 2 values (`contains_iff`), so
a(n) is a sum of these polynomials (`a_eq`, `a_poly`); the g.f. and the recurrence follow by
comparing coefficients.
-/

namespace OMA.S_oeis_a211853

open PowerSeries Finset


instance {L N : ℕ} : DecidablePred (@newInOrder L N) := fun x => by unfold newInOrder; infer_instance

instance {L N : ℕ} : DecidablePred (@noAllDiff L N) := fun x => by unfold noAllDiff; infer_instance

/-- One more than the largest entry (0 for the empty array): the number of values of an array
that introduces them in order. -/
def nb {L N : ℕ} (y : Fin L → Fin N) : ℕ := univ.sup (fun i => (y i : ℕ) + 1)

lemma le_nb {L N : ℕ} (y : Fin L → Fin N) (i : Fin L) : (y i : ℕ) + 1 ≤ nb y :=
  Finset.le_sup (f := fun i => (y i : ℕ) + 1) (mem_univ i)

lemma lt_nb {L N : ℕ} (y : Fin L → Fin N) (c : ℕ) (h : c < nb y) : ∃ i, c < (y i : ℕ) + 1 := by
  obtain ⟨i, -, hi⟩ := Finset.lt_sup_iff.mp h
  exact ⟨i, hi⟩

/-- The last two entries are different. -/
def dl {L N : ℕ} (x : Fin L → Fin N) : Prop :=
  ∃ i : Fin L, ∃ j : Fin L, (i : ℕ) + 1 = j ∧ (j : ℕ) + 1 = L ∧ x i ≠ x j

instance {L N : ℕ} : DecidablePred (@dl L N) := fun x => by unfold dl; infer_instance

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

lemma dl_snoc {m N : ℕ} (y : Fin (m + 1) → Fin N) (w : Fin N) :
    dl (Fin.snoc y w : Fin (m + 2) → Fin N) ↔ y (Fin.last m) ≠ w := by
  unfold dl
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

lemma dl_iff {m N : ℕ} (y : Fin (m + 1) → Fin N) :
    dl y ↔ 1 ≤ m ∧ y ⟨m - 1, by omega⟩ ≠ y (Fin.last m) := by
  unfold dl
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩, hij, hjL, hv⟩
    simp only at hij hjL
    have e1 : (⟨j, hj⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp; omega)
    have e2 : (⟨i, hi⟩ : Fin (m + 1)) = ⟨m - 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e1, e2] at hv
    exact ⟨by omega, hv⟩
  · rintro ⟨hm, hv⟩
    exact ⟨⟨m - 1, by omega⟩, Fin.last m, by simp; omega, by simp, hv⟩

lemma nad_snoc {m N : ℕ} (y : Fin (m + 1) → Fin N) (w : Fin N) :
    noAllDiff (Fin.snoc y w : Fin (m + 2) → Fin N) ↔
      noAllDiff y ∧ ¬ (dl y ∧ y (Fin.last m) ≠ w ∧ y ⟨m - 1, by omega⟩ ≠ w) := by
  rw [dl_iff]
  unfold noAllDiff
  constructor
  · intro h
    refine ⟨fun ⟨i, hi⟩ h2 => ?_, ?_⟩
    · simp only at h2 ⊢
      have := h ⟨i, by omega⟩ (by simp only; omega)
      simp only at this
      rw [snoc_lt y w i (by omega) (by omega), snoc_lt y w (i + 1) (by omega) (by omega),
        snoc_lt y w (i + 2) (by omega) (by omega)] at this
      exact this
    · rintro ⟨⟨hm, h1⟩, h2, h3⟩
      apply h ⟨m - 1, by omega⟩ (by simp only; omega)
      simp only
      have e3 : (⟨m - 1 + 2, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) := Fin.ext (by simp; omega)
      have e1 : (⟨m - 1 + 1, by omega⟩ : Fin (m + 2)) = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
      rw [snoc_lt y w (m - 1) (by omega) (by omega), e1, snoc_lt y w m (by omega) (by omega), e3,
        Fin.snoc_last]
      exact ⟨h1, h2, h3⟩
  · rintro ⟨h, hw⟩ ⟨i, hi⟩ h2
    simp only at h2 ⊢
    rcases Nat.lt_or_ge (i + 2) (m + 1) with hlt | hge
    · rw [snoc_lt y w i (by omega) (by omega), snoc_lt y w (i + 1) (by omega) (by omega),
        snoc_lt y w (i + 2) (by omega) (by omega)]
      exact h ⟨i, by omega⟩ (by simp only; omega)
    · have e3 : (⟨i + 2, h2⟩ : Fin (m + 2)) = Fin.last (m + 1) := Fin.ext (by simp; omega)
      have e0 : (⟨i, by omega⟩ : Fin (m + 1)) = ⟨m - 1, by omega⟩ := Fin.ext (by simp; omega)
      have e1 : (⟨i + 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp; omega)
      rw [snoc_lt y w i (by omega) (by omega), snoc_lt y w (i + 1) (by omega) (by omega), e3,
        Fin.snoc_last, e0, e1]
      rintro ⟨h1, h3, h4⟩
      exact hw ⟨⟨by omega, h1⟩, h3, h4⟩

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
no three adjacent different entries, with b values, and with different (f = true) or equal last
two entries (a single entry counts as equal). -/
def P (N m b : ℕ) (f : Bool) : ℕ :=
  ((univ : Finset (Fin (m + 1) → Fin N)).filter (fun y => newInOrder y ∧ noAllDiff y ∧ nb y = b ∧
    decide (dl y) = f)).card

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

lemma split_dl (N m b : ℕ) :
    ((univ : Finset (Fin (m + 1) → Fin N)).filter (fun y => newInOrder y ∧ noAllDiff y ∧ nb y = b)).card =
      P N m b false + P N m b true := by
  unfold P
  rw [card_eq_sum_card_fiberwise (f := fun y => decide (dl y)) (t := univ)
      (fun _ _ => Finset.mem_coe.mpr (mem_univ _)), Fintype.sum_bool,
    add_comm, filter_filter, filter_filter]
  congr 1 <;> (congr 1; ext y; simp only [mem_filter, mem_univ, true_and]; tauto)

lemma P_succ_false (N m b : ℕ) : P N (m + 1) b false = P N m b false + P N m b true := by
  rw [← split_dl]
  unfold P
  refine card_bij' (fun x _ => Fin.init x) (fun y _ => Fin.snoc y (y (Fin.last m))) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and, decide_eq_false_iff_not] at hx ⊢
    obtain ⟨hr, hn, hb, hf⟩ := hx
    have e : x = Fin.snoc (Fin.init x) (x (Fin.last _)) := (Fin.snoc_init_self x).symm
    rw [e, dl_snoc, not_not] at hf
    rw [e, rgs_snoc] at hr
    rw [e, nad_snoc] at hn
    rw [e, nb_snoc, ← hf, max_eq_left (le_nb _ _)] at hb
    exact ⟨hr.1, hn.1, hb⟩
  · intro y hy
    simp only [mem_filter, mem_univ, true_and, decide_eq_false_iff_not] at hy ⊢
    obtain ⟨hr, hn, hb⟩ := hy
    refine ⟨(rgs_snoc y _).mpr ⟨hr, by have := le_nb y (Fin.last m); omega⟩,
      (nad_snoc y _).mpr ⟨hn, fun h => h.2.1 rfl⟩, ?_, fun h => (dl_snoc y _).mp h rfl⟩
    rw [nb_snoc, max_eq_left (le_nb y _), hb]
  · intro x hx
    simp only [mem_filter, mem_univ, true_and, decide_eq_false_iff_not] at hx
    have hf := hx.2.2.2
    have e : x = Fin.snoc (Fin.init x) (x (Fin.last _)) := (Fin.snoc_init_self x).symm
    rw [e, dl_snoc, not_not] at hf
    rw [hf]
    exact Fin.snoc_init_self x
  · intro y _
    simp

lemma P_succ_true (N m b : ℕ) (hb : 1 ≤ b) (hN : m + 2 ≤ N) :
    P N (m + 1) b true = (b - 1) * P N m b false + P N m (b - 1) false + P N m b true := by
  have step1 : P N (m + 1) b true = ∑ y : Fin (m + 1) → Fin N,
      if newInOrder y ∧ noAllDiff y then
        ((univ : Finset (Fin N)).filter (fun w : Fin N => (w : ℕ) ≤ nb y ∧
          max (nb y) ((w : ℕ) + 1) = b ∧ (y (Fin.last m) : ℕ) ≠ (w : ℕ) ∧
            ¬ (dl y ∧ (y ⟨m - 1, by omega⟩ : ℕ) ≠ (w : ℕ)))).card else 0 := by
    unfold P
    rw [card_eq_sum_card_fiberwise (f := Fin.init) (t := univ) (by simp)]
    refine sum_congr rfl (fun y _ => ?_)
    split_ifs with hy
    · refine card_bij' (fun x _ => x (Fin.last _)) (fun w _ => Fin.snoc y w) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq] at hx ⊢
        obtain ⟨⟨hr, hn, hb', hf⟩, hinit⟩ := hx
        have e : x = Fin.snoc y (x (Fin.last _)) := by
          rw [← hinit]
          exact (Fin.snoc_init_self x).symm
        rw [e, rgs_snoc] at hr
        rw [e, nb_snoc] at hb'
        rw [e, dl_snoc] at hf
        rw [e, nad_snoc] at hn
        refine ⟨hr.2, hb', fun h => hf (Fin.ext h), fun ⟨h1, h2⟩ => hn.2 ⟨h1, hf, fun h => h2 ?_⟩⟩
        rw [h]
      · intro w hw
        simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq] at hw ⊢
        obtain ⟨hle, hmax, hne, hd⟩ := hw
        refine ⟨⟨(rgs_snoc y w).mpr ⟨hy.1, hle⟩,
          (nad_snoc y w).mpr ⟨hy.2, fun ⟨h1, _, h3⟩ => hd ⟨h1, fun h => h3 (Fin.ext h)⟩⟩,
          by rw [nb_snoc]; exact hmax, (dl_snoc y w).mpr (fun h => hne (congrArg Fin.val h))⟩, by simp⟩
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
      rw [e, nad_snoc] at hn
      exact ⟨hr.1, hn.1⟩
  have step2 : ∀ y : Fin (m + 1) → Fin N, (if newInOrder y ∧ noAllDiff y then
        ((univ : Finset (Fin N)).filter (fun w : Fin N => (w : ℕ) ≤ nb y ∧
          max (nb y) ((w : ℕ) + 1) = b ∧ (y (Fin.last m) : ℕ) ≠ (w : ℕ) ∧
            ¬ (dl y ∧ (y ⟨m - 1, by omega⟩ : ℕ) ≠ (w : ℕ)))).card else 0) =
      (if newInOrder y ∧ noAllDiff y ∧ nb y = b ∧ decide (dl y) = false then b - 1 else 0) +
        (if newInOrder y ∧ noAllDiff y ∧ nb y = b - 1 ∧ decide (dl y) = false then 1 else 0) +
        (if newInOrder y ∧ noAllDiff y ∧ nb y = b ∧ decide (dl y) = true then 1 else 0) := by
    intro y
    by_cases hy : newInOrder y ∧ noAllDiff y
    · rw [if_pos hy]
      have hc : nb y < N := by have := nb_le_len y hy.1; omega
      by_cases hd : dl y
      · have hd' := (dl_iff y).mp hd
        have e : (univ : Finset (Fin N)).filter (fun w : Fin N => (w : ℕ) ≤ nb y ∧
            max (nb y) ((w : ℕ) + 1) = b ∧ (y (Fin.last m) : ℕ) ≠ (w : ℕ) ∧
              ¬ (dl y ∧ (y ⟨m - 1, by omega⟩ : ℕ) ≠ (w : ℕ))) =
            if nb y = b then {y ⟨m - 1, by omega⟩} else ∅ := by
          have h1 := le_nb y ⟨m - 1, by omega⟩
          have h2 : (y ⟨m - 1, by omega⟩ : ℕ) ≠ (y (Fin.last m) : ℕ) := fun h => hd'.2 (Fin.ext h)
          split_ifs with hb'
          · ext w
            simp only [mem_filter, mem_univ, true_and, mem_singleton, hd, true_and, not_not, Fin.ext_iff]
            omega
          · ext w
            simp only [mem_filter, mem_univ, true_and, hd, true_and, not_not, Finset.notMem_empty,
              iff_false]
            omega
        rw [e]
        simp only [hy.1, hy.2, hd, decide_true, true_and, Bool.true_eq_false, and_false, if_false,
          and_true, zero_add]
        split_ifs <;> simp
      · have e : (univ : Finset (Fin N)).filter (fun w : Fin N => (w : ℕ) ≤ nb y ∧
            max (nb y) ((w : ℕ) + 1) = b ∧ (y (Fin.last m) : ℕ) ≠ (w : ℕ) ∧
              ¬ (dl y ∧ (y ⟨m - 1, by omega⟩ : ℕ) ≠ (w : ℕ))) =
            (univ : Finset (Fin N)).filter (fun w : Fin N => (w : ℕ) ≤ nb y ∧
              max (nb y) ((w : ℕ) + 1) = b ∧ (y (Fin.last m) : ℕ) ≠ (w : ℕ)) := by
          ext w
          simp only [mem_filter, mem_univ, true_and, hd, false_and, not_false_eq_true, and_true]
        rw [e, card_w N b (nb y) (y (Fin.last m)) (le_nb y _) hc]
        simp only [hy.1, hy.2, hd, decide_false, true_and, Bool.false_eq_true, and_false, if_false,
          and_true, add_zero]
        split_ifs <;> omega
    · rw [if_neg hy, if_neg (fun h => hy ⟨h.1, h.2.1⟩), if_neg (fun h => hy ⟨h.1, h.2.1⟩),
        if_neg (fun h => hy ⟨h.1, h.2.1⟩)]
  rw [step1, sum_congr rfl (fun y _ => step2 y), sum_add_distrib, sum_add_distrib]
  unfold P
  simp only [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul]
  ring

lemma P_succ_true_q (N m b : ℕ) (hb : 1 ≤ b) (hN : m + 2 ≤ N) :
    (P N (m + 1) b true : ℚ) = ((b : ℚ) - 1) * (P N m b false : ℚ) + (P N m (b - 1) false : ℚ) +
      (P N m b true : ℚ) := by
  rw [P_succ_true N m b hb hN]
  push_cast [Nat.cast_sub hb]
  ring

lemma P_one_true (N m : ℕ) : P N m 1 true = 0 := by
  unfold P
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro y - ⟨-, -, hb, hd⟩
  simp only [decide_eq_true_eq] at hd
  obtain ⟨i, j, -, -, hij⟩ := hd
  apply hij
  have hi := le_nb y i
  have hj := le_nb y j
  ext
  omega

lemma P_one_false (N : ℕ) (hN : 1 ≤ N) : P N 0 1 false = 1 := by
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
    · unfold dl
      rintro ⟨i, j, hij, hj, -⟩
      have := i.isLt
      omega

lemma P_big2 (N m b : ℕ) (hN : m + 1 ≤ N) :
    (m + 2 < 2 * b → P N m b false = 0) ∧ (m + 3 < 2 * b → P N m b true = 0) := by
  induction m generalizing b with
  | zero =>
    have h0 : ∀ f, 1 < b → P N 0 b f = 0 := by
      intro f hb
      unfold P
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro y - ⟨hr, -, hnb, -⟩
      have := nb_le_len y hr
      omega
    exact ⟨fun h => h0 false (by omega), fun h => h0 true (by omega)⟩
  | succ m ih =>
    constructor
    · intro h
      rw [P_succ_false, (ih b (by omega)).1 (by omega), (ih b (by omega)).2 (by omega)]
    · intro h
      rw [P_succ_true N m b (by omega) (by omega), (ih b (by omega)).1 (by omega),
        (ih (b - 1) (by omega)).1 (by omega), (ih b (by omega)).2 (by omega)]
      simp

lemma E0 (N j : ℕ) (hN : 2 * j + 2 ≤ N) :
    P N (2 * j + 1) (j + 2) false = 0 ∧ P N (2 * j + 1) (j + 2) true = 1 := by
  induction j with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [show 2 * 0 + 1 = 0 + 1 from rfl, P_succ_false, (P_big2 N 0 (0 + 2) (by omega)).1 (by omega),
        (P_big2 N 0 (0 + 2) (by omega)).2 (by omega)]
      all_goals norm_num
    · rw [show 2 * 0 + 1 = 0 + 1 from rfl, P_succ_true N 0 (0 + 2) (by omega) (by omega),
        (P_big2 N 0 (0 + 2) (by omega)).1 (by omega), (P_big2 N 0 (0 + 2) (by omega)).2 (by omega),
        show 0 + 2 - 1 = 1 from rfl, P_one_false N (by omega)]
      all_goals norm_num
  | succ j ih =>
    obtain ⟨ihF, ihT⟩ := ih (by omega)
    have z1 := (P_big2 N (2 * j + 2) (j + 1 + 2) (by omega)).1 (by omega)
    have z2 := (P_big2 N (2 * j + 2) (j + 1 + 2) (by omega)).2 (by omega)
    have s1 : P N (2 * j + 2) (j + 2) false = 1 := by
      rw [show 2 * j + 2 = 2 * j + 1 + 1 by ring, P_succ_false, ihF, ihT]
    rw [show 2 * (j + 1) + 1 = 2 * j + 2 + 1 by ring]
    refine ⟨?_, ?_⟩
    · rw [P_succ_false, z1, z2]
      all_goals norm_num
    · rw [P_succ_true N (2 * j + 2) (j + 1 + 2) (by omega) (by omega), z1, z2,
        show j + 1 + 2 - 1 = j + 2 by omega, s1]
      all_goals norm_num

/-- The arrays of length 2j + 1 with j + 1 values (excess 1). -/
lemma E1 (N j : ℕ) (hN : 2 * j + 1 ≤ N) :
    (P N (2 * j) (j + 1) false : ℚ) = 1 ∧
      (P N (2 * j) (j + 1) true : ℚ) = 2 * (j : ℚ) := by
  have hF : ∀ j, 2 * j + 1 ≤ N → (P N (2 * j) (j + 1) false : ℚ) = 1 := by
    intro j hN
    cases j with
    | zero =>
      rw [show 2 * 0 = 0 from rfl, show 0 + 1 = 1 from rfl, P_one_false N (by omega)]
      all_goals norm_num
    | succ j =>
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, show j + 1 + 1 = j + 2 by ring, P_succ_false,
        (E0 N j (by omega)).1, (E0 N j (by omega)).2]
      all_goals norm_num
  induction j with
  | zero =>
    refine ⟨hF 0 hN, ?_⟩
    rw [show (0 : ℕ) + 1 = 1 from rfl, P_one_true]
    norm_num
  | succ j ih =>
    obtain ⟨ihF, ihT⟩ := ih (by omega)
    refine ⟨hF (j + 1) hN, ?_⟩
    have hs : P N (2 * j + 1) (j + 1) false =
        P N (2 * j) (j + 1) false + P N (2 * j) (j + 1) true := P_succ_false N (2 * j) (j + 1)
    have hq := P_succ_true_q N (2 * j + 1) (j + 2) (by omega) (by omega)
    rw [show j + 2 - 1 = j + 1 by omega, hs] at hq
    have p1 := (E0 N j (by omega)).1
    have p2 := (E0 N j (by omega)).2
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, show j + 1 + 1 = j + 2 by ring, hq]
    push_cast
    rw [ihF, ihT, p1, p2]
    push_cast
    ring

/-- The arrays of length 2j + 2 with j + 1 values (excess 2). -/
lemma E2 (N j : ℕ) (hN : 2 * j + 2 ≤ N) :
    (P N (2 * j + 1) (j + 1) false : ℚ) = 1 + 2 * (j : ℚ) ∧
      (P N (2 * j + 1) (j + 1) true : ℚ) = (3 / 2) * (j : ℚ) + (5 / 2) * (j : ℚ) ^ 2 := by
  have hF : ∀ j, 2 * j + 2 ≤ N → (P N (2 * j + 1) (j + 1) false : ℚ) = 1 + 2 * (j : ℚ) := by
    intro j hN
    rw [P_succ_false]
    obtain ⟨q1, q2⟩ := E1 N j (by omega)
    push_cast
    linear_combination q1 + q2
  induction j with
  | zero =>
    refine ⟨hF 0 hN, ?_⟩
    rw [show (0 : ℕ) + 1 = 1 from rfl, P_one_true]
    norm_num
  | succ j ih =>
    obtain ⟨ihF, ihT⟩ := ih (by omega)
    refine ⟨hF (j + 1) hN, ?_⟩
    have hs : P N (2 * j + 2) (j + 1) false =
        P N (2 * j + 1) (j + 1) false + P N (2 * j + 1) (j + 1) true := by rw [show 2 * j + 2 = 2 * j + 1 + 1 by ring, P_succ_false]
    have hq := P_succ_true_q N (2 * j + 2) (j + 2) (by omega) (by omega)
    rw [show j + 2 - 1 = j + 1 by omega, hs] at hq
    obtain ⟨p1, p2⟩ := E1 N (j + 1) (by omega)
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, show j + 1 + 1 = j + 2 by ring] at p1 p2
    rw [show 2 * (j + 1) + 1 = 2 * j + 2 + 1 by ring, show j + 1 + 1 = j + 2 by ring, hq]
    push_cast
    rw [ihF, ihT, p1, p2]
    push_cast
    ring

/-- The arrays of length 2j + 3 with j + 1 values (excess 3). -/
lemma E3 (N j : ℕ) (hN : 2 * j + 3 ≤ N) :
    (P N (2 * j + 2) (j + 1) false : ℚ) = 1 + (7 / 2) * (j : ℚ) + (5 / 2) * (j : ℚ) ^ 2 ∧
      (P N (2 * j + 2) (j + 1) true : ℚ) = (5 / 3) * (j : ℚ) + 4 * (j : ℚ) ^ 2 + (7 / 3) * (j : ℚ) ^ 3 := by
  have hF : ∀ j, 2 * j + 3 ≤ N → (P N (2 * j + 2) (j + 1) false : ℚ) = 1 + (7 / 2) * (j : ℚ) + (5 / 2) * (j : ℚ) ^ 2 := by
    intro j hN
    rw [show 2 * j + 2 = 2 * j + 1 + 1 by ring, P_succ_false]
    obtain ⟨q1, q2⟩ := E2 N j (by omega)
    push_cast
    linear_combination q1 + q2
  induction j with
  | zero =>
    refine ⟨hF 0 hN, ?_⟩
    rw [show (0 : ℕ) + 1 = 1 from rfl, P_one_true]
    norm_num
  | succ j ih =>
    obtain ⟨ihF, ihT⟩ := ih (by omega)
    refine ⟨hF (j + 1) hN, ?_⟩
    have hs : P N (2 * j + 3) (j + 1) false =
        P N (2 * j + 2) (j + 1) false + P N (2 * j + 2) (j + 1) true := by rw [show 2 * j + 3 = 2 * j + 2 + 1 by ring, P_succ_false]
    have hq := P_succ_true_q N (2 * j + 3) (j + 2) (by omega) (by omega)
    rw [show j + 2 - 1 = j + 1 by omega, hs] at hq
    obtain ⟨p1, p2⟩ := E2 N (j + 1) (by omega)
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring, show j + 1 + 1 = j + 2 by ring] at p1 p2
    rw [show 2 * (j + 1) + 2 = 2 * j + 3 + 1 by ring, show j + 1 + 1 = j + 2 by ring, hq]
    push_cast
    rw [ihF, ihT, p1, p2]
    push_cast
    ring

/-- The arrays of length 2j + 4 with j + 1 values (excess 4). -/
lemma E4 (N j : ℕ) (hN : 2 * j + 4 ≤ N) :
    (P N (2 * j + 3) (j + 1) false : ℚ) = 1 + (31 / 6) * (j : ℚ) + (13 / 2) * (j : ℚ) ^ 2 + (7 / 3) * (j : ℚ) ^ 3 ∧
      (P N (2 * j + 3) (j + 1) true : ℚ) = (25 / 12) * (j : ℚ) + (149 / 24) * (j : ℚ) ^ 2 + (71 / 12) * (j : ℚ) ^ 3 + (43 / 24) * (j : ℚ) ^ 4 := by
  have hF : ∀ j, 2 * j + 4 ≤ N → (P N (2 * j + 3) (j + 1) false : ℚ) = 1 + (31 / 6) * (j : ℚ) + (13 / 2) * (j : ℚ) ^ 2 + (7 / 3) * (j : ℚ) ^ 3 := by
    intro j hN
    rw [show 2 * j + 3 = 2 * j + 2 + 1 by ring, P_succ_false]
    obtain ⟨q1, q2⟩ := E3 N j (by omega)
    push_cast
    linear_combination q1 + q2
  induction j with
  | zero =>
    refine ⟨hF 0 hN, ?_⟩
    rw [show (0 : ℕ) + 1 = 1 from rfl, P_one_true]
    norm_num
  | succ j ih =>
    obtain ⟨ihF, ihT⟩ := ih (by omega)
    refine ⟨hF (j + 1) hN, ?_⟩
    have hs : P N (2 * j + 4) (j + 1) false =
        P N (2 * j + 3) (j + 1) false + P N (2 * j + 3) (j + 1) true := by rw [show 2 * j + 4 = 2 * j + 3 + 1 by ring, P_succ_false]
    have hq := P_succ_true_q N (2 * j + 4) (j + 2) (by omega) (by omega)
    rw [show j + 2 - 1 = j + 1 by omega, hs] at hq
    obtain ⟨p1, p2⟩ := E3 N (j + 1) (by omega)
    rw [show 2 * (j + 1) + 2 = 2 * j + 4 by ring, show j + 1 + 1 = j + 2 by ring] at p1 p2
    rw [show 2 * (j + 1) + 3 = 2 * j + 4 + 1 by ring, show j + 1 + 1 = j + 2 by ring, hq]
    push_cast
    rw [ihF, ihT, p1, p2]
    push_cast
    ring

/-- The arrays of length 2j + 5 with j + 1 values (excess 5). -/
lemma E5 (N j : ℕ) (hN : 2 * j + 5 ≤ N) :
    (P N (2 * j + 4) (j + 1) false : ℚ) = 1 + (29 / 4) * (j : ℚ) + (305 / 24) * (j : ℚ) ^ 2 + (33 / 4) * (j : ℚ) ^ 3 + (43 / 24) * (j : ℚ) ^ 4 ∧
      (P N (2 * j + 4) (j + 1) true : ℚ) = (41 / 15) * (j : ℚ) + (29 / 3) * (j : ℚ) ^ 2 + (145 / 12) * (j : ℚ) ^ 3 + (19 / 3) * (j : ℚ) ^ 4 + (71 / 60) * (j : ℚ) ^ 5 := by
  have hF : ∀ j, 2 * j + 5 ≤ N → (P N (2 * j + 4) (j + 1) false : ℚ) = 1 + (29 / 4) * (j : ℚ) + (305 / 24) * (j : ℚ) ^ 2 + (33 / 4) * (j : ℚ) ^ 3 + (43 / 24) * (j : ℚ) ^ 4 := by
    intro j hN
    rw [show 2 * j + 4 = 2 * j + 3 + 1 by ring, P_succ_false]
    obtain ⟨q1, q2⟩ := E4 N j (by omega)
    push_cast
    linear_combination q1 + q2
  induction j with
  | zero =>
    refine ⟨hF 0 hN, ?_⟩
    rw [show (0 : ℕ) + 1 = 1 from rfl, P_one_true]
    norm_num
  | succ j ih =>
    obtain ⟨ihF, ihT⟩ := ih (by omega)
    refine ⟨hF (j + 1) hN, ?_⟩
    have hs : P N (2 * j + 5) (j + 1) false =
        P N (2 * j + 4) (j + 1) false + P N (2 * j + 4) (j + 1) true := by rw [show 2 * j + 5 = 2 * j + 4 + 1 by ring, P_succ_false]
    have hq := P_succ_true_q N (2 * j + 5) (j + 2) (by omega) (by omega)
    rw [show j + 2 - 1 = j + 1 by omega, hs] at hq
    obtain ⟨p1, p2⟩ := E4 N (j + 1) (by omega)
    rw [show 2 * (j + 1) + 3 = 2 * j + 5 by ring, show j + 1 + 1 = j + 2 by ring] at p1 p2
    rw [show 2 * (j + 1) + 4 = 2 * j + 5 + 1 by ring, show j + 1 + 1 = j + 2 by ring, hq]
    push_cast
    rw [ihF, ihT, p1, p2]
    push_cast
    ring

/-- The arrays of length 2j + 6 with j + 1 values (excess 6). -/
lemma E6 (N j : ℕ) (hN : 2 * j + 6 ≤ N) :
    (P N (2 * j + 5) (j + 1) false : ℚ) = 1 + (599 / 60) * (j : ℚ) + (179 / 8) * (j : ℚ) ^ 2 + (61 / 3) * (j : ℚ) ^ 3 + (65 / 8) * (j : ℚ) ^ 4 + (71 / 60) * (j : ℚ) ^ 5 ∧
      (P N (2 * j + 5) (j + 1) true : ℚ) = (11 / 3) * (j : ℚ) + (5423 / 360) * (j : ℚ) ^ 2 + (1099 / 48) * (j : ℚ) ^ 3 + (2339 / 144) * (j : ℚ) ^ 4 + (87 / 16) * (j : ℚ) ^ 5 + (499 / 720) * (j : ℚ) ^ 6 := by
  have hF : ∀ j, 2 * j + 6 ≤ N → (P N (2 * j + 5) (j + 1) false : ℚ) = 1 + (599 / 60) * (j : ℚ) + (179 / 8) * (j : ℚ) ^ 2 + (61 / 3) * (j : ℚ) ^ 3 + (65 / 8) * (j : ℚ) ^ 4 + (71 / 60) * (j : ℚ) ^ 5 := by
    intro j hN
    rw [show 2 * j + 5 = 2 * j + 4 + 1 by ring, P_succ_false]
    obtain ⟨q1, q2⟩ := E5 N j (by omega)
    push_cast
    linear_combination q1 + q2
  induction j with
  | zero =>
    refine ⟨hF 0 hN, ?_⟩
    rw [show (0 : ℕ) + 1 = 1 from rfl, P_one_true]
    norm_num
  | succ j ih =>
    obtain ⟨ihF, ihT⟩ := ih (by omega)
    refine ⟨hF (j + 1) hN, ?_⟩
    have hs : P N (2 * j + 6) (j + 1) false =
        P N (2 * j + 5) (j + 1) false + P N (2 * j + 5) (j + 1) true := by rw [show 2 * j + 6 = 2 * j + 5 + 1 by ring, P_succ_false]
    have hq := P_succ_true_q N (2 * j + 6) (j + 2) (by omega) (by omega)
    rw [show j + 2 - 1 = j + 1 by omega, hs] at hq
    obtain ⟨p1, p2⟩ := E5 N (j + 1) (by omega)
    rw [show 2 * (j + 1) + 4 = 2 * j + 6 by ring, show j + 1 + 1 = j + 2 by ring] at p1 p2
    rw [show 2 * (j + 1) + 5 = 2 * j + 6 + 1 by ring, show j + 1 + 1 = j + 2 by ring, hq]
    push_cast
    rw [ihF, ihT, p1, p2]
    push_cast
    ring

lemma a_eq (n : ℕ) : a n =
    (P (2 * n + 8) (2 * n + 7) (n + 5) false + P (2 * n + 8) (2 * n + 7) (n + 5) true) +
    (P (2 * n + 8) (2 * n + 7) (n + 4) false + P (2 * n + 8) (2 * n + 7) (n + 4) true) +
    (P (2 * n + 8) (2 * n + 7) (n + 3) false + P (2 * n + 8) (2 * n + 7) (n + 3) true) +
    (P (2 * n + 8) (2 * n + 7) (n + 2) false + P (2 * n + 8) (2 * n + 7) (n + 2) true) := by
  unfold a
  have hg : ∀ x : Fin (2 * n + 8) → Fin (2 * n + 8), good x ↔ newInOrder x ∧ noAllDiff x ∧ n + 2 ≤ nb x := by
    intro x
    unfold good
    constructor
    · rintro ⟨hr, hn, hc⟩
      exact ⟨hr, hn, by have := (contains_iff x hr (n + 1)).mp hc; omega⟩
    · rintro ⟨hr, hn, hc⟩
      exact ⟨hr, hn, (contains_iff x hr (n + 1)).mpr (by omega)⟩
  rw [filter_congr (fun x _ => hg x)]
  rw [card_eq_sum_card_fiberwise (f := nb) (t := Ico (n + 2) (2 * n + 8 + 1)) (by
    intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    simp only [coe_Ico, Set.mem_Ico]
    exact ⟨hx.2.2, by have := nb_le_len x hx.1; omega⟩)]
  have hs : ∀ b, n + 2 ≤ b →
      (((univ : Finset (Fin (2 * n + 8) → Fin (2 * n + 8))).filter
        (fun x => newInOrder x ∧ noAllDiff x ∧ n + 2 ≤ nb x)).filter (fun x => nb x = b)).card =
        P (2 * n + 8) (2 * n + 7) b false + P (2 * n + 8) (2 * n + 7) b true := by
    intro b hb
    rw [filter_filter, ← split_dl]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨hr, hn, _⟩, hx⟩
      exact ⟨hr, hn, hx⟩
    · rintro ⟨hr, hn, hx⟩
      exact ⟨⟨hr, hn, by omega⟩, hx⟩
  have hz : ∀ b ∈ Ico (n + 6) (2 * n + 8 + 1),
      (((univ : Finset (Fin (2 * n + 8) → Fin (2 * n + 8))).filter
        (fun x => newInOrder x ∧ noAllDiff x ∧ n + 2 ≤ nb x)).filter (fun x => nb x = b)).card = 0 := by
    intro b hb
    rw [mem_Ico] at hb
    rw [hs b (by omega), (P_big2 (2 * n + 8) (2 * n + 7) b (by omega)).1 (by omega),
      (P_big2 (2 * n + 8) (2 * n + 7) b (by omega)).2 (by omega)]
  rw [← sum_Ico_consecutive _ (show n + 2 ≤ n + 6 by omega)
    (show n + 6 ≤ 2 * n + 8 + 1 by omega), sum_eq_zero hz, add_zero]
  rw [sum_Ico_succ_top (show n + 2 ≤ n + 5 by omega), sum_Ico_succ_top (show n + 2 ≤ n + 4 by omega), sum_Ico_succ_top (show n + 2 ≤ n + 3 by omega), sum_Ico_succ_top (show n + 2 ≤ n + 2 by omega), Ico_self, sum_empty, zero_add]
  rw [hs (n + 2) (by omega), hs (n + 3) (by omega), hs (n + 4) (by omega), hs (n + 5) (by omega)]
  ring

/-- a(n) as a polynomial in n. -/
lemma a_poly (n : ℕ) : (a n : ℚ) = 323 + (8788 / 15) * (n : ℚ) + (179153 / 360) * (n : ℚ) ^ 2 + (11681 / 48) * (n : ℚ) ^ 3 + (10031 / 144) * (n : ℚ) ^ 4 + (2587 / 240) * (n : ℚ) ^ 5 + (499 / 720) * (n : ℚ) ^ 6 := by
  obtain ⟨e2F, e2T⟩ := E6 (2 * n + 8) (n + 1) (by omega)
  rw [show 2 * (n + 1) + 5 = 2 * n + 7 by ring, show n + 1 + 1 = n + 2 by ring] at e2F e2T
  obtain ⟨e3F, e3T⟩ := E4 (2 * n + 8) (n + 2) (by omega)
  rw [show 2 * (n + 2) + 3 = 2 * n + 7 by ring, show n + 2 + 1 = n + 3 by ring] at e3F e3T
  obtain ⟨e4F, e4T⟩ := E2 (2 * n + 8) (n + 3) (by omega)
  rw [show 2 * (n + 3) + 1 = 2 * n + 7 by ring, show n + 3 + 1 = n + 4 by ring] at e4F e4T
  have e5 := E0 (2 * n + 8) (n + 3) (by omega)
  rw [show 2 * (n + 3) + 1 = 2 * n + 7 by ring, show n + 3 + 2 = n + 5 by ring] at e5
  have e5F : (P (2 * n + 8) (2 * n + 7) (n + 5) false : ℚ) = 0 := by exact_mod_cast e5.1
  have e5T : (P (2 * n + 8) (2 * n + 7) (n + 5) true : ℚ) = 1 := by exact_mod_cast e5.2
  rw [a_eq]
  push_cast
  rw [e2F, e2T, e3F, e3T, e4F, e4T, e5F, e5T]
  push_cast
  ring

/-- Controls: the entry's listed terms, a(1) to a(25). -/
theorem controls :
    a 1 = 1731 ∧ a 2 = 6936 ∧ a 3 = 21897 ∧ a 4 = 57913 ∧
    a 5 = 134164 ∧ a 6 = 280751 ∧ a 7 = 542235 ∧ a 8 = 981675 ∧
    a 9 = 1685165 ∧ a 10 = 2766870 ∧ a 11 = 4374561 ∧ a 12 = 6695649 ∧
    a 13 = 9963718 ∧ a 14 = 14465557 ∧ a 15 = 20548691 ∧ a 16 = 28629411 ∧
    a 17 = 39201303 ∧ a 18 = 52844276 ∧ a 19 = 70234089 ∧ a 20 = 92152377 ∧
    a 21 = 119497176 ∧ a 22 = 153293947 ∧ a 23 = 194707099 ∧ a 24 = 245052011 ∧
    a 25 = 305807553 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    apply Nat.cast_injective (R := ℚ)
    rw [a_poly]
    norm_num

/-- Barker's g.f. -/
theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (1731 - 5181 * X + 9696 * X ^ 2 - 10295 * X ^ 3 + 6435 * X ^ 4 - 2210 * X ^ 5 + 323 * X ^ 6) := by
  have v1 : (a 1 : ℚ) = 1731 := by rw [a_poly]; norm_num
  have v2 : (a 2 : ℚ) = 6936 := by rw [a_poly]; norm_num
  have v3 : (a 3 : ℚ) = 21897 := by rw [a_poly]; norm_num
  have v4 : (a 4 : ℚ) = 57913 := by rw [a_poly]; norm_num
  have v5 : (a 5 : ℚ) = 134164 := by rw [a_poly]; norm_num
  have v6 : (a 6 : ℚ) = 280751 := by rw [a_poly]; norm_num
  have v7 : (a 7 : ℚ) = 542235 := by rw [a_poly]; norm_num
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 7 = A - C (7 : ℚ) * (A * X ^ 1) + C (21 : ℚ) * (A * X ^ 2) - C (35 : ℚ) * (A * X ^ 3) + C (35 : ℚ) * (A * X ^ 4) - C (21 : ℚ) * (A * X ^ 5) + C (7 : ℚ) * (A * X ^ 6) - A * X ^ 7 := by
    simp only [map_ofNat]
    ring
  have e2 : (X * (1731 - 5181 * X + 9696 * X ^ 2 - 10295 * X ^ 3 + 6435 * X ^ 4 - 2210 * X ^ 5 + 323 * X ^ 6) : ℚ⟦X⟧) = X ^ 1 * C (1731 : ℚ) - X ^ 2 * C (5181 : ℚ) + X ^ 3 * C (9696 : ℚ) - X ^ 4 * C (10295 : ℚ) + X ^ 5 * C (6435 : ℚ) - X ^ 6 * C (2210 : ℚ) + X ^ 7 * C (323 : ℚ) := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk,
    coeff_C_mul]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | m
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
      X * (1731 - 5181 * X + 9696 * X ^ 2 - 10295 * X ^ 3 + 6435 * X ^ 4 - 2210 * X ^ 5 + 323 * X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a211853

theorem OMA.solution : type_of% @OMA.S_oeis_a211853.main :=
  OMA.S_oeis_a211853.conjecture
