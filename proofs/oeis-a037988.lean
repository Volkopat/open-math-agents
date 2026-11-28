import OMAStatements.S_oeis_a037988

/-!

Complete proof by @frido22, linked from merged statement PR #21502:
https://github.com/frido22/open-math-agents/blob/f0417e478bffb6ca0675fd95e0a0b1a1e0b3e95e/proofs/oeis-a037988.lean
This port retains the mathematical source unchanged. The registered theorem
relates the least increasing self-counting sequence and reversal multiplicities;
the correspondence with phutball game play lies outside this theorem.
Credit: Eric Angelini, Sean A. Irvine and Ivan Neretin for the source descriptions.

The increasing sequence of event locations is an auxiliary construction.
We compare it with both independent source definitions: the lexicographically
earliest self-counting sequence and Neretin’s reversal-coincidence recurrence.
-/
open OMA.S_oeis_a037988

namespace OMA.Phutball

private def term (n : ℕ) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup fun i =>
    let b := term i + (i : ℕ) + 1
    if b ≤ n then b else 0
termination_by n

private def event : ℕ → ℕ
  | 0 => 0
  | i+1 => term i + i + 1

private lemma event_ge (i : ℕ) : i ≤ event i := by
  cases i with
  | zero => rfl
  | succ i => simp only [event]; omega

private lemma term_le_iff (n b : ℕ) :
    term n ≤ b ↔ ∀ i < n, event (i+1) ≤ n → event (i+1) ≤ b := by
  conv_lhs => rw [term]
  simp only [Finset.sup_le_iff, Finset.mem_univ, true_implies]
  constructor
  · intro h i hi he
    have q := h ⟨i, hi⟩
    change (if event (i+1) ≤ n then event (i+1) else 0) ≤ b at q
    simpa [he] using q
  · intro h i
    change (if event (i.val+1) ≤ n then event (i.val+1) else 0) ≤ b
    split_ifs with he
    · exact h i i.isLt he
    · exact Nat.zero_le _

private lemma event_le_term {n i : ℕ} (h : event i ≤ n) : event i ≤ term n := by
  cases i with
  | zero => exact Nat.zero_le _
  | succ i => exact (term_le_iff n _).mp le_rfl i (by have := event_ge (i+1); omega) h

private lemma term_le_index (n : ℕ) : term n ≤ n := (term_le_iff n _).mpr fun _ _ h => h

private lemma term_mono : Monotone term := by
  intro n m h
  exact (term_le_iff n _).mpr fun _ _ he => event_le_term (he.trans h)

private lemma event_strict : StrictMono event := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => have := event_ge 1; change 0 < event 1; omega
  | succ i =>
    have h : term i ≤ term (i+1) := term_mono (Nat.le_succ i)
    simp only [event]
    omega

private lemma phase (i n : ℕ) :
    term n = event i ↔ event i ≤ n ∧ n < event (i+1) := by
  constructor
  · intro h
    refine ⟨h ▸ term_le_index n, ?_⟩
    by_contra! he
    have hh := event_le_term he
    have lt : event i < event (i+1) := event_strict (Nat.lt_succ_self i)
    omega
  · rintro ⟨lo, hi⟩
    apply le_antisymm _ (event_le_term lo)
    apply (term_le_iff n _).mpr
    intro j _ hj
    have h : j+1 < i+1 := event_strict.lt_iff_lt.mp (hj.trans_lt hi)
    exact event_strict.monotone (by omega)

private lemma covers (n : ℕ) : ∃ i, event i ≤ n ∧ n < event (i+1) := by
  induction n with
  | zero => exact ⟨0, le_rfl, event_strict (Nat.zero_lt_succ 0)⟩
  | succ n ih =>
    obtain ⟨i, lo, hi⟩ := ih
    by_cases h : n+1 < event (i+1)
    · exact ⟨i, by omega, h⟩
    · have next : event (i+1) < event (i+1+1) := event_strict (Nat.lt_succ_self (i+1))
      exact ⟨i+1, by omega, by omega⟩

private lemma grows (i : ℕ) : event i < event (i+1) := event_strict (Nat.lt_succ_self i)

private def gap (i : ℕ) : ℕ := event (i+1) - event i

private lemma gap_pos (i : ℕ) : 0 < gap i := Nat.sub_pos_of_lt (grows i)

private lemma event_add_gap (i : ℕ) : event i + gap i = event (i+1) := by
  unfold gap
  have := grows i
  omega

private lemma event_at (i : ℕ) : term (event i) = event i :=
  (phase i _).mpr ⟨le_rfl, grows i⟩

private lemma event_double (i : ℕ) : event (event i+1) = 2*event i+1 := by
  change term (event i) + event i + 1 = _
  rw [event_at]
  omega

private lemma event_le_double (k : ℕ) : event k ≤ 2*k := by
  cases k with
  | zero => rfl
  | succ k =>
    have h := term_le_index k
    change term k+k+1 ≤ 2*(k+1)
    omega

private lemma strict_advance {f : ℕ → ℕ} (h : StrictMono f) (i t : ℕ) :
    f i+t ≤ f (i+t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have inc : f (i+t) < f (i+t+1) := h (Nat.lt_succ_self (i+t))
    change f i+(t+1) ≤ f (i+t+1)
    omega

/-- Every smaller choice would either break strict increase or miss an earlier
value's prescribed count at twice that value. -/
private lemma critical_events : critical event := by
  refine ⟨⟨rfl, event_strict, fun i _ => ⟨event_le_double _, by rw [event_double]; omega⟩⟩, ?_⟩
  intro f sf n agree
  rcases sf with ⟨zero, inc, counts⟩
  cases n with
  | zero => exact zero.symm.le
  | succ j =>
    obtain ⟨i, lo, hi⟩ := covers j
    have value := (phase i j).mpr ⟨lo, hi⟩
    have ile := event_ge i
    change term j+j+1 ≤ f (j+1)
    rcases Nat.eq_zero_or_pos i with h | h
    · subst i
      have e : event 0 = 0 := rfl
      have bound : j+1 ≤ f (j+1) := inc.id_le (j+1)
      omega
    · have fi : f i = event i := (agree i (by omega)).symm
      have right := (counts i h).2
      rw [fi] at right
      have step := strict_advance inc (event i+1) (j-event i)
      rw [show event i+1+(j-event i) = j+1 by omega] at step
      omega

private noncomputable def rank (t : ℕ) := (covers t).choose

private lemma rank_interval (t : ℕ) : event (rank t) ≤ t ∧ t < event (rank t+1) :=
  (covers t).choose_spec

private lemma rank_eq (t j : ℕ) : rank t = j ↔ event j ≤ t ∧ t < event (j+1) := by
  constructor
  · rintro rfl
    exact rank_interval _
  · rintro ⟨lo, hi⟩
    have h := rank_interval t
    have lhs : j < rank t+1 := event_strict.lt_iff_lt.mp (lo.trans_lt h.2)
    have rhs : rank t < j+1 := event_strict.lt_iff_lt.mp (h.1.trans_lt hi)
    omega

private lemma event_affine {i k : ℕ} (lo : event i < k) (hi : k ≤ event (i+1)) :
    event k = k + event i := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j+1 := ⟨k-1, by omega⟩
  have eq := (phase i j).mpr ⟨by omega, by omega⟩
  change term j+j+1 = j+1+event i
  omega

private lemma rank_rising {i m : ℕ} (lo : 2*event i ≤ m) (hi : m < event i + event (i+1)) :
    rank m = m - event i := by
  apply (rank_eq _ _).mpr
  constructor
  · by_cases edge : m = 2*event i
    · rw [show m-event i = event i by omega, edge]
      exact event_le_double _
    · have eq := event_affine (i := i) (k := m-event i) (by omega) (by omega)
      omega
  · have eq := event_affine (i := i) (k := m-event i+1) (by omega) (by omega)
    omega

private lemma rank_flat {i m : ℕ} (lo : event i + event (i+1) ≤ m) (hi : m < 2*event (i+1)) :
    rank m = event (i+1) := by
  apply (rank_eq _ _).mpr
  have left := event_affine (i := i) (k := event (i+1)) (grows i) le_rfl
  have right := event_double (i+1)
  omega

/-- Matching odd positions in a prefix and its reversal must both lie inside
the unique interval that contains the midpoint of the reflection. -/
private lemma reflected {i m t : ℕ} (lo : 2*event i ≤ m) (hi : m < 2*event (i+1)) (ht : t < m) :
    rank t = rank (m-1-t) ↔
      (event i ≤ t ∧ t < event (i+1)) ∧ (event i ≤ m-1-t ∧ m-1-t < event (i+1)) := by
  constructor
  · intro eq
    have left := rank_interval t
    have right := rank_interval (m-1-t)
    rw [← eq] at right
    have h : rank t = i := by
      rcases lt_trichotomy (rank t) i with lt | he | gt
      · have e := event_strict.monotone (show rank t+1 ≤ i by omega)
        omega
      · exact he
      · have e := event_strict.monotone (show i+1 ≤ rank t by omega)
        omega
    rw [h] at left right
    exact ⟨left, right⟩
  · rintro ⟨left, right⟩
    exact ((rank_eq _ _).mpr left).trans ((rank_eq _ _).mpr right).symm

private noncomputable def model (j : ℕ) : ℕ := if j%2 = 0 then 0 else 2*rank (j/2)+1

private lemma model_even (s : ℕ) : model (2*s) = 0 := by simp [model]
private lemma model_odd (s : ℕ) : model (2*s+1) = 2*rank s+1 := by
  simp only [model, if_neg (show (2*s+1)%2 ≠ 0 by omega), show (2*s+1)/2=s by omega]

private def count (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :=
  ((Finset.range n).filter p).card

private lemma mirror_range (n : ℕ) :
    mirror n = count (fun j => mirror j = mirror (n-1-j)) n := by
  conv_lhs => rw [mirror]
  unfold count
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ e
    exact Fin.ext e
  · intro j hj
    obtain ⟨hr, eq⟩ := Finset.mem_filter.mp hj
    exact ⟨⟨j, Finset.mem_range.mp hr⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, eq⟩, rfl⟩

private lemma count_step (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    count p (n+1) = count p n + if p n then 1 else 0 := by
  by_cases h : p n <;> simp [count, Finset.range_add_one, Finset.filter_insert, h]

private lemma count_pairs (p : ℕ → Prop) [DecidablePred p] (m : ℕ) :
    count p (2*m) = count (fun s => p (2*s)) m + count (fun s => p (2*s+1)) m := by
  induction m with
  | zero => simp [count]
  | succ m ih =>
    rw [show 2*(m+1)=2*m+1+1 by omega, count_step, count_step, ih,
        count_step (fun s => p (2*s)) m, count_step (fun s => p (2*s+1)) m]
    omega

private lemma model_even_matches (m : ℕ) :
    count (fun j => model j = model (2*m-1-j)) (2*m) = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hr, e⟩ := Finset.mem_filter.mp hj
  have lt := Finset.mem_range.mp hr
  by_cases h : j%2 = 0
  · have h' : (2*m-1-j)%2 ≠ 0 := by omega
    simp [model, h, h'] at e
  · have h' : (2*m-1-j)%2 = 0 := by omega
    simp [model, h, h'] at e

private lemma split_matches (m : ℕ) :
    count (fun j => model j = model (2*m-j)) (2*m+1) =
      m+1 + count (fun s => rank s = rank (m-1-s)) m := by
  let p (j : ℕ) := model j = model (2*m-j)
  have all (s : ℕ) (hs : s < m) : p (2*s) := by
    change model (2*s) = model (2*m-2*s)
    rw [show 2*m-2*s = 2*(m-s) by omega, model_even, model_even]
  have evens : count (fun s => p (2*s)) m = m := by
    unfold count
    rw [Finset.filter_eq_self.mpr (fun s hs => all s (Finset.mem_range.mp hs)), Finset.card_range]
  have odds : count (fun s => p (2*s+1)) m = count (fun s => rank s = rank (m-1-s)) m := by
    unfold count
    congr 1
    apply Finset.filter_congr
    intro s hs
    have lt := Finset.mem_range.mp hs
    change (model (2*s+1) = model (2*m-(2*s+1))) ↔ _
    rw [show 2*m-(2*s+1) = 2*(m-1-s)+1 by omega, model_odd, model_odd]
    omega
  have last : p (2*m) := by simp [p, model]
  change count p (2*m+1) = _
  rw [count_step, if_pos last, count_pairs, evens, odds]
  omega

private lemma overlap {i m : ℕ} (lo : 2*event i ≤ m) (hi : m < 2*event (i+1)) :
    count (fun s => rank s = rank (m-1-s)) m =
      min (event (i+1)) (m-event i) - max (event i) (m-event (i+1)) := by
  have eq : ((Finset.range m).filter fun s => rank s = rank (m-1-s)) =
      Finset.Ico (max (event i) (m-event (i+1))) (min (event (i+1)) (m-event i)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hs, eq⟩
      have both := (reflected lo hi hs).mp eq
      omega
    · intro inside
      have hs : s < m := by omega
      exact ⟨hs, (reflected lo hi hs).mpr (by omega)⟩
  rw [count, eq, Nat.card_Ico]

private lemma model_odd_matches (m : ℕ) :
    count (fun j => model j = model (2*m-j)) (2*m+1) = 2*rank m+1 := by
  obtain ⟨i, left, right⟩ := covers (m/2)
  have lo : 2*event i ≤ m := by omega
  have hi : m < 2*event (i+1) := by omega
  rw [split_matches, overlap lo hi]
  by_cases h : m < event i+event (i+1)
  · rw [rank_rising lo h]
    omega
  · rw [rank_flat (by omega : event i+event (i+1) ≤ m) hi]
    omega

/-- The candidate satisfies the original reversal-counting recurrence at every index. -/
private lemma mirror_model (n : ℕ) : mirror n = model n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have eq : ((Finset.range n).filter fun j => mirror j = mirror (n-1-j)) =
        ((Finset.range n).filter fun j => model j = model (n-1-j)) := by
      apply Finset.filter_congr
      intro j hj
      have lt := Finset.mem_range.mp hj
      rw [ih j lt, ih (n-1-j) (by omega)]
    rw [mirror_range]
    change ((Finset.range n).filter fun j => mirror j = mirror (n-1-j)).card = _
    rw [eq]
    by_cases h : n%2 = 0
    · obtain ⟨m, rfl⟩ : ∃ m, n = 2*m := ⟨n/2, by omega⟩
      rw [model_even]
      exact model_even_matches m
    · obtain ⟨m, rfl⟩ : ∃ m, n = 2*m+1 := ⟨n/2, by omega⟩
      rw [model_odd, show 2*m+1-1=2*m by omega]
      exact model_odd_matches m

theorem even_terms (m : ℕ) : mirror (2*m) = 0 := (mirror_model _).trans (model_even _)

private lemma fibre (j : ℕ) : {t : ℕ | mirror t = 2*j+1} =
    (fun s : ℕ => 2*s+1) '' Set.Ico (event j) (event (j+1)) := by
  ext t
  change (mirror t = 2*j+1) ↔ ∃ s ∈ Set.Ico (event j) (event (j+1)), 2*s+1 = t
  rw [mirror_model]
  constructor
  · intro e
    by_cases h : t%2 = 0
    · simp [model, h] at e
    · obtain ⟨s, rfl⟩ : ∃ s, t = 2*s+1 := ⟨t/2, by omega⟩
      rw [model_odd] at e
      exact ⟨s, (rank_eq s j).mp (by omega), rfl⟩
  · rintro ⟨s, hs, rfl⟩
    rw [model_odd, (rank_eq s j).mpr hs]

private lemma repetition_eq (j : ℕ) : repetitions j = gap j := by
  rw [repetitions, fibre, Set.ncard_image_of_injective _ (by intro a b h; dsimp at h; omega),
    Set.ncard_Ico_nat]
  rfl

private lemma sums_eq (j : ℕ) : sums j = event j := by
  induction j with
  | zero => simp [sums, event]
  | succ j ih =>
    calc sums (j+1) = sums j + repetitions j := Finset.sum_range_succ _ _
         _ = _ := by rw [ih, repetition_eq, event_add_gap]

/-- All positions with reversal count 2j+1, expressed in terms of the conjectured sums. -/
theorem occurrence_indices (j : ℕ) : {t : ℕ | mirror t = 2*j+1} =
    (fun s : ℕ => 2*s+1) '' Set.Ico (sums j) (sums (j+1)) := by
  simpa only [sums_eq] using fibre j

private lemma critical_sums : critical sums := by
  have eq : sums = event := funext sums_eq
  rw [eq]
  exact critical_events

/-- The prefix-minimum characterization uniquely determines every critical value. -/
theorem critical_eq_sums {c : ℕ → ℕ} (h : critical c) : c = sums := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    exact le_antisymm (h.2 sums critical_sums.1 n ih)
      (critical_sums.2 c h.1 n (fun j hj => (ih j hj).symm))

end OMA.Phutball

theorem OMA.solution : type_of% @OMA.S_oeis_a037988.main := OMA.Phutball.critical_sums

