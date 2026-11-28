import OMAStatements.S_oeis_a359807

/-!

Complete proof by @frido22, linked from merged statement PR #21410:
https://github.com/frido22/open-math-agents/blob/d8a293c1b77bd7ed404c812cc4b049306df86240/proofs/oeis-a359807.lean
This port retains the mathematical source unchanged and adds provenance credit.
The underlying sequences are due to Neal Gersh Tolunsky and Ivan Neretin.

The candidate values are the increasing events B(0)=0, B(i+1)=term(i)+i+1.
A gap of size d between events creates d-1 unit gaps and then a gap of size d+1.
This derives Ivan Neretin’s substitution from Neal Gersh Tolunsky’s recurrence.
Source: https://oeis.org/A359807 and https://oeis.org/A272729.
-/

open OMA.S_oeis_a359807

namespace OMA.Tolunsky

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

private lemma gap_zero : gap 0 = 1 := by
  have h := term_le_index 0
  simp only [gap, event]
  omega

private lemma gap_step (t : ℕ) : gap (t+1) + term t = term (t+1)+1 := by
  have h : term t ≤ term (t+1) := term_mono (Nat.le_succ t)
  simp only [gap, event]
  omega

private lemma interior_gap (i t : ℕ) (lo : event i ≤ t) (hi : t+1 < event (i+1)) :
    gap (t+1) = 1 := by
  have left := (phase i t).mpr ⟨lo, by omega⟩
  have right := (phase i (t+1)).mpr ⟨by omega, hi⟩
  have inc := gap_step t
  omega

private lemma last_gap (i : ℕ) : gap (event (i+1)) = gap i + 1 := by
  have lt := grows i
  have h : event (i+1)-1+1 = event (i+1) := by omega
  have left := (phase i (event (i+1)-1)).mpr ⟨by omega, by omega⟩
  have right := (phase (i+1) (event (i+1))).mpr ⟨le_rfl, grows (i+1)⟩
  have inc := gap_step (event (i+1)-1)
  rw [h] at inc
  have eq := event_add_gap i
  omega

/-- Consecutive gaps, starting at position p. -/
private def segment (p len : ℕ) : List ℕ :=
  match len with
  | 0 => []
  | k+1 => gap p :: segment (p+1) k

private lemma segment_join (p u v : ℕ) :
    segment p (u+v) = segment p u ++ segment (p+u) v := by
  induction u generalizing p with
  | zero => simp [segment]
  | succ u ih =>
    rw [show u+1+v = (u+v)+1 by omega]
    simp only [segment, List.cons_append]
    rw [ih, show p+1+u = p+(u+1) by omega]

private lemma segment_ones (p len : ℕ) (h : ∀ t, p ≤ t → t < p+len → gap t = 1) :
    segment p len = List.replicate len 1 := by
  induction len generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [segment, h p le_rfl (by omega), List.replicate_succ]
    congr 1
    exact ih (p+1) (fun t lo hi => h t (by omega) (by omega))

/-- A run of length d produces d-1 unit gaps and then one gap of length d+1. -/
private lemma children (i : ℕ) : segment (event i+1) (gap i) = substLetter (gap i) := by
  have pos := gap_pos i
  have sum := event_add_gap i
  have ones : segment (event i+1) (gap i-1) = List.replicate (gap i-1) 1 := by
    apply segment_ones
    intro t lo hi
    obtain ⟨u, rfl⟩ : ∃ u, t = u+1 := ⟨t-1, by omega⟩
    exact interior_gap i u (by omega) (by omega)
  calc
    segment (event i+1) (gap i) = segment (event i+1) ((gap i-1)+1) := by congr 1; omega
    _ = segment (event i+1) (gap i-1) ++ segment (event i+1+(gap i-1)) 1 := segment_join _ _ _
    _ = substLetter (gap i) := by
      rw [ones, show event i+1+(gap i-1) = event (i+1) by omega]
      simp [segment, last_gap, substLetter]

/-- After reading i letters, all the gaps from i through event(i) are waiting in the queue. -/
private lemma unread_eq (i : ℕ) : unread i = gap i :: segment (i+1) (event i-i) := by
  induction i with
  | zero => simp [unread, gap_zero, event, segment]
  | succ i ih =>
    rw [unread, ih]
    change segment (i+1) (event i-i) ++ substLetter (gap i) =
      gap (i+1) :: segment (i+1+1) (event (i+1)-(i+1))
    have ei := event_ge i
    have en := event_ge (i+1)
    have sum := event_add_gap i
    rw [← children, ← show i+1+(event i-i) = event i+1 by omega, ← segment_join]
    rw [show event i-i+gap i = (event (i+1)-(i+1))+1 by omega, segment]

private lemma run_eq (i : ℕ) : runLength i = gap i := by
  rw [runLength, unread_eq]
  rfl

private lemma start_eq (i : ℕ) : start i = event i := by
  induction i with
  | zero => simp [start, event]
  | succ i ih =>
    calc start (i+1) = start i + runLength i := Finset.sum_range_succ _ _
         _ = _ := by rw [ih, run_eq, event_add_gap]

/-- The successive words in Neretin's trajectory, starting from the single letter 1. -/
def generation : ℕ → List ℕ
  | 0 => [1]
  | k+1 => (generation k).flatMap substLetter

def generationStart : ℕ → ℕ
  | 0 => 0
  | k+1 => generationStart k + (generation k).length

private lemma consume (w : List ℕ) (n : ℕ) (tail : List ℕ) (h : unread n = w ++ tail) :
    (List.range' n w.length).map runLength = w ∧ unread (n+w.length) = tail ++ w.flatMap substLetter := by
  induction w generalizing n tail with
  | nil => simpa using h
  | cons x xs ih =>
    have hx : runLength n = x := by rw [runLength, h]; rfl
    have next : unread (n+1) = xs ++ (tail ++ substLetter x) := by
      simp [unread, h, List.append_assoc]
    obtain ⟨read, left⟩ := ih (n+1) (tail ++ substLetter x) next
    refine ⟨?_, ?_⟩
    · simp only [List.length_cons, List.range'_succ, List.map_cons, hx, read]
    · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using left

private lemma generation_ready (k : ℕ) : unread (generationStart k) = generation k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := (consume (generation k) (generationStart k) [] (by simpa using ih)).2
    simpa [generationStart, generation] using h

/-- Each entire row of the substitution appears, in order, in the run-length sequence. -/
theorem reads_generations (k : ℕ) :
    (List.range' (generationStart k) (generation k).length).map runLength = generation k :=
  (consume (generation k) (generationStart k) [] (by simpa using generation_ready k)).1

/-- At original index 2^k the sequence takes the value 2^k-1. -/
theorem at_powers_of_two (k : ℕ) : term (2^k-1) = 2^k-1 := by
  induction k with
  | zero => simpa using (Nat.eq_zero_of_le_zero (term_le_index 0))
  | succ k ih =>
    have pos : 0 < 2^k := by positivity
    have eq : event (2^k) = 2^(k+1)-1 := calc
      event (2^k) = event ((2^k-1)+1) := congrArg event (by omega)
      _ = term (2^k-1) + (2^k-1) + 1 := rfl
      _ = 2^(k+1)-1 := by rw [ih, pow_succ]; omega
    simpa only [eq] using ((phase (2^k) (event (2^k))).mpr ⟨le_rfl, grows _⟩)

end OMA.Tolunsky

open OMA.Tolunsky

theorem OMA.solution : type_of% @OMA.S_oeis_a359807.main := by
  refine ⟨fun i => ⟨by rw [run_eq]; exact gap_pos i, fun n => by simpa only [start_eq] using phase i n⟩, ?_⟩
  ext v
  constructor
  · rintro ⟨n, rfl⟩
    obtain ⟨i, h⟩ := covers n
    exact ⟨i, (start_eq i).trans ((phase i n).mpr h).symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨event i, ?_⟩
    rw [start_eq]
    exact (phase i _).mpr ⟨le_rfl, grows i⟩

