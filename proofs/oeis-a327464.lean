import OMAStatements.S_oeis_a327464

namespace OMA.S_oeis_a327464

/-- Least prime and least composite strictly above each input from 0 through 107. -/
private def primeTable : List ℕ :=
  [2, 2, 3, 5, 5, 7, 7, 11, 11, 11, 11, 13, 13, 17, 17, 17,
   17, 19, 19, 23, 23, 23, 23, 29, 29, 29, 29, 29, 29, 31, 31, 37,
   37, 37, 37, 37, 37, 41, 41, 41, 41, 43, 43, 47, 47, 47, 47, 53,
   53, 53, 53, 53, 53, 59, 59, 59, 59, 59, 59, 61, 61, 67, 67, 67,
   67, 67, 67, 71, 71, 71, 71, 73, 73, 79, 79, 79, 79, 79, 79, 83,
   83, 83, 83, 89, 89, 89, 89, 89, 89, 97, 97, 97, 97, 97, 97, 97,
   97, 101, 101, 101, 101, 103, 103, 107, 107, 107, 107, 109]

private def compositeTable : List ℕ :=
  [4, 4, 4, 4, 6, 6, 8, 8, 9, 10, 12, 12, 14, 14, 15, 16,
   18, 18, 20, 20, 21, 22, 24, 24, 25, 26, 27, 28, 30, 30, 32, 32,
   33, 34, 35, 36, 38, 38, 39, 40, 42, 42, 44, 44, 45, 46, 48, 48,
   49, 50, 51, 52, 54, 54, 55, 56, 57, 58, 60, 60, 62, 62, 63, 64,
   65, 66, 68, 68, 69, 70, 72, 72, 74, 74, 75, 76, 77, 78, 80, 80,
   81, 82, 84, 84, 85, 86, 87, 88, 90, 90, 91, 92, 93, 94, 95, 96,
   98, 98, 99, 100, 102, 102, 104, 104, 105, 106, 108, 108]

/-- Reachable values grouped by the index modulo six, starting at index four. -/
private def states : ℕ → List ℕ
  | 0 => [1, 4, 6, 12, 16, 18, 22, 24, 54]
  | 1 => [1, 2, 4, 6, 7, 11, 13, 16, 17, 18, 19, 22, 23, 24, 101, 107]
  | 2 => [1, 4, 6, 12, 16, 18, 22, 24, 54, 84]
  | 3 => [1, 4, 6, 7, 13, 16, 18, 22, 24]
  | 4 => [1, 4, 6, 16, 18, 22, 24]
  | 5 => [1, 2, 4, 6, 11, 13, 16, 18, 19, 23, 24, 101]
  | _ => []

private def candidate (b : Bool) (m : ℕ) : ℕ :=
  ((if b then primeTable else compositeTable)[m]?).getD 0

private def qualifies (b : Bool) (m k : ℕ) : Prop :=
  m < k ∧ if b then k.Prime else 1 < k ∧ ¬ k.Prime

private instance (b : Bool) (m k : ℕ) : Decidable (qualifies b m k) := by
  unfold qualifies
  infer_instance

private def checkEntry (m : ℕ) (b : Bool) : Bool :=
  decide (qualifies b m (candidate b m)) &&
    (List.range (candidate b m - (m + 1))).all
      (fun gap => !decide (qualifies b m (m + 1 + gap)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem tables_checked :
    (List.range 108).all (fun m => checkEntry m false && checkEntry m true) = true := by
  decide +kernel

private theorem tables_correct (b : Bool) (m : Fin 108) :
    qualifies b m (candidate b m) ∧
      ∀ gap : Fin (candidate b m - (m + 1)), ¬ qualifies b m (m + 1 + gap) := by
  have hc := (List.all_eq_true.mp tables_checked) m.val (List.mem_range.mpr m.isLt)
  simp only [Bool.and_eq_true] at hc
  have hb : checkEntry m b = true := by
    cases b with
    | false => exact hc.1
    | true => exact hc.2
  simp only [checkEntry, Bool.and_eq_true, decide_eq_true_eq] at hb
  refine ⟨hb.1, fun gap => ?_⟩
  have hg := (List.all_eq_true.mp hb.2) gap.val (List.mem_range.mpr gap.isLt)
  simpa using hg

private theorem least_candidate (b : Bool) (m : ℕ) (hm : m ≤ 107) :
    sInf {k | qualifies b m k} = candidate b m := by
  have hc := tables_correct b ⟨m, by omega⟩
  have hh : candidate b m ∈ {k | qualifies b m k} := hc.1
  have hi := Nat.sInf_mem (show {k | qualifies b m k}.Nonempty from ⟨_, hh⟩)
  apply le_antisymm (Nat.sInf_le hh)
  by_contra hn
  have hlow : m < sInf {k | qualifies b m k} := hi.1
  let k := sInf {k | qualifies b m k}
  have hgap : k - (m + 1) < candidate b m - (m + 1) := by
    change ¬ candidate b m ≤ k at hn
    change m < k at hlow
    omega
  have he : m + 1 + (k - (m + 1)) = k := by
    change m < k at hlow
    omega
  have ht := hc.2 ⟨k - (m + 1), hgap⟩
  change ¬ qualifies b m (m + 1 + (k - (m + 1))) at ht
  rw [he] at ht
  exact ht hi

private def primeFlag (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range (n.sqrt + 1)).all (fun d => decide (d < 2 ∨ n % d ≠ 0))

private theorem primeFlag_true (n : ℕ) : primeFlag n = true ↔ n.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [primeFlag, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Nat.dvd_iff_mod_eq_zero]
  constructor
  · rintro ⟨hn, h⟩
    exact ⟨hn, fun d hd hb => (h d (by omega)).resolve_left (by omega)⟩
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun d hd => ?_⟩
    by_cases ht : d < 2
    · exact Or.inl ht
    · exact Or.inr (h d (by omega) (by omega))

private theorem primeFlag_eq_decide (n : ℕ) : primeFlag n = decide n.Prime := by
  cases hb : primeFlag n
  · have hp : ¬ n.Prime := fun hh => by
      have hw := (primeFlag_true n).mpr hh
      rw [hb] at hw
      contradiction
    simp [hp]
  · have hp := (primeFlag_true n).mp hb
    simp [hp]

private def step (n v : ℕ) : ℕ := rev5 (candidate (primeFlag n) v)

private def fast : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => step (n + 2) (fast (n + 1))

private theorem step_fast (n : ℕ) (hn : 1 ≤ n) : fast (n + 1) = step (n + 1) (fast n) := by
  cases n with
  | zero => omega
  | succ n => rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem transition_table : ∀ r : Fin 6,
    (states r.val).all (fun m => decide (
      rev5 (candidate false m) ∈ states ((r.val + 1) % 6) ∧
      ((r.val = 0 ∨ r.val = 4) →
        rev5 (candidate true m) ∈ states ((r.val + 1) % 6)))) := by
  decide +kernel

private theorem transition (r : Fin 6) (m : Fin 108) (b : Bool)
    (hm : m.val ∈ states r.val) (hb : b = true → r.val = 0 ∨ r.val = 4) :
    rev5 (candidate b m) ∈ states ((r.val + 1) % 6) := by
  have h := of_decide_eq_true ((List.all_eq_true.mp (transition_table r)) m.val hm)
  cases b with
  | false => exact h.1
  | true => exact h.2 (hb rfl)

private theorem states_bounded : ∀ r : Fin 6, (states r.val).all (fun v => decide (v ≤ 107)) := by
  decide +kernel

private theorem state_bound (r v : ℕ) (hr : r < 6) (hv : v ∈ states r) : v ≤ 107 := by
  exact of_decide_eq_true ((List.all_eq_true.mp (states_bounded ⟨r, hr⟩)) v hv)

private theorem prime_case (n : ℕ) (hn : 4 ≤ n) (hp : (n + 1).Prime) :
    n % 6 = 0 ∨ n % 6 = 4 := by
  have h2 : ¬ 2 ∣ n + 1 := by
    intro hd
    have h := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd
    omega
  have h3 : ¬ 3 ∣ n + 1 := by
    intro hd
    have h := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd
    omega
  omega

private theorem fast_valid (m : ℕ) : fast (m + 4) ∈ states ((m + 4) % 6) := by
  induction m with
  | zero => decide +kernel
  | succ m ih =>
    let n := m + 4
    have hn : 4 ≤ n := by dsimp [n]; omega
    have hval : fast n ≤ 107 := state_bound _ _ (Nat.mod_lt _ (by decide)) ih
    have hh := transition ⟨n % 6, Nat.mod_lt _ (by decide)⟩
      ⟨fast n, by omega⟩ (decide (n + 1).Prime) ih
      (fun h => prime_case n hn (of_decide_eq_true h))
    change fast (n + 1) ∈ states ((n + 1) % 6)
    rw [step_fast _ (by omega), step, primeFlag_eq_decide,
      show (n + 1) % 6 = (n % 6 + 1) % 6 by omega]
    exact hh

private theorem fast_bound (n : ℕ) : fast n ≤ 107 := by
  by_cases hn : 4 ≤ n
  · rw [show n = n - 4 + 4 by omega]
    exact state_bound _ _ (Nat.mod_lt _ (by decide)) (fast_valid (n - 4))
  · interval_cases n <;> decide +kernel

private theorem agrees (n : ℕ) : a n = fast n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [a, fast, step, primeFlag_eq_decide, ih]
      by_cases h : (n + 2).Prime
      · simp only [h, if_true, decide_true]
        rw [nextPrime, ← least_candidate true _ (fast_bound (n + 1))]
        rfl
      · simp only [h, if_false, decide_false]
        rw [nextComposite, ← least_candidate false _ (fast_bound (n + 1))]
        rfl

private def scan (i v : ℕ) : ℕ → Bool
  | 0 => decide (v < 107)
  | k + 1 => decide (v < 107) && scan (i + 1) (step (i + 1) v) k

private theorem scan_sound (k i : ℕ) (hi : 1 ≤ i)
    (h : scan i (fast i) k = true) : ∀ j ≤ k, fast (i + j) < 107 := by
  induction k generalizing i with
  | zero =>
    intro j hj
    have he : j = 0 := by omega
    subst j
    simpa [scan] using h
  | succ k ih =>
    simp only [scan, Bool.and_eq_true, decide_eq_true_eq] at h
    intro j hj
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have hs : scan (i + 1) (fast (i + 1)) k = true := by
        rw [step_fast i hi]
        exact h.2
      have hk := ih (i + 1) (by omega) hs j (by omega)
      rwa [show i + 1 + j = i + (j + 1) by omega] at hk

private def advance (i v : ℕ) : ℕ → ℕ
  | 0 => v
  | k + 1 => advance (i + 1) (step (i + 1) v) k

private theorem advance_sound (k i : ℕ) (hi : 1 ≤ i) :
    advance i (fast i) k = fast (i + k) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    rw [advance, ← step_fast i hi, ih (i + 1) (by omega),
      show i + 1 + k = i + (k + 1) by omega]

/-- Starting values for the checked blocks of 21 consecutive indices. -/
private def checkpoint (j : ℕ) : ℕ :=
  ([1, 16, 1, 16, 24, 16, 11, 4, 24, 4, 13, 16, 1, 16, 6, 16, 1, 6, 1, 1, 17, 16, 1, 16, 6, 16, 1, 4, 6, 16, 13, 4, 13, 1, 16, 24, 13, 4, 6, 4, 6, 16, 107] : List ℕ)[j]?.getD 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
private theorem certificates : ∀ j : Fin 42,
    advance (1 + 21 * j.val) (checkpoint j.val) 21 = checkpoint (j.val + 1) ∧
    scan (1 + 21 * j.val) (checkpoint j.val) 20 = true := by
  intro j
  fin_cases j <;> decide +kernel

private theorem fast_checkpoint (j : ℕ) (hj : j ≤ 42) :
    fast (1 + 21 * j) = checkpoint j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hh := (certificates ⟨j, by omega⟩).1
    change advance (1 + 21 * j) (checkpoint j) 21 = checkpoint (j + 1) at hh
    rw [← ih (by omega), advance_sound _ _ (by omega)] at hh
    rw [show 1 + 21 * (j + 1) = 1 + 21 * j + 21 by omega]
    exact hh

private theorem reaches : fast 883 = 107 := by
  have h := fast_checkpoint 42 (by decide)
  exact h

private theorem earlier (n : ℕ) (hn : 1 ≤ n) (hlt : n < 883) : fast n < 107 := by
  let j := (n - 1) / 21
  let i := (n - 1) % 21
  have hj : j < 42 := by dsimp [j]; omega
  have hi : i ≤ 20 := by dsimp [i]; omega
  have hh := (certificates ⟨j, hj⟩).2
  change scan (1 + 21 * j) (checkpoint j) 20 = true at hh
  rw [← fast_checkpoint j (by omega)] at hh
  have ht := scan_sound 20 (1 + 21 * j) (by omega) hh i hi
  have he : 1 + 21 * j + i = n := by dsimp [j, i]; omega
  rwa [he] at ht

end OMA.S_oeis_a327464

theorem OMA.solution : type_of% @OMA.S_oeis_a327464.main := by
  refine ⟨fun n _ => ?_, ?_, fun n hn hlt => ?_⟩
  · rw [OMA.S_oeis_a327464.agrees]
    exact OMA.S_oeis_a327464.fast_bound n
  · rw [OMA.S_oeis_a327464.agrees]
    exact OMA.S_oeis_a327464.reaches
  · rw [OMA.S_oeis_a327464.agrees]
    exact OMA.S_oeis_a327464.earlier n hn hlt
