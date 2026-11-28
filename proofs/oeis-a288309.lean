import OMAStatements.S_oeis_a288309

namespace OMA.S_oeis_a288309

-- Original proof by @jleguina.

/-- The number of disjoint 00 pairs read greedily from the left. -/
private def pairs : List ℕ → ℕ
  | 0 :: 0 :: w => pairs w + 1
  | _ :: w => pairs w
  | [] => 0

/-- A pending zero lets the output pair count follow the same greedy recursion.
Scanning either 00 or 01 contributes one pair, and scanning 1 contributes none. -/
private theorem scan_stats : ∀ w : List ℕ, (∀ d ∈ w, d ≤ 1) →
    (∀ d ∈ step w, d ≤ 1) ∧ w.length = w.count 0 + w.count 1 ∧
    (step w).count 0 = w.count 0 + w.count 1 + pairs w ∧
    (step w).count 1 = 2 * w.count 1 + pairs w ∧
    pairs (0 :: step w) + pairs w = w.count 0
  | [], _ => by simp [step, pairs]
  | [0], _ => by decide
  | 0 :: 0 :: w, h => by
    obtain ⟨hb, hl, hz, ho, hp⟩ := scan_stats w (fun d hd => h d (by simp [hd]))
    simp [step, pairs, hl, hz, ho]
    exact ⟨hb, by omega⟩
  | 0 :: 1 :: w, h => by
    obtain ⟨hb, hl, hz, ho, hp⟩ := scan_stats w (fun d hd => h d (by simp [hd]))
    simp [step, pairs, hl, hz, ho]
    exact ⟨hb, by omega⟩
  | 1 :: w, h => by
    obtain ⟨hb, hl, hz, ho, hp⟩ := scan_stats w (fun d hd => h d (by simp [hd]))
    simp [step, pairs, hl, hz, ho]
    exact ⟨hb, by omega⟩
  | 0 :: (k + 2) :: w, h => by
    have := h (k + 2) (by simp)
    omega
  | (k + 2) :: w, h => by
    have := h (k + 2) (by simp)
    omega

private theorem iter_succ_eq (n : ℕ) : iter (n + 1) = step (iter n) := by
  simp only [iter, Function.iterate_succ_apply']

private theorem iter_properties (n : ℕ) : (∀ d ∈ iter n, d ≤ 1) ∧ ∃ t, iter n = 0 :: 0 :: t := by
  induction n with
  | zero => exact ⟨by simp [iter], ⟨[], rfl⟩⟩
  | succ n ih =>
    obtain ⟨hb, t, ht⟩ := ih
    rw [iter_succ_eq]
    refine ⟨(scan_stats _ hb).1, ?_⟩
    rw [ht]
    exact ⟨1 :: 0 :: step t, rfl⟩

private def zeroCount (n : ℕ) : ℕ := (iter n).count 0
private def oneCount (n : ℕ) : ℕ := (iter n).count 1
private def pairCount (n : ℕ) : ℕ := pairs (iter n)

private theorem iter_step_stats (n : ℕ) :
    zeroCount (n + 1) = zeroCount n + oneCount n + pairCount n ∧ oneCount (n + 1) = 2 * oneCount n + pairCount n ∧ pairCount (n + 1) + pairCount n = zeroCount n := by
  obtain ⟨hb, t, ht⟩ := iter_properties n
  obtain ⟨_, _, hz, ho, hp⟩ := scan_stats _ hb
  have hpend : pairs (0 :: step (iter n)) = pairs (step (iter n)) := by rw [ht]; rfl
  rw [hpend] at hp
  simpa only [zeroCount, oneCount, pairCount, iter_succ_eq] using And.intro hz (And.intro ho hp)

private theorem len_iter (n : ℕ) : ((iter n).length : ℤ) = zeroCount n + oneCount n := by
  have h := (scan_stats _ (iter_properties n).1).2.1
  unfold zeroCount oneCount
  omega

private theorem len_rec (n : ℕ) : ((iter (n + 3)).length : ℤ) = 2 * (iter (n + 2)).length +
    2 * (iter (n + 1)).length - 3 * (iter n).length := by
  simp only [len_iter]
  obtain ⟨hz, ho, hp⟩ := iter_step_stats n
  obtain ⟨hz', ho', hp'⟩ := iter_step_stats (n + 1)
  obtain ⟨hz'', ho'', hp''⟩ := iter_step_stats (n + 2)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hz' ho' hp' hz'' ho'' hp''
  omega

/-- Kimberling's conjecture: the n-th iterate has a(n) letters. -/
theorem conjecture : ∀ n : ℕ, ((iter n).length : ℤ) = A n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | k + 3 =>
      rw [len_rec k, A, ih (k + 2) (by omega), ih (k + 1) (by omega), ih k (by omega)]

/-- Controls: the iterates 00, 0010, 00101100 and a(0..6) = 2, 4, 8, 18, 40, 92, 210. -/
example : iter 1 = [0, 0, 1, 0] ∧ iter 2 = [0, 0, 1, 0, 1, 1, 0, 0] ∧
    (List.range 7).map (fun n => (iter n).length) = [2, 4, 8, 18, 40, 92, 210] := by
  decide +kernel

end OMA.S_oeis_a288309

theorem OMA.solution : type_of% @OMA.S_oeis_a288309.main :=
  OMA.S_oeis_a288309.conjecture
