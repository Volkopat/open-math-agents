import OMAStatements.S_oeis_a318698
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-!
The greedy sequences are from OEIS A318698 and A318699 (OEIS Foundation,
CC BY-SA 4.0). The first starts at zero and follows the parity of the index.
The second starts at one and follows the opposite parity.
https://oeis.org/A318698/internal
https://oeis.org/A318699/internal

Credit: @grp06
-/

namespace OMA.S_oeis_a318698

private theorem some_digit (v : ℕ) : ∃ d, d ∈ digits v := by
  by_cases hv : v = 0
  · exact ⟨0, by simp [digits, hv]⟩
  · cases h : Nat.digits 10 v with
    | nil => exact (hv (Nat.digits_eq_nil_iff_eq_zero.mp h)).elim
    | cons d ds => exact ⟨d, by simp [digits, hv, h]⟩

private theorem digit_lt {v d : ℕ} (h : d ∈ digits v) : d < 10 := by
  by_cases hv : v = 0
  · have hd : d = 0 := by simpa [digits, hv] using h
    omega
  · exact Nat.digits_lt_base (b := 10) (m := v) (d := d)
      (by omega) (by simpa only [digits, if_neg hv] using h)

-- The nonzero prefix ensures that all three suffix positions are present.
private theorem large_suffix {d e r : ℕ} (hd : d < 10) (he : e < 10)
    (hr : r < 2) (t : ℕ) :
    ∃ x > t, x % 2 = r ∧ d ∈ digits x ∧ e ∈ digits x := by
  let x := r + 10 * (e + 10 * (d + 10 * (t + 1)))
  have hdigits : digits x = r :: e :: d :: Nat.digits 10 (t + 1) := by
    have hx : x ≠ 0 := by dsimp [x]; omega
    unfold digits
    rw [if_neg hx]
    dsimp only [x]
    rw [Nat.digits_add 10 (by omega) r (e + 10 * (d + 10 * (t + 1)))
          (by omega) (Or.inr (by omega)),
        Nat.digits_add 10 (by omega) e (d + 10 * (t + 1)) he (Or.inr (by omega)),
        Nat.digits_add 10 (by omega) d (t + 1) hd (Or.inr (by omega))]
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · dsimp [x]
    omega
  · dsimp [x]
    omega
  · simp [hdigits]
  · simp [hdigits]

private theorem eligible_exists (s : Finset ℕ) (v p : ℕ) :
    ∃ x, eligible s v p x := by
  obtain ⟨d, hd⟩ := some_digit v
  obtain ⟨x, hx, hp, hxd, _⟩ :=
    large_suffix (digit_lt hd) (e := 0) (r := p % 2) (by omega) (by omega) (s.sup id)
  refine ⟨x, ?_, hp, ⟨d, hd, hxd⟩⟩
  intro h
  have hle : x ≤ s.sup id := Finset.le_sup (f := id) h
  exact (not_le_of_gt hx) hle

private theorem state_step (seed n : ℕ) :
    state seed (n + 1) =
      (next (state seed n).2 (a seed n) (n + 1 + seed),
       insert (next (state seed n).2 (a seed n) (n + 1 + seed)) (state seed n).2) := by
  cases h : state seed n with
  | mk v s => simp only [a, state, h]

private theorem value_step (seed n : ℕ) :
    a seed (n + 1) = next (state seed n).2 (a seed n) (n + 1 + seed) := by
  exact congrArg Prod.fst (state_step seed n)

private theorem seen_step (seed n : ℕ) :
    (state seed (n + 1)).2 = insert (a seed (n + 1)) (state seed n).2 := by
  rw [value_step, state_step]

private theorem step_eligible (seed n : ℕ) :
    eligible (state seed n).2 (a seed n) (n + 1 + seed) (a seed (n + 1)) := by
  classical
  have h := eligible_exists (state seed n).2 (a seed n) (n + 1 + seed)
  rw [value_step, next, dif_pos h]
  exact Nat.find_spec h

private theorem step_le {seed n m : ℕ}
    (hm : eligible (state seed n).2 (a seed n) (n + 1 + seed) m) :
    a seed (n + 1) ≤ m := by
  classical
  have h : ∃ x, eligible (state seed n).2 (a seed n) (n + 1 + seed) x := ⟨m, hm⟩
  rw [value_step, next, dif_pos h]
  exact Nat.find_min' h hm

private theorem seen_iff (seed n x : ℕ) :
    x ∈ (state seed n).2 ↔ ∃ i ≤ n, a seed i = x := by
  induction n with
  | zero =>
      change x ∈ ({seed} : Finset ℕ) ↔ ∃ i ≤ 0, a seed i = x
      rw [Finset.mem_singleton]
      constructor
      · intro h
        exact ⟨0, le_rfl, h.symm⟩
      · rintro ⟨i, hi, he⟩
        have hi0 : i = 0 := by omega
        subst i
        exact he.symm
  | succ n ih =>
      rw [seen_step, Finset.mem_insert, ih]
      constructor
      · rintro (h | ⟨i, hi, h⟩)
        · exact ⟨n + 1, le_rfl, h.symm⟩
        · exact ⟨i, by omega, h⟩
      · rintro ⟨i, hi, h⟩
        by_cases hlast : i = n + 1
        · subst i
          exact Or.inl h.symm
        · exact Or.inr ⟨i, by omega, h⟩

private theorem value_parity (seed n : ℕ) : a seed n % 2 = (n + seed) % 2 := by
  cases n with
  | zero => simp [a, state]
  | succ n => exact (step_eligible seed n).2.1

private theorem earlier_ne (seed : ℕ) {i j : ℕ} (h : i < j) :
    a seed i ≠ a seed j := by
  cases j with
  | zero => omega
  | succ n =>
      intro heq
      exact (step_eligible seed n).1
        ((seen_iff seed n (a seed (n + 1))).2 ⟨i, by omega, heq⟩)

private theorem value_injective (seed : ℕ) : Function.Injective (a seed) := by
  intro i j h
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · exact earlier_ne seed hlt h
  · exact earlier_ne seed hgt h.symm

-- A finite union of conditions that each eventually fail also eventually fails.
private theorem eventually_avoid (P : ℕ → ℕ → Prop) (S : Finset ℕ) :
    (∀ d ∈ S, ∃ N, ∀ n ≥ N, ¬ P d n) →
      ∃ N, ∀ n ≥ N, ∀ d ∈ S, ¬ P d n := by
  induction S using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨0, fun _ _ d hd => (Finset.notMem_empty d hd).elim⟩
  | insert d S _ ih =>
      intro h
      obtain ⟨Nd, hd⟩ := h d (Finset.mem_insert_self d S)
      obtain ⟨Ns, hs⟩ := ih (fun e he => h e (Finset.mem_insert_of_mem he))
      refine ⟨max Nd Ns, ?_⟩
      intro n hn e he
      rcases Finset.mem_insert.mp he with hde | he
      · subst e
        exact hd n ((le_max_left Nd Ns).trans hn)
      · exact hs n ((le_max_right Nd Ns).trans hn) e he

private def recurrent (seed p d : ℕ) : Prop :=
  ∀ N, ∃ n ≥ N, a seed n % 2 = p ∧ d ∈ digits (a seed n)

private theorem recurrent_even (seed : ℕ) : ∃ d < 10, recurrent seed 0 d := by
  classical
  by_contra h
  have hfinite : ∀ d ∈ Finset.range 10, ∃ N, ∀ n ≥ N,
      ¬ (a seed n % 2 = 0 ∧ d ∈ digits (a seed n)) := by
    intro d hd
    have hnr : ¬ recurrent seed 0 d := fun hr => h ⟨d, Finset.mem_range.mp hd, hr⟩
    obtain ⟨N, hN⟩ := not_forall.mp hnr
    exact ⟨N, fun n hn hp => hN ⟨n, hn, hp⟩⟩
  obtain ⟨N, hN⟩ := eventually_avoid
    (fun d n => a seed n % 2 = 0 ∧ d ∈ digits (a seed n)) (Finset.range 10) hfinite
  let n := 2 * N + seed
  have hp : a seed n % 2 = 0 := by
    rw [value_parity]
    dsimp [n]
    omega
  obtain ⟨d, hd⟩ := some_digit (a seed n)
  exact hN n (by dsimp [n]; omega) d (Finset.mem_range.mpr (digit_lt hd)) ⟨hp, hd⟩

private theorem eventually_above (seed m : ℕ) : ∃ N, ∀ n ≥ N, m < a seed n := by
  classical
  have hfinite : ∀ d ∈ Finset.range (m + 1), ∃ N, ∀ n ≥ N, a seed n ≠ d := by
    intro d _
    by_cases hd : ∃ i, a seed i = d
    · obtain ⟨i, hi⟩ := hd
      refine ⟨i + 1, fun n hn he => ?_⟩
      exact earlier_ne seed (show i < n by omega) (hi.trans he.symm)
    · exact ⟨0, fun n _ he => hd ⟨n, he⟩⟩
  obtain ⟨N, hN⟩ := eventually_avoid (fun d n => a seed n = d)
    (Finset.range (m + 1)) hfinite
  refine ⟨N, fun n hn => ?_⟩
  by_contra hm
  exact hN n hn (a seed n) (Finset.mem_range.mpr (by omega)) rfl

-- Each sufficiently late occurrence of the digit gives another turn on
-- which a missing opposite-parity value would be an eligible choice.
private theorem forced {seed p d m : ℕ} (hr : recurrent seed p d)
    (hm : m % 2 = 1 - p) (hd : d ∈ digits m) : ∃ n, a seed n = m := by
  classical
  by_contra hmissing
  obtain ⟨N, hN⟩ := eventually_above seed m
  obtain ⟨n, hn, hp, hnd⟩ := hr N
  have hpar : m % 2 = (n + 1 + seed) % 2 := by
    have hp' := value_parity seed n
    omega
  have he : eligible (state seed n).2 (a seed n) (n + 1 + seed) m := by
    refine ⟨?_, hpar, ⟨d, hnd, hd⟩⟩
    intro hseen
    obtain ⟨i, _, hi⟩ := (seen_iff seed n m).1 hseen
    exact hmissing ⟨i, hi⟩
  exact (not_le_of_gt (hN (n + 1) (by omega))) (step_le he)

private theorem spread {seed p d e : ℕ} (hr : recurrent seed p d)
    (he : e < 10) : recurrent seed (1 - p) e := by
  intro N
  obtain ⟨i, _, _, hi⟩ := hr 0
  obtain ⟨x, hx, hp, hd, hxe⟩ :=
    large_suffix (digit_lt hi) he (r := 1 - p) (by omega) ((state seed N).2.sup id)
  obtain ⟨n, hn⟩ := forced hr hp hd
  have hlate : N < n := by
    by_contra hnot
    have hmem : x ∈ (state seed N).2 :=
      (seen_iff seed N x).2 ⟨n, by omega, hn⟩
    have hle : x ≤ (state seed N).2.sup id := Finset.le_sup (f := id) hmem
    exact (not_le_of_gt hx) hle
  refine ⟨n, hlate.le, ?_⟩
  rw [hn]
  exact ⟨hp, hxe⟩

private theorem value_surjective (seed : ℕ) : Function.Surjective (a seed) := by
  obtain ⟨d, _, hd⟩ := recurrent_even seed
  have hodd : ∀ e < 10, recurrent seed 1 e := fun e he => spread hd he
  have heven : ∀ e < 10, recurrent seed 0 e := fun e he => spread (hodd 0 (by omega)) he
  intro m
  obtain ⟨e, he⟩ := some_digit m
  by_cases hm : m % 2 = 0
  · exact forced (hodd e (digit_lt he)) hm he
  · exact forced (heven e (digit_lt he)) (by omega) he

end OMA.S_oeis_a318698

theorem OMA.solution : type_of% @OMA.S_oeis_a318698.main := by
  exact ⟨⟨OMA.S_oeis_a318698.value_injective 0, OMA.S_oeis_a318698.value_surjective 0⟩,
    ⟨OMA.S_oeis_a318698.value_injective 1, OMA.S_oeis_a318698.value_surjective 1⟩⟩
