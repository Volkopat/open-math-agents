import OMAStatements.S_oeis_a110454

-- Problem: A110454: Largest composite number obtained by concatenation of parts of a distinct partition of n, or 0 if no such number exist.
-- Upstream: formal-conjectures statements/oeis-a110454.lean:0 (declaration OMA.S_oeis_a110454.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: every concatenation of a list L is below 10^(sum L), so the candidate set is
-- bounded. For n = 3 and n >= 5 the list [n-2, 2] gives the even candidate 10(n-2)+2 > 2, so
-- a(n) > 0. For n = 1, 2, 4 a list of at least three distinct positive entries has sum >= 6, and
-- a list of two has entries 1, 3 in some order, whose concatenations 13 and 31 are prime.

namespace S02A110454

open OMA.S_oeis_a110454

theorem lt_ten_pow (x : ℕ) : x < 10 ^ x := by
  induction x with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    omega

theorem len_le (x : ℕ) : (Nat.digits 10 x).length ≤ x :=
  (Nat.digits_length_le_iff (by norm_num) x).mpr (lt_ten_pow x)

theorem step_le (acc x : ℕ) :
    acc * 10 ^ (Nat.digits 10 x).length + x + 1 ≤ (acc + 1) * 10 ^ x := by
  have h1 : x < 10 ^ (Nat.digits 10 x).length := Nat.lt_base_pow_length_digits (by norm_num)
  have h2 : 10 ^ (Nat.digits 10 x).length ≤ 10 ^ x := Nat.pow_le_pow_right (by norm_num) (len_le x)
  have h3 : (acc + 1) * 10 ^ (Nat.digits 10 x).length ≤ (acc + 1) * 10 ^ x :=
    Nat.mul_le_mul (le_refl _) h2
  have h4 : (acc + 1) * 10 ^ (Nat.digits 10 x).length
      = acc * 10 ^ (Nat.digits 10 x).length + 10 ^ (Nat.digits 10 x).length := by ring
  omega

theorem fold_lt (L : List ℕ) : ∀ acc : ℕ,
    L.foldl (fun acc x => acc * 10 ^ (Nat.digits 10 x).length + x) acc < (acc + 1) * 10 ^ L.sum := by
  induction L with
  | nil =>
    intro acc
    rw [List.foldl_nil, List.sum_nil, pow_zero, mul_one]
    omega
  | cons x L ih =>
    intro acc
    rw [List.foldl_cons, List.sum_cons]
    have hs := step_le acc x
    calc _ < (acc * 10 ^ (Nat.digits 10 x).length + x + 1) * 10 ^ L.sum := ih _
      _ ≤ ((acc + 1) * 10 ^ x) * 10 ^ L.sum := Nat.mul_le_mul hs (le_refl _)
      _ = (acc + 1) * 10 ^ (x + L.sum) := by ring

theorem bdd (n : ℕ) : BddAbove (comps n) := by
  refine ⟨10 ^ n, fun m hm => ?_⟩
  obtain ⟨L, -, -, hsum, -, hcat, -, -⟩ := hm
  have h := fold_lt L 0
  rw [hsum] at h
  rw [← hcat]
  unfold cat
  omega

theorem cat_two (x y : ℕ) (hy : 0 < y) (hy10 : y < 10) : cat [x, y] = x * 10 + y := by
  have h : Nat.digits 10 y = [y] := Nat.digits_of_lt 10 y (by omega) hy10
  show (0 * 10 ^ (Nat.digits 10 x).length + x) * 10 ^ (Nat.digits 10 y).length + y = x * 10 + y
  rw [h]
  simp

theorem witness (n : ℕ) (hn : 1 ≤ n) (hne : ¬ (n = 1 ∨ n = 2 ∨ n = 4)) :
    (n - 2) * 10 + 2 ∈ comps n := by
  refine ⟨[n - 2, 2], ?_, ?_, ?_, ?_, cat_two (n - 2) 2 (by norm_num) (by norm_num), by omega, ?_⟩
  · rw [List.nodup_cons]
    refine ⟨fun h => ?_, List.nodup_singleton 2⟩
    simp at h
    omega
  · intro x hx
    simp at hx
    omega
  · rw [List.sum_cons, List.sum_cons, List.sum_nil]
    omega
  · simp
  · intro hp
    have h2 : 2 ∣ (n - 2) * 10 + 2 := ⟨(n - 2) * 5 + 1, by ring⟩
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h
    · omega
    · omega

theorem none_in (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 4) (m : ℕ) : m ∉ comps n := by
  intro hm
  obtain ⟨L, hnd, hpos, hsum, hlen, hcat, -, hnp⟩ := hm
  rcases L with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · have hx : 0 < x := hpos x (by simp)
    have hy : 0 < y := hpos y (by simp)
    have hne : x ≠ y := (List.pairwise_cons.mp hnd).1 y (by simp)
    rw [List.sum_cons, List.sum_cons, List.sum_nil] at hsum
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (x = 1 ∧ y = 3) ∨ (x = 3 ∧ y = 1) := by omega
    · rw [cat_two 1 3 (by norm_num) (by norm_num)] at hcat
      rw [← hcat] at hnp
      exact hnp (by norm_num)
    · rw [cat_two 3 1 (by norm_num) (by norm_num)] at hcat
      rw [← hcat] at hnp
      exact hnp (by norm_num)
  · have hx : 0 < x := hpos x (by simp)
    have hy : 0 < y := hpos y (by simp)
    have hz : 0 < z := hpos z (by simp)
    have p1 := List.pairwise_cons.mp hnd
    have p2 := List.pairwise_cons.mp p1.2
    have hxy : x ≠ y := p1.1 y (by simp)
    have hxz : x ≠ z := p1.1 z (by simp)
    have hyz : y ≠ z := p2.1 z (by simp)
    rw [List.sum_cons, List.sum_cons, List.sum_cons] at hsum
    omega

theorem main' (n : ℕ) (hn : 1 ≤ n) : a n = 0 ↔ n = 1 ∨ n = 2 ∨ n = 4 := by
  constructor
  · intro h0
    by_contra hne
    have hle : (n - 2) * 10 + 2 ≤ a n := le_csSup (bdd n) (witness n hn hne)
    omega
  · intro h
    apply Nat.le_zero.mp
    show sSup (comps n) ≤ 0
    apply csSup_le'
    intro m hm
    exact absurd hm (none_in n h m)

end S02A110454

open OMA.S_oeis_a110454 S02A110454 in
theorem OMA.solution : type_of% @OMA.S_oeis_a110454.main := by
  intro n hn
  exact main' n hn
