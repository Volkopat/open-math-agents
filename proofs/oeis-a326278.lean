import OMAStatements.S_oeis_a326278
import Mathlib

-- Problem: OEIS A326278, the number of ordered pairs of edges on n vertices that are not
-- nesting (or not crossing). Conjectures of Colin Barker: a(n) = n(3 - 4n + n^3)/6 and the
-- recurrence of order 5.
-- Statement: statements/oeis-a326278.lean (declaration OMA.S_oeis_a326278.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. The indicator of a pair that is not nesting is
--   [a < b][c < d] - [a < c < d < b] - [c < a < b < d],
-- because the two nesting patterns exclude each other and each implies a < b and c < d. The sum
-- of [a < b][c < d] over all a, b, c, d < n is (n(n-1)/2)^2. Each chain pattern has the sum
-- n(n-1)(n-2)(n-3)/24: after a permutation of the four sums it is the sum over b, d, c, a of
-- [a < c < d < b], which is computed from the inside (lemma chain4). The same is true for the
-- two crossing patterns. So both counts are (n(n-1)/2)^2 - n(n-1)(n-2)(n-3)/12
-- = n(n^3 - 4n + 3)/6, and the recurrence holds for each polynomial of degree 4.

namespace OMA.A326278

open OMA.S_oeis_a326278 Finset

/-- The fourfold sum over `range n`. -/
def S4 (n : ℕ) (H : ℕ → ℕ → ℕ → ℕ → ℚ) : ℚ :=
  ∑ a ∈ range n, ∑ b ∈ range n, ∑ c ∈ range n, ∑ d ∈ range n, H a b c d

lemma rev3 (n : ℕ) (F : ℕ → ℕ → ℕ → ℚ) :
    ∑ x ∈ range n, ∑ y ∈ range n, ∑ z ∈ range n, F x y z
      = ∑ z ∈ range n, ∑ y ∈ range n, ∑ x ∈ range n, F x y z := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun y _ => Finset.sum_comm]
  rw [Finset.sum_comm]

lemma swap24 (n : ℕ) (H : ℕ → ℕ → ℕ → ℕ → ℚ) : S4 n H = S4 n (fun a d c b => H a b c d) := by
  unfold S4
  exact Finset.sum_congr rfl fun a _ => rev3 n (fun b c d => H a b c d)

lemma swapBlocks (n : ℕ) (H : ℕ → ℕ → ℕ → ℕ → ℚ) : S4 n H = S4 n (fun c d a b => H a b c d) := by
  unfold S4
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_comm]

lemma toChain (n : ℕ) (H : ℕ → ℕ → ℕ → ℕ → ℚ) :
    S4 n H = ∑ b ∈ range n, ∑ d ∈ range n, ∑ c ∈ range n, ∑ a ∈ range n, H a b c d := by
  unfold S4
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => rev3 n (fun a c d => H a b c d)

lemma restrict (n y : ℕ) (hy : y ≤ n) (g : ℕ → ℚ) :
    ∑ x ∈ range n, (if x < y then g x else 0) = ∑ x ∈ range y, g x := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma sum1 (m : ℕ) : ∑ x ∈ range m, (x : ℚ) = (m : ℚ) * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum2 (m : ℕ) : ∑ x ∈ range m, ((x : ℚ) * (x - 1) / 2) = (m : ℚ) * (m - 1) * (m - 2) / 6 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum3 (m : ℕ) :
    ∑ x ∈ range m, ((x : ℚ) * (x - 1) * (x - 2) / 6) = (m : ℚ) * (m - 1) * (m - 2) * (m - 3) / 24 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The number of chains a < c < d < b below n. -/
lemma chain4 (n : ℕ) :
    ∑ b ∈ range n, ∑ d ∈ range n, ∑ c ∈ range n, ∑ a ∈ range n,
      (if a < c ∧ c < d ∧ d < b then (1 : ℚ) else 0)
      = (n : ℚ) * (n - 1) * (n - 2) * (n - 3) / 24 := by
  have h1 : ∀ b ∈ range n, ∀ d ∈ range n, ∀ c ∈ range n,
      ∑ a ∈ range n, (if a < c ∧ c < d ∧ d < b then (1 : ℚ) else 0)
        = if c < d then (if d < b then (c : ℚ) else 0) else 0 := by
    intro b _ d _ c hc
    by_cases h : c < d ∧ d < b
    · rw [if_pos h.1, if_pos h.2]
      have : ∀ a, (if a < c ∧ c < d ∧ d < b then (1 : ℚ) else 0) = if a < c then 1 else 0 := by
        intro a
        by_cases ha : a < c <;> simp [ha, h.1, h.2]
      simp only [this]
      rw [restrict n c (Finset.mem_range.mp hc).le]
      simp
    · have : ∀ a, (if a < c ∧ c < d ∧ d < b then (1 : ℚ) else 0) = 0 := by
        intro a
        rw [if_neg (fun hh => h hh.2)]
      simp only [this, Finset.sum_const_zero]
      by_cases h' : c < d
      · rw [if_pos h', if_neg (fun hh => h ⟨h', hh⟩)]
      · rw [if_neg h']
  have h2 : ∀ b ∈ range n, ∀ d ∈ range n,
      ∑ c ∈ range n, (if c < d then (if d < b then (c : ℚ) else 0) else 0)
        = if d < b then (d : ℚ) * (d - 1) / 2 else 0 := by
    intro b _ d hd
    rw [restrict n d (Finset.mem_range.mp hd).le]
    by_cases h : d < b
    · simp only [if_pos h]
      exact sum1 d
    · simp only [if_neg h, Finset.sum_const_zero]
  have h3 : ∀ b ∈ range n,
      ∑ d ∈ range n, (if d < b then (d : ℚ) * (d - 1) / 2 else 0)
        = (b : ℚ) * (b - 1) * (b - 2) / 6 := by
    intro b hb
    rw [restrict n b (Finset.mem_range.mp hb).le]
    exact sum2 b
  rw [← sum3 n]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [← h3 b hb]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← h2 b hb d hd]
  exact Finset.sum_congr rfl fun c hc => h1 b hb d hd c hc

lemma pairs (n : ℕ) :
    ∑ a ∈ range n, ∑ b ∈ range n, (if a < b then (1 : ℚ) else 0) = (n : ℚ) * (n - 1) / 2 := by
  rw [Finset.sum_comm, ← sum1 n]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [restrict n b (Finset.mem_range.mp hb).le]
  simp

/-- The four chain patterns have the same count. -/
lemma pat1 (n : ℕ) :
    S4 n (fun a b c d => if a < c ∧ c < d ∧ d < b then (1 : ℚ) else 0)
      = (n : ℚ) * (n - 1) * (n - 2) * (n - 3) / 24 := by
  rw [toChain, chain4]

lemma pat2 (n : ℕ) :
    S4 n (fun a b c d => if c < a ∧ a < b ∧ b < d then (1 : ℚ) else 0)
      = (n : ℚ) * (n - 1) * (n - 2) * (n - 3) / 24 := by
  rw [swapBlocks, pat1]

lemma pat3 (n : ℕ) :
    S4 n (fun a b c d => if a < c ∧ c < b ∧ b < d then (1 : ℚ) else 0)
      = (n : ℚ) * (n - 1) * (n - 2) * (n - 3) / 24 := by
  rw [swap24, pat1]

lemma pat4 (n : ℕ) :
    S4 n (fun a b c d => if c < a ∧ a < d ∧ d < b then (1 : ℚ) else 0)
      = (n : ℚ) * (n - 1) * (n - 2) * (n - 3) / 24 := by
  rw [swapBlocks, pat3]

lemma pat0 (n : ℕ) :
    S4 n (fun a b c d => (if a < b then (1 : ℚ) else 0) * (if c < d then 1 else 0))
      = ((n : ℚ) * (n - 1) / 2) ^ 2 := by
  unfold S4
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [pairs]
  ring

lemma S4_sub (n : ℕ) (H1 H2 : ℕ → ℕ → ℕ → ℕ → ℚ) :
    S4 n (fun a b c d => H1 a b c d - H2 a b c d) = S4 n H1 - S4 n H2 := by
  unfold S4
  simp only [Finset.sum_sub_distrib]

lemma card_S4 (n : ℕ) (R : ℕ × ℕ × ℕ × ℕ → Prop) [DecidablePred R] :
    (((range n ×ˢ range n ×ˢ range n ×ˢ range n).filter R).card : ℚ)
      = S4 n (fun a b c d => if R (a, b, c, d) then 1 else 0) := by
  unfold S4
  rw [Finset.card_filter]
  push_cast
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_product]

lemma nesting_val (n : ℕ) :
    (notNesting n : ℚ) = ((n : ℚ) * (n - 1) / 2) ^ 2 - 2 * ((n : ℚ) * (n - 1) * (n - 2) * (n - 3) / 24) := by
  unfold notNesting
  rw [card_S4]
  have hpt : ∀ a b c d : ℕ,
      (if (a < b ∧ c < d ∧ ¬ (a < c ∧ c < d ∧ d < b) ∧ ¬ (c < a ∧ a < b ∧ b < d)) then (1 : ℚ) else 0)
        = (if a < b then (1 : ℚ) else 0) * (if c < d then 1 else 0)
          - (if a < c ∧ c < d ∧ d < b then (1 : ℚ) else 0)
          - (if c < a ∧ a < b ∧ b < d then (1 : ℚ) else 0) := by
    intro a b c d
    split_ifs <;> first | (exfalso; omega) | norm_num
  simp only [hpt]
  rw [S4_sub, S4_sub, pat0, pat1, pat2]
  ring

lemma crossing_val (n : ℕ) :
    (notCrossing n : ℚ) = ((n : ℚ) * (n - 1) / 2) ^ 2 - 2 * ((n : ℚ) * (n - 1) * (n - 2) * (n - 3) / 24) := by
  unfold notCrossing
  rw [card_S4]
  have hpt : ∀ a b c d : ℕ,
      (if (a < b ∧ c < d ∧ ¬ (a < c ∧ c < b ∧ b < d) ∧ ¬ (c < a ∧ a < d ∧ d < b)) then (1 : ℚ) else 0)
        = (if a < b then (1 : ℚ) else 0) * (if c < d then 1 else 0)
          - (if a < c ∧ c < b ∧ b < d then (1 : ℚ) else 0)
          - (if c < a ∧ a < d ∧ d < b then (1 : ℚ) else 0) := by
    intro a b c d
    split_ifs <;> first | (exfalso; omega) | norm_num
  simp only [hpt]
  rw [S4_sub, S4_sub, pat0, pat3, pat4]
  ring

theorem result :
    (∀ n : ℕ, 6 * notNesting n + 4 * n ^ 2 = n * (n ^ 3 + 3)) ∧
    (∀ n : ℕ, notCrossing n = notNesting n) ∧
    (∀ n : ℕ, 4 < n → (notNesting n : ℤ) = 5 * notNesting (n - 1) - 10 * notNesting (n - 2)
      + 10 * notNesting (n - 3) - 5 * notNesting (n - 4) + notNesting (n - 5)) := by
  refine ⟨fun n => ?_, fun n => ?_, fun n hn => ?_⟩
  · have h := nesting_val n
    have : ((6 * notNesting n + 4 * n ^ 2 : ℕ) : ℚ) = ((n * (n ^ 3 + 3) : ℕ) : ℚ) := by
      push_cast
      rw [h]
      ring
    exact_mod_cast this
  · have : (notCrossing n : ℚ) = (notNesting n : ℚ) := by rw [crossing_val, nesting_val]
    exact_mod_cast this
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have : ((notNesting (m + 5) : ℤ) : ℚ) = ((5 * notNesting (m + 5 - 1) - 10 * notNesting (m + 5 - 2)
        + 10 * notNesting (m + 5 - 3) - 5 * notNesting (m + 5 - 4) + notNesting (m + 5 - 5) : ℤ) : ℚ) := by
      rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
        show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
        show m + 5 - 5 = m by omega]
      push_cast
      rw [nesting_val, nesting_val, nesting_val, nesting_val, nesting_val, nesting_val]
      push_cast
      ring
    exact_mod_cast this

end OMA.A326278

theorem OMA.solution : type_of% @OMA.S_oeis_a326278.main := OMA.A326278.result
