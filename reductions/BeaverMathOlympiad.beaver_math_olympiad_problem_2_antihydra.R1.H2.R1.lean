import OMAReductions.R_BeaverMathOlympiad_beaver_math_olympiad_problem_2_antihydra_R1

namespace OMA.R_BeaverMathOlympiad_beaver_math_olympiad_problem_2_antihydra_R1_H2_R1

private theorem even_pair_residue {a : Nat → Nat}
    (ha : ∀ n, a (n + 1) = 3 * a n / 2) (n : Nat) :
    a n % 4 = 0 ↔ a n % 2 = 0 ∧ a (n + 1) % 2 = 0 := by
  rw [ha n]
  omega

private theorem even_odd_even_residue {a : Nat → Nat}
    (ha : ∀ n, a (n + 1) = 3 * a n / 2) (n : Nat) :
    a n % 8 = 2 ↔ a n % 2 = 0 ∧ a (n + 1) % 2 ≠ 0 ∧ a (n + 2) % 2 = 0 := by
  rw [show n + 2 = (n + 1) + 1 by omega, ha (n + 1), ha n]
  omega

private theorem odd_triple_residue {a : Nat → Nat}
    (ha : ∀ n, a (n + 1) = 3 * a n / 2) (n : Nat) :
    a n % 8 = 1 ↔ a n % 2 ≠ 0 ∧ a (n + 1) % 2 ≠ 0 ∧ a (n + 2) % 2 ≠ 0 := by
  rw [show n + 2 = (n + 1) + 1 by omega, ha (n + 1), ha n]
  omega

private theorem count_range_succ (f : Nat → Bool) (n : Nat) :
    (List.range (n + 1)).countP f = (List.range n).countP f + (if f n then 1 else 0) := by
  rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil, Nat.zero_add]

/-- The reserve is the unused credit on the last even term, up to two units. -/
private theorem credit_decomposition {a : Nat → Nat} {b : Nat → Int}
    (a₀ : a 0 = 8) (ha : ∀ n, a (n + 1) = 3 * a n / 2) (b₀ : b 0 = 0)
    (hb : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1)
    (k : Nat) :
    b (k + 2) = 2 * ((List.range (k + 1)).countP (fun i => a i % 4 == 0) : Int) +
      ((List.range k).countP (fun i => a i % 8 == 2) : Int) -
      ((List.range k).countP (fun i => a i % 8 == 1) : Int) +
      (if a (k + 1) % 2 = 0 then 2 else if a k % 2 = 0 then 1 else 0) := by
  let P (j : Nat) := (List.range j).countP (fun i => a i % 4 == 0)
  let S (j : Nat) := (List.range j).countP (fun i => a i % 8 == 2)
  let Q (j : Nat) := (List.range j).countP (fun i => a i % 8 == 1)
  let reserve (j : Nat) : Int :=
    if a (j + 1) % 2 = 0 then 2 else if a j % 2 = 0 then 1 else 0
  have hP (j : Nat) :
      P (j + 1) = P j + (if a j % 2 = 0 ∧ a (j + 1) % 2 = 0 then 1 else 0) := by
    unfold P
    rw [count_range_succ]
    simp only [beq_iff_eq, even_pair_residue ha j]
  have hS (j : Nat) :
      S (j + 1) = S j + (if a j % 2 = 0 ∧ a (j + 1) % 2 ≠ 0 ∧ a (j + 2) % 2 = 0 then 1 else 0) := by
    unfold S
    rw [count_range_succ]
    simp only [beq_iff_eq, even_odd_even_residue ha j]
  have hQ (j : Nat) :
      Q (j + 1) = Q j + (if a j % 2 ≠ 0 ∧ a (j + 1) % 2 ≠ 0 ∧ a (j + 2) % 2 ≠ 0 then 1 else 0) := by
    unfold Q
    rw [count_range_succ]
    simp only [beq_iff_eq, odd_triple_residue ha j]
  change b (k + 2) = 2 * (P (k + 1) : Int) + (S k : Int) - (Q k : Int) + reserve k
  induction k with
  | zero =>
    have a₁ : a 1 = 12 := by rw [show (1 : Nat) = 0 + 1 by rfl, ha 0, a₀]
    have b₁ : b 1 = 2 := by rw [show (1 : Nat) = 0 + 1 by rfl, hb 0, a₀, b₀]; decide
    have b₂ : b 2 = 4 := by rw [show (2 : Nat) = 1 + 1 by rfl, hb 1, a₁, b₁]; decide
    simp [P, S, Q, reserve, a₀, a₁, b₂, List.range_succ]
  | succ j ih =>
    change b ((j + 2) + 1) =
      2 * (P ((j + 1) + 1) : Int) + (S (j + 1) : Int) - (Q (j + 1) : Int) + reserve (j + 1)
    rw [hP (j + 1), hS j, hQ j, hb (j + 2)]
    unfold reserve at ih ⊢
    by_cases h₀ : a j % 2 = 0 <;> by_cases h₁ : a (j + 1) % 2 = 0 <;>
      by_cases h₂ : a (j + 2) % 2 = 0 <;> simp [h₀, h₁, h₂] at ih ⊢ <;> omega

/-- The combined credit from even-even and even-odd-even occurrences is at
least one quarter of the prefix length. -/
def H1 : Prop :=
  ∀ (a : Nat → Nat), a 0 = 8 → (∀ n, a (n + 1) = 3 * a n / 2) →
    ∀ n, 100000 < n → n ≤ 4 * (2 * (List.range (n - 1)).countP (fun i => a i % 4 == 0) +
      (List.range (n - 2)).countP (fun i => a i % 8 == 2))

/-- Sufficient upper frequency for starts of completed odd-odd-odd triples. -/
def H2 : Prop :=
  ∀ (a : Nat → Nat), a 0 = 8 → (∀ n, a (n + 1) = 3 * a n / 2) →
    ∀ n, 100000 < n → 4 * (List.range (n - 2)).countP (fun i => a i % 8 == 1) ≤ n

theorem main : H1 → H2 → OMA.R_BeaverMathOlympiad_beaver_math_olympiad_problem_2_antihydra_R1.H2 := by
  intro hPair hTriple a b a₀ ha b₀ hb n hn
  have hPairCount := hPair a a₀ ha n hn
  have hTripleCount := hTriple a a₀ ha n hn
  let k := n - 2
  have hk : k + 2 = n := by omega
  have hp : k + 1 = n - 1 := by omega
  have h := credit_decomposition a₀ ha b₀ hb k
  rw [hp, hk] at h
  dsimp only [k] at h
  have hReserve : (0 : Int) ≤
      (if a (n - 1) % 2 = 0 then 2 else if a (n - 2) % 2 = 0 then 1 else 0) := by
    split <;> (try split) <;> omega
  omega

end OMA.R_BeaverMathOlympiad_beaver_math_olympiad_problem_2_antihydra_R1_H2_R1
