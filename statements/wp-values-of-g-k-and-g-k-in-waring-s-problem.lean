import Mathlib

/-!
# Values of g(k) and G(k) in Waring's problem

Source: https://en.wikipedia.org/wiki/Waring's_problem
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wp_values_of_g_k_and_g_k_in_waring_s_problem

-- definitions the statement needs (no sorry, no axiom)

/-- `IsSumOfPowers k s n`: `n` is a sum of at most `s` `k`-th powers of natural numbers. -/
def IsSumOfPowers (k s n : ℕ) : Prop :=
  ∃ l : List ℕ, l.length ≤ s ∧ (l.map (fun x => x ^ k)).sum = n

/-- `g k`: the minimum number `s` of `k`-th powers of naturals needed to represent
all positive integers (Waring's problem). -/
noncomputable def g (k : ℕ) : ℕ :=
  sInf { s : ℕ | ∀ n : ℕ, 0 < n → IsSumOfPowers k s n }

/-- `G k`: the least positive integer `s` such that every sufficiently large integer
(i.e. every integer greater than some constant) is a sum of at most `s` `k`-th powers. -/
noncomputable def G (k : ℕ) : ℕ :=
  sInf { s : ℕ | ∃ N : ℕ, ∀ n : ℕ, N ≤ n → IsSumOfPowers k s n }

-- The source's Euclidean divisions: 3^k = 2^k * q k + r k (0 ≤ r k < 2^k), so
-- q k = ⌊(3/2)^k⌋, and 4^k = 3^k * d k + s k (0 ≤ s k < 3^k).
def q (k : ℕ) : ℕ := 3 ^ k / 2 ^ k
def r (k : ℕ) : ℕ := 3 ^ k % 2 ^ k
def d (k : ℕ) : ℕ := 4 ^ k / 3 ^ k
def s (k : ℕ) : ℕ := 4 ^ k % 3 ^ k

theorem main :
    -- Exact values of g(k) (table: Lagrange, Wieferich-Kempner, Balasubramanian-Deshouillers-Dress,
    -- Chen-Conway, Pillai, Dickson-Pillai).
    g 1 = 1 ∧ g 2 = 4 ∧ g 3 = 9 ∧ g 4 = 19 ∧ g 5 = 37 ∧ g 6 = 73 ∧ g 7 = 143 ∧
    -- Classical lower bound (J. A. Euler, c. 1772): g(k) ≥ 2^k + q - 2.
    (∀ k ≥ 1, 2 ^ k + q k - 2 ≤ g k) ∧
    -- The formula "valid for all k" (Dickson, Pillai, Rubugunday, Niven), all three cases
    -- exactly as displayed in the source.
    (∀ k, q k + r k ≤ 2 ^ k → g k = 2 ^ k + q k - 2) ∧
    (∀ k, q k + r k > 2 ^ k → q k * d k + q k + d k = 2 ^ k → g k = 2 ^ k + q k + d k - 2) ∧
    (∀ k, q k + r k > 2 ^ k → q k * d k + q k + d k > 2 ^ k → g k = 2 ^ k + q k + d k - 3) ∧
    -- Exact values of G(k) and G(k) ≤ g(k).
    G 1 = 1 ∧ G 2 = 4 ∧ G 4 = 16 ∧
    (∀ k, G k ≤ g k) ∧
    -- Lower bounds for G(k), the four displayed cases with the source's ranges.
    (∀ r ≥ 2, 2 ^ (r + 2) ≤ G (2 ^ r)) ∧
    (∀ r, 2 ^ (r + 2) ≤ G (3 * 2 ^ r)) ∧
    (∀ p r, Nat.Prime p → 2 < p → p ^ (r + 1) ≤ G (p ^ r * (p - 1))) ∧
    (∀ p r, Nat.Prime p → 2 < p → (p ^ (r + 1) - 1) / 2 ≤ G (p ^ r * ((p - 1) / 2))) ∧
    (∀ k ≥ 2, k + 1 ≤ G k) ∧
    -- The "Bounds" table rows for G(3) through G(20).
    (4 ≤ G 3 ∧ G 3 ≤ 7) ∧ (6 ≤ G 5 ∧ G 5 ≤ 17) ∧ (9 ≤ G 6 ∧ G 6 ≤ 24) ∧
    (8 ≤ G 7 ∧ G 7 ≤ 33) ∧ (32 ≤ G 8 ∧ G 8 ≤ 42) ∧ (13 ≤ G 9 ∧ G 9 ≤ 50) ∧
    (12 ≤ G 10 ∧ G 10 ≤ 59) ∧ (12 ≤ G 11 ∧ G 11 ≤ 67) ∧ (16 ≤ G 12 ∧ G 12 ≤ 76) ∧
    (14 ≤ G 13 ∧ G 13 ≤ 84) ∧ (15 ≤ G 14 ∧ G 14 ≤ 92) ∧ (16 ≤ G 15 ∧ G 15 ≤ 100) ∧
    (64 ≤ G 16 ∧ G 16 ≤ 109) ∧ (18 ≤ G 17 ∧ G 17 ≤ 117) ∧ (27 ≤ G 18 ∧ G 18 ≤ 125) ∧
    (20 ≤ G 19 ∧ G 19 ≤ 134) ∧ (25 ≤ G 20 ∧ G 20 ≤ 142) := by
  sorry

end OMA.S_wp_values_of_g_k_and_g_k_in_waring_s_problem
