import Mathlib

/-!
# Integer partitions under a divisibility constraint

Source: https://mathoverflow.net/questions/315485/integer-partitions-under-divisibility-constraint

The question asks for a method finding the partitions for any input and
determining when the solution set is empty or has several members. The sorted
representative has positive parts and every earlier part properly divides each
later part. The divisor recursion below produces the entire solution set and a
count-only version. We also give a bound beyond which solutions always exist
for each positive prescribed number of parts. For lengths at least two,
we give infinitely many inputs with any prescribed lower bound on the count.
At each length the least representable sum and its unique decomposition are exact.
-/
namespace OMA.S_mo_315485

def IsPartition (n k : ℕ) (l : List ℕ) : Prop :=
  l.sum = n ∧ l.length = k ∧ (∀ a ∈ l, 0 < a) ∧
    l.Pairwise (fun a b => a < b ∧ a ∣ b)

/-- 'lo' is the least permitted first part. After dividing out the first part
the remaining ones are all strictly greater than one. -/
def partitions (lo : ℕ) : ℕ → ℕ → Finset (List ℕ)
  | 0, n => if n = 0 then {[]} else ∅
  | k+1, n =>
    (n.divisors.filter (lo ≤ ·)).biUnion fun d =>
      (partitions 2 k (n/d - 1)).image fun l => d :: l.map (d * ·)

def count (lo : ℕ) : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | k+1, n => ∑ d ∈ n.divisors.filter (lo ≤ ·), count 2 k (n/d - 1)

def cutoff : ℕ → ℕ
  | 0 => 1
  | k+1 => 2^(2*(k+1)) * (2*cutoff k+1)

theorem main :
    (∀ n k l, l ∈ partitions 1 k n ↔ IsPartition n k l) ∧
    (∀ n k, (partitions 1 k n).card = count 1 k n) ∧
    (∀ n k, cutoff k ≤ n → ∃ l, IsPartition n (k+1) l) ∧
    (∀ k b : ℕ, ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, 0 < n → M ∣ n → b ≤ count 1 (k+2) n) ∧
    (∀ k, (∀ n l, IsPartition n k l → 2^k-1 ≤ n) ∧ ∃! l, IsPartition (2^k-1) k l) := by
  sorry

end OMA.S_mo_315485
