import Mathlib

/-!
# Expected minimum Hamming distance with overlaps

Source: https://mathoverflow.net/questions/128755
Credit: @LDJAI

The two words are independent and their bits are fair. The first `n + k - 1`
text bits suffice, so expectation is a uniform finite average. We use
zero-based indices and assume `0 < k` for the minimum to be defined.
The theorem gives an explicit answer via the signed even-subgraph formula.
The motivating limit in the post is not part of the formula question;
the printed `k → 0` is understood as `k → ∞`.
-/

namespace OMA.S_mo_128755

open scoped BigOperators

def windowWeight {n m : ℕ} (a : Fin n → Bool) (b : Fin m → Bool)
    (i : ℕ) : ℕ :=
  (Finset.univ.filter (fun j : Fin n =>
    a j ≠ (if h : i + j.val < m then b ⟨i + j.val, h⟩ else false))).card

def minWindowWeight {n m : ℕ} (k : ℕ) (a : Fin n → Bool)
    (b : Fin m → Bool) : ℕ :=
  (List.range k).foldl (fun acc i => min acc (windowWeight a b i)) n

def expectedMin (n k : ℕ) : ℚ :=
  (∑ a : Fin n → Bool, ∑ b : Fin (n + k - 1) → Bool,
    (minWindowWeight k a b : ℚ)) / (2 : ℚ) ^ (n + (n + k - 1))

/-- The coefficient tail for a window with `h` selected edges. -/
def signedTail (n r h : ℕ) : ℚ :=
  if h = 0 then
    ∑ d ∈ Finset.Icc r n, (n.choose d : ℚ)
  else
    -(∑ j ∈ Finset.range r,
      (-1 : ℚ) ^ j * ((h - 1).choose j : ℚ) *
        ((n - h).choose (r - 1 - j) : ℚ))

/-- An edge `(i,j)` joins pattern bit `j` to text bit `i+j`. -/
noncomputable def evenEdgeSets (n k : ℕ) : Finset (Finset (Fin k × Fin n)) := by
  classical
  exact (Finset.univ : Finset (Fin k × Fin n)).powerset.filter (fun e =>
    (∀ j : Fin n, (e.filter (fun p => p.2 = j)).card % 2 = 0) ∧
    (∀ u : Fin (n + k - 1),
      (e.filter (fun p => p.1.val + p.2.val = u.val)).card % 2 = 0))

noncomputable def exactFormula (n k : ℕ) : ℚ :=
  (∑ r ∈ Finset.Icc 1 n, ∑ e ∈ evenEdgeSets n k, ∏ i : Fin k,
    signedTail n r (e.filter (fun p => p.1 = i)).card) /
    (2 : ℚ) ^ (n * k)

theorem main : ∀ n k : ℕ, 0 < k → expectedMin n k = exactFormula n k := by
  sorry

end OMA.S_mo_128755
