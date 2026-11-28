import Mathlib

/-!
# A270236: occurrences of p in the restricted growth functions of length n
Source: https://oeis.org/A270236 (conjectures in the entry of R. J. Mathar, Mar 13 2016)

T(n,p) (n >= 1, 1 <= p <= n) is the number of occurrences of the value p in all restricted growth
functions (RGFs) of length n, where an RGF of length n is a sequence f(1), ..., f(n) with f(1) = 1
and f(j) <= 1 + max_{i<j} f(i) (all values positive). RGFs are represented as lists; the condition
at index i (0-based) reads 1 <= l[i] <= 1 + max(l[0..i-1]), with the max of an empty prefix equal to 0,
which forces l[0] = 1. Every entry of an RGF of length n is at most n, so the RGFs of length n are
exactly the lists of length n with entries in 0..n satisfying the condition.

Conjectures (both formalized):
* T(n, n-1) = 2 + n*(n-1)/2 for n > 1;
* T(n+1, n-1) = 2 + n*(n+1)*(3*n^2-5*n+26)/24 for n > 1 (stated over the rationals).
-/

namespace OMA.S_oeis_a270236

/-- The restricted growth condition. -/
def IsRGF (l : List ℕ) : Prop :=
  ∀ i : Fin l.length, 1 ≤ l[i] ∧ l[i] ≤ (l.take i).foldr max 0 + 1

instance (l : List ℕ) : Decidable (IsRGF l) := by unfold IsRGF; infer_instance

/-- The RGFs of length n. -/
def rgfs (n : ℕ) : Finset (List ℕ) :=
  ((Fintype.piFinset fun _ : Fin n => Finset.range (n + 1)).image fun f => List.ofFn f).filter IsRGF

/-- T(n,p): number of occurrences of p in all RGFs of length n. -/
def T (n p : ℕ) : ℕ := ∑ l ∈ rgfs n, l.count p

theorem main :
    (∀ n : ℕ, 1 < n → T n (n - 1) = 2 + n * (n - 1) / 2) ∧
    (∀ n : ℕ, 1 < n → (T (n + 1) (n - 1) : ℚ) =
      2 + (n : ℚ) * (n + 1) * (3 * (n : ℚ) ^ 2 - 5 * n + 26) / 24) := by
  sorry

end OMA.S_oeis_a270236
