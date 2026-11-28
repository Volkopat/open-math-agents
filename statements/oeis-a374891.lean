import Mathlib

/-!
# A374891: Obverse convolution (1)**A000984; see Comments.

Source: https://oeis.org/A374891
Credit: @agchua

Formula line of A374891 (entry by Clark Kimberling, Jul 31 2024):
  a(n+1) = a(n)*A244174(n+1) for n>=0 (conjectured) = a(n)*A323230(n+2) for n>=0 (conjectured).
Offset 0. Both conjectured identities are stated, for all n >= 0, as printed.

Definitions:
* The obverse convolution s**t (A374848) is u(n) = Product_{k=0..n} (s(k) + t(n-k)); here s = A000012
  (all ones) and t = A000984, t(m) = binomial(2m, m), as in the Mathematica program of the entry:
  a(n) = Product_{k=0..n} (1 + binomial(2(n-k), n-k)). This gives all 13 listed terms.
* A244174 (offset 0), by its name: the number of compositions of 3n in which the minimal multiplicity
  of parts equals n, that is, every part that occurs has multiplicity at least n and some part has
  multiplicity exactly n. A composition of m is Mathlib's Composition m (an ordered list of positive
  parts with sum m). The listed a(0) = 1 is kept as a separate case; the conjecture uses only
  indices n + 1 >= 1, and the count gives the listed 3, 7, 21, 71, 253, 925 for n = 1..6.
* A323230 (offset 0), by its name: a(n) = binomial(2(n - 1), n - 1) + 1, with the listed a(0) = 1;
  the conjecture uses only indices n + 2 >= 2.
-/

namespace OMA.S_oeis_a374891

/-- A374891: a(n) = Product_{k=0..n} (1 + binomial(2(n-k), n-k)). -/
def a (n : ℕ) : ℕ := ∏ k ∈ Finset.range (n + 1), (1 + Nat.choose (2 * (n - k)) (n - k))

/-- A244174: the number of compositions of 3n in which the minimal multiplicity of parts
equals n (a(0) = 1 as listed). -/
noncomputable def A244174 (n : ℕ) : ℕ :=
  if n = 0 then 1 else
    (Finset.univ.filter (fun c : Composition (3 * n) =>
      (∀ p ∈ c.blocks, n ≤ c.blocks.count p) ∧ ∃ p ∈ c.blocks, c.blocks.count p = n)).card

/-- A323230: a(n) = binomial(2(n - 1), n - 1) + 1 (a(0) = 1 as listed). -/
def A323230 (n : ℕ) : ℕ := if n = 0 then 1 else Nat.choose (2 * (n - 1)) (n - 1) + 1

/-- The conjecture: a(n+1) = a(n)*A244174(n+1) and a(n+1) = a(n)*A323230(n+2) for n >= 0. -/
theorem main : ∀ n : ℕ, a (n + 1) = a n * A244174 (n + 1) ∧ a (n + 1) = a n * A323230 (n + 2) := by
  sorry

end OMA.S_oeis_a374891
