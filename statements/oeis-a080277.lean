import Mathlib

/-!
# A080277: Partial sums of A038712.

Source: https://oeis.org/A080277
Credit: @agchua

Formula line of A080277 (the entry is by N. J. A. Sloane, Mar 19 2003), verbatim:
  a(n) is conjectured to be asymptotic to n*log(n)/log(2). - Klaus Brockhaus, Mar 23 2003
  [See Bannister et al., 2013. - N. J. A. Sloane, Nov 26 2013]

Formalisation. A038712(n) = 2^(k+1) - 1, where k is the exponent of the highest power of 2
dividing n (the name line of A038712; k = padicValNat 2 n). A080277(n) = A038712(1) + ... +
A038712(n), offset 1. Asymptotic to n*log(n)/log(2) means that the ratio of a(n) to
n*log(n)/log(2) tends to 1.
-/

namespace OMA.S_oeis_a080277

/-- A038712(n) = 2^(k+1) - 1, where 2^k is the highest power of 2 dividing n. -/
noncomputable def A038712 (n : ℕ) : ℕ := 2 ^ (padicValNat 2 n + 1) - 1

/-- A080277(n) = A038712(1) + ... + A038712(n). -/
noncomputable def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, A038712 k

/-- a(n) is asymptotic to n*log(n)/log(2). -/
theorem main : Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n * Real.log n / Real.log 2))
    Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a080277
