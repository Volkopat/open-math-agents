import Mathlib

/-!
# Giuga's Conjecture on Primality

Source: https://www.openproblemgarden.org/op/giugas_conjecture_on_primality
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source (Giuga, posted 2012; cf. Borwein–Borwein–Borwein–Girgensohn, "Giuga's Conjecture on
Primality", Amer. Math. Monthly 103 (1996) 40–50): an integer n is prime if and only if

    Σ_{j=1}^{n−1} j^(n−1) ≡ −1  (mod n).

The displayed formula on the source page is the standard Giuga sum; the bibliography [BBBG] fixes
the exact form above. The conjecture is stated for n ≥ 2 (primality is a property of integers
at least 2, and the sum is over j = 1, …, n−1).
-/

namespace OMA.S_opg_giugas_conjecture_on_primality

/--
Giuga's conjecture: for n ≥ 2, n is prime if and only if the sum of j^(n−1) over
j = 1, …, n−1 is congruent to −1 modulo n.
-/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      (n.Prime ↔ (∑ j ∈ Finset.Icc 1 (n - 1), (j : ZMod n) ^ (n - 1)) = -1) := by
  sorry

end OMA.S_opg_giugas_conjecture_on_primality
