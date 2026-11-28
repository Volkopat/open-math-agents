import Mathlib

/-!
# The integral numerator and divisibility conjectures for A145656

Source: https://oeis.org/A145656 and https://oeis.org/A068566
Credit: @VestigeClub

At every positive index n, the first sequence is the reduced numerator of
the genus-one polynomial evaluated at 2, namely the sum of 2^(n-d)/d over
1 ≤ d < n. The second sequence is the reduced numerator of the partial
sum of 1/(d*2^d). We reindex those finite sums with d=i+1.

Peter Bala's 2024 claim is about the numerator of a real expression.
The first conjunct makes rationality explicit and compares reduced
numerators. The second is the divisibility observation recorded in 2025
for n ≥ 2. The integral is over the real interval from zero to one.
-/

namespace OMA.S_oeis_a145656

def polynomialValue (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n-1), (2:ℚ)^(n-1-i)/((i:ℚ)+1)

def harmonicPart (k : ℕ) : ℚ :=
  ∑ i ∈ Finset.range k, 1/(((i:ℚ)+1)*2^(i+1))

noncomputable def expression (n : ℕ) : ℝ :=
  2^n*Real.log 2 - 2^(n+1)*∫ x in (0:ℝ)..1, x^(2*n-1)/(1+x^2)^n

theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ q : ℚ,
      (q:ℝ)=expression n ∧ q.num=(polynomialValue n).num) ∧
    (∀ n : ℕ, 2 ≤ n → (harmonicPart (n-1)).num ∣ (polynomialValue n).num) := by
  sorry

end OMA.S_oeis_a145656
