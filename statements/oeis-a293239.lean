import Mathlib

/-!
# Expanded derivatives of x^x

Factor out x^x and write a term as (log x)^j x^(-k). Differentiating
x^x supplies the factors 1 and log x. Differentiating the remaining
monomial supplies j (log x)^(j-1) x^(-k-1) and
-k (log x)^j x^(-k-1). The recurrence for c collects coefficients
of identical terms, including any cancellations. Each derivative increases
either exponent by at most one, so both lie in 0..n after n steps.
At n=0 the polynomial is the constant one.

The second differences start at index zero. The ordinary generating
function is stated coefficientwise after multiplying by (1-x)^2 (1-x^4).

Source: https://oeis.org/A293239
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a293239

def c : ℕ → ℕ → ℕ → ℤ
  | 0, j, k => if j = 0 ∧ k = 0 then 1 else 0
  | n+1, j, k =>
    c n j k + (if 0 < j then c n (j-1) k else 0) +
      (if 0 < k then ((j+1 : ℕ) : ℤ) * c n (j+1) (k-1) -
        ((k-1 : ℕ) : ℤ) * c n j (k-1) else 0)

def a (n : ℕ) : ℤ :=
  Int.ofNat (((Finset.range (n+1) ×ˢ Finset.range (n+1)).filter
    (fun jk => c n jk.1 jk.2 ≠ 0)).card)

def secondDiff (n : ℕ) : ℤ := a (n+2) - 2*a (n+1) + a n

def expectedDiff (n : ℕ) : ℤ :=
  if n < 8 then ([1,1,1,0,2,1,0,1] : List ℤ).getD n 0
  else ([2,1,1,0] : List ℤ).getD ((n-8)%4) 0

def lag (n d : ℕ) : ℤ := if d ≤ n then a (n-d) else 0

def numerator (n : ℕ) : ℤ :=
  ([1,0,1,1,0,0,1,0,-1,1,0,0,1,-1] : List ℤ).getD n 0

theorem main :
    (∀ n : ℕ, secondDiff n = expectedDiff n) ∧
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ))
      (fun n : ℕ => (n : ℝ)^2 / 2) ∧
    (∀ n : ℕ, lag n 0 - 2*lag n 1 + lag n 2 - lag n 4 + 2*lag n 5 - lag n 6 =
      numerator n) ∧
    (∀ n : ℕ, 7 < n → (a n : ℂ) = (5 + (-1 : ℂ)^n +
      (1-Complex.I)*(-Complex.I)^n + (1+Complex.I)*Complex.I^n +
      2*(n : ℂ) + 4*(n : ℂ)^2) / 8) ∧
    (∀ n : ℕ, 6 < n → a n = 2*a (n-1) - a (n-2) + a (n-4) -
      2*a (n-5) + a (n-6)) := by
  sorry

end OMA.S_oeis_a293239
