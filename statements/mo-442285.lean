import Mathlib

/-!
# Hankel determinants of Catalan and Narayana convolutions

Source: Johann Cigler, https://mathoverflow.net/questions/442285 (CC BY-SA 4.0).
Credit: @connoranderson

The first formula concerns ordinary Catalan numbers. The remark asks for a
polynomial identity in q, equivalently an identity at every rational q. The
final edit gives the degree and leading coefficient in the neighboring size
class. We retain the printed q-integer and the signs from the source.
-/

namespace OMA.S_mo_442285

/-- The coefficient of x^t in (c(x)−1)^k. For positive k and t, the displayed
ballot number is (k/t) binom(2t,t−k) when t ≥ k, and zero otherwise. -/
def catalanConvolution (k t : ℕ) : ℚ :=
  if k = 0 then (if t = 0 then 1 else 0) else
  if t = 0 then 0 else
    (((2*t-1).choose (t+k-1) : ℕ) : ℚ) - (((2*t-1).choose (t+k) : ℕ) : ℚ)

/-- Coefficient of x^(r+1) in the Narayana generating function, with linear
coefficient 1 and quadratic coefficient 1+q. -/
def narayana (r : ℕ) (q : ℚ) : ℚ :=
  (∑ i ∈ Finset.range (r+1),
    ((r+1).choose i : ℚ) * ((r+1).choose (i+1) : ℚ) * q^i) / (r+1 : ℕ)

/-- Ordinary Cauchy convolution of k copies of the positive-degree part. -/
def narayanaConvolution : ℕ → ℕ → ℚ → ℚ
  | 0, t, _ => if t = 0 then 1 else 0
  | k+1, t, q => ∑ i ∈ Finset.range t, narayana i q * narayanaConvolution k (t-1-i) q

/-- The size-zero determinant is 1 by the empty determinant convention. -/
noncomputable def hankel (c : ℕ → ℚ) (N m : ℕ) : ℚ :=
  (Matrix.of fun i j : Fin N => c (i.val+j.val+m+1)).det

def qInt (n : ℕ) (q : ℚ) : ℚ := ∑ i ∈ Finset.range n, q^i

theorem main : ∀ k : ℕ, 0 < k →
    (∀ n m : ℕ, m ≤ k →
      hankel (catalanConvolution k) (k*n) m = (-1 : ℚ)^(k.choose 2*n) * (n+1 : ℕ)^m) ∧
    (∀ (n m : ℕ) (q : ℚ), m ≤ k →
      hankel (fun t => narayanaConvolution k t q) (k*n) m =
        (-1 : ℚ)^(k.choose 2*n) * q^(k^2*n.choose 2) * (qInt (n+1) q)^m) ∧
    (∀ m : ℕ, 2 ≤ m → m ≤ k+2 → ∃ P : Polynomial ℚ,
      (∀ n : ℕ, P.eval (n : ℚ) =
        (-1 : ℚ)^(n*k.choose 2+(k-1).choose 2) *
          hankel (catalanConvolution k) (k*n+k-1) m) ∧
      P.degree = (3*(m-1) : ℕ) ∧
      P.leadingCoeff = (-1 : ℚ)^m * bernoulli (2*m-2) /
        (2*m-2).factorial * 2^(2*m-3) * (k : ℚ)^(2*m-2)) := by
  sorry

end OMA.S_mo_442285
