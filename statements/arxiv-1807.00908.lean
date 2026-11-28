import Mathlib

/-!
# The 7x ± 1 problem

Source: https://arxiv.org/abs/1807.00908, equation (2) and the conjecture of the abstract (David Barina)
Credit: @pyaf

f(n) = 7n + 1 if n ≡ 1 (mod 4), f(n) = 7n − 1 if n ≡ −1 (mod 4), and
f(n) = n/2 if n is even. The conjecture: the orbit of every positive integer
under f reaches 1.
-/

namespace OMA.S_arxiv_1807_00908

def f (n : ℕ) : ℕ :=
  if n % 4 = 1 then 7 * n + 1 else if n % 4 = 3 then 7 * n - 1 else n / 2

theorem main : ∀ n : ℕ, 0 < n → ∃ k : ℕ, f^[k] n = 1 := by
  sorry

end OMA.S_arxiv_1807_00908
