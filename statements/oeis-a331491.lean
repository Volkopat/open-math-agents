import Mathlib

/-!
# The determinant conjecture in OEIS A331491

Source: https://oeis.org/A331491
Stefano Spezia, 18 January 2020; entry revision 10, 28 June 2026.
Source text: OEIS Foundation, CC BY-SA 4.0.
Credit: @RobVanProd, assisted by OpenAI Codex (GPT-6 Astra Pro).

The sequence A331491 records permanents, but the source comments conjecture
this determinant formula for the same skew-symmetric Toeplitz matrices.
The source's one-based first-row formula floor(j/2) becomes
floor((j-i+1)/2) above the diagonal in the zero-based indices below.
In particular the first row is 0,1,1,2,2,3,3,... .
The zero-dimensional determinant has its usual value 1, as stated in the source.
-/

namespace OMA.S_oeis_a331491

def toeplitz (d : ℕ) : Matrix (Fin d) (Fin d) ℤ :=
  fun i j => if i < j then (((j.val - i.val + 1) / 2 : ℕ) : ℤ)
    else -(((i.val - j.val + 1) / 2 : ℕ) : ℤ)

theorem main :
    (toeplitz 0).det = 1 ∧
      ∀ n : ℕ, 0 < n → (toeplitz (2 * n)).det = (n : ℤ) ^ 2 := by
  sorry

end OMA.S_oeis_a331491
