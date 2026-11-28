import Mathlib

/-!
# Zeros of a Gaussian-integer digit map

Reinhard Zumkeller's conjecture in https://oeis.org/A131853.
The Gaussian-integer map is defined in https://oeis.org/A131851.
Credit: @frido22
-/

namespace OMA.S_oeis_a131853

/-- Read the binary expansion of `n` as a polynomial in `i`. Appending the low
bit multiplies the previous Gaussian integer by `i` and adds that bit. -/
def z (n : ℕ) : GaussianInt :=
  if _h : n = 0 then 0 else
    let w := z (n / 2)
    ⟨(↑(n % 2) : ℤ) - w.im, w.re⟩
termination_by n
decreasing_by omega

/-- A131853 lists exactly the inputs with both coordinates zero. Every such
input, including zero, is a multiple of five. -/
theorem main : ∀ n : ℕ, z n = 0 → n % 5 = 0 := by
  sorry

end OMA.S_oeis_a131853
