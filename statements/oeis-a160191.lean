import Mathlib

/-!
# The Lodumo-8 transform of the Lucas sequence

The pair at n contains the consecutive Lucas numbers L(n), L(n+1).
Lodumo replaces each residue by its least unused nonnegative representative.
At the t-th occurrence, counting from zero, the representative of residue r
is therefore r + 8*t. Earlier appearances are counted strictly before n.
R. J. Mathar's conjecture relates the terms at n, n+6 and n+12.

https://oeis.org/A160191 · https://oeis.org/A000032 · https://oeis.org/transforms.txt
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a160191

def lucasPair : ℕ → ℕ × ℕ
  | 0 => (2, 1)
  | n+1 => let p := lucasPair n; (p.2, p.1 + p.2)

def residue (n : ℕ) : ℕ := (lucasPair n).1 % 8

def earlierCount (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => earlierCount r n + if residue n = r then 1 else 0

def term (n : ℕ) : ℕ := residue n + 8 * earlierCount (residue n) n

theorem main : ∀ n : ℕ, (term (n+12) : ℤ) = 2 * (term (n+6) : ℤ) - term n := by
  sorry

end OMA.S_oeis_a160191
