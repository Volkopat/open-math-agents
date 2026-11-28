import Mathlib

/-!
# Two arrays for integral equations on exponential generating functions

Source: Mikhail Kurkov, https://mathoverflow.net/questions/475505 (CC BY-SA 4.0).
Credit: @connoranderson.

Both array indices below start at zero, so row n and column k represent the
source's T(n+1,k+1). Its two recurrences use the parameter s=0 and s=q.
Primitives have zero constant term. The normalized series are units, which
allows integral parameters p and q, including negative powers.
-/

namespace OMA.S_mo_475505
open PowerSeries
noncomputable section
abbrev PS := PowerSeries ℚ

def primitive (f : PS) : PS := mk (fun | 0 => 0 | n+1 => coeff n f / (n+1:ℚ))

def row (p q s : ℤ) : ℕ → ℕ → ℤ
  | 0, k => if k=0 then 1 else 0
  | n+1, 0 => row p q s n 0
  | n+1, k+1 => (1+q*(k+1))*row p q s n (k+1) +
      p*((n:ℤ)+1+(s-2)*k)*row p q s n k

theorem main : ∀ (p q : ℤ) (A B : PSˣ),
    constantCoeff (A:PS)=1 → constantCoeff (B:PS)=1 →
    (A:PS) = (exp ℚ).subst (X+(p:PS)*primitive (primitive (↑(A^q):PS))) →
    (B:PS) = (1+primitive (B:PS))*(1+(p:PS)*primitive (↑(B^q):PS)) →
    ∀ n : ℕ,
      (∑ k ∈ Finset.range (n+1), (row p q 0 n k:ℚ)) =
        ((n+1).factorial:ℚ)*coeff (n+1) (A:PS) ∧
      (∑ k ∈ Finset.range (n+1), (row p q q n k:ℚ)) =
        (n.factorial:ℚ)*coeff n (B:PS) := by
  sorry

end
end OMA.S_mo_475505
