import Mathlib

/-!
Source: https://oeis.org/A000276
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A000/A000276.seq
Credit: @Heart-galaxy

Both Mathar recurrences are recorded as proved by Roberto Blanco Gomez
on October 1, 2026. The independent exact formula is Jovovic's factorial
times (harmonic(n-2)-1). The source offset is 4, so the common domains
are n>=6 for the first recurrence and n>=7 for the second.
-/

namespace OMA.S_oeis_a000276

def a (n : ℕ) : ℚ := (Nat.factorial (n-1) : ℚ)*(harmonic (n-2)-1)

theorem main :
    (∀ n : ℕ, 6 ≤ n → (-(n:ℚ)+2)*a n+((n:ℚ)-1)*(2*(n:ℚ)-5)*a (n-1)-
      ((n:ℚ)-1)*((n:ℚ)-2)*((n:ℚ)-3)*a (n-2)=0) ∧
    (∀ n : ℕ, 7 ≤ n → a n+2*(-(n:ℚ)+2)*a (n-1)+
      ((n:ℚ)^2-6*(n:ℚ)+10)*a (n-2)+((n:ℚ)-3)*((n:ℚ)-4)*a (n-3)=0) := by
  sorry

end OMA.S_oeis_a000276
