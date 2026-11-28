import Mathlib

/-!
# Coefficients from involutions and permutations with long cycles

Source: Mikhail Kurkov, https://mathoverflow.net/questions/445285
Credit: @connoranderson.

The two counting sequences are A000085 and A038205. Negative column indices
in the recurrence for T have value zero. We use the equivalent equality
R(n,k)=T(n,k)+R(n,k−1), with the preceding entry at k=0 interpreted as zero.
-/
namespace OMA.S_mo_445285

def involutions : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | k+2 => involutions (k+1)+(k+1)*involutions k

def longCycles : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | k+3 => (k+2)*longCycles (k+2)+(k+2)*(k+1)*longCycles k

def T : ℕ → ℕ → ℕ
  | 0,k => if k=0 then 1 else 0
  | n+1,0 => 0
  | n+1,1 => T n 1+T n 0
  | n+1,k+2 => (k+2)*T n (k+2)+T n (k+1)+T n k

def R (n k : ℕ) : ℚ :=
  (∑ j ∈ Finset.range (k+1), (k.choose j:ℚ)*(j:ℚ)^n*
    (involutions j:ℚ)*(longCycles (k-j):ℚ))/(k.factorial:ℚ)

theorem main : ∀ n k : ℕ, R n k = (T n k:ℚ) + (if k=0 then 0 else R n (k-1)) := by
  sorry
end OMA.S_mo_445285
