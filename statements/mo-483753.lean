import Mathlib

/-!
# The generalized Stirling identity for binary rows

Source: Mikhail Kurkov, https://mathoverflow.net/questions/483753
Credit: @connoranderson.

The two source arrays are OEIS A358612 and A373183. We express the
conjecture as an identity of integer polynomials after multiplying by X.
Substitution of -X and the overall sign encode the alternating signs on
the ordinary coefficients of the second row polynomial.
-/
namespace OMA.S_mo_483753
open Polynomial

def weight (n : ℕ) : ℕ := n.bits.count true

def evenRow (v : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | k+2 => (k+2 : ℤ)*v (k+2) + v (k+1) -
      (evenRow v (k+1) + v (k+1))/(k+1 : ℤ)

def entries : ℕ → ℕ → ℤ :=
  Nat.binaryRec (motive := fun _ => ℕ → ℤ)
    (fun k => if k=1 ∨ k=2 then 1 else 0)
    (fun b _ v => if b then fun k => (k:ℤ)*v k + v (k-1) else evenRow v)

noncomputable def row : ℕ → ℤ[X] :=
  Nat.binaryRec (motive := fun _ => ℤ[X]) X
    (fun b _ P => if b then X*P else X*(P.comp (X+1)-P))

theorem main : ∀ n : ℕ,
    (∑ k ∈ Finset.range (weight n+3), C (entries n k) * descPochhammer ℤ k) =
      C ((-1 : ℤ)^(weight n+1)) * X * (row n).comp (-X) := by
  sorry
end OMA.S_mo_483753
