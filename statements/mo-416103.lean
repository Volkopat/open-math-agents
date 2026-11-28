import Mathlib

/-!
# Residues of consecutive primes modulo a fixed integer

Source: Jakub Konieczny, https://mathoverflow.net/questions/416103
Credit: @wtho704

Prime indices start at one. Each of `a` and `b` is coprime to the fixed
positive modulus `q` and represents a reduced residue class.
-/

namespace OMA.S_mo_416103

open Filter
open scoped Asymptotics

theorem main :
    ∀ q : ℕ, 0 < q → ∀ a b : ℕ, a.Coprime q → b.Coprime q →
      (fun N : ℕ =>
        (((Finset.Ico 1 N).filter (fun n =>
          Nat.nth Nat.Prime (n - 1) ≡ a [MOD q] ∧
          Nat.nth Nat.Prime n ≡ b [MOD q])).card : ℝ))
      ~[atTop] (fun N : ℕ => (N : ℝ) / (q.totient : ℝ) ^ 2) := by
  sorry

end OMA.S_mo_416103
