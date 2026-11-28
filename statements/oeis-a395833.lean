import Mathlib.Data.Fintype.Fin
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

namespace OMA.S_oeis_a395833

/-- The sequence `A395833`: unique integer sequence with `a(0) = 1`, `a(1) = 1`, whose generating
function `A(x) = ∑ a(k) x^k` satisfies `[x^n] A(x / A(x)^(2*n - 1)) = 0` for all `n > 1`.
Equivalently, `a(n) = - ∑_{k=1}^{n-1} a(k) * [x^{n-k}] A(x)^{-(2*n - 1)*k}` for `n ≥ 2`. -/
noncomputable def A395833 : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 =>
    let Atrunc : PowerSeries ℤ :=
      PowerSeries.mk fun j => if _ : j < n + 2 then A395833 j else 0
    let B : PowerSeries ℤ := Ring.inverse Atrunc
    (-(∑ k : Fin (n + 1),
        A395833 (k.1 + 1) * PowerSeries.coeff (n + 1 - k.1) (B ^ ((2 * (n + 2) - 1) * (k.1 + 1)))))

/-- Conjectures (OEIS A395833):
1. `(2*n - 1)` divides `A395833(n)` for all `n ≥ 1`.
2. `A395833(n) ≡ 0 (mod 3)` for all `n ≥ 2`. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ((2 * n - 1 : ℕ) : ℤ) ∣ A395833 n) ∧
    (∀ n : ℕ, 2 ≤ n → (3 : ℤ) ∣ A395833 n) := by
  sorry

end OMA.S_oeis_a395833
