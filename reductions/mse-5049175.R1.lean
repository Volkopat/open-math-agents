import OMAStatements.S_mse_5049175
import Mathlib

/-!
# Reduction of MSE 5049175: the gcd of two Faulhaber polynomials

Classical slice, not progress on the conjecture. Write `f_n` for the Faulhaber polynomial. The
conjectured gcd is always a common divisor, by the classical divisibilities of Faulhaber and
Jacobi:

* `f_1 = x(x+1)/2` divides every `f_n` with `n ≥ 1` (roots `0` and `-1`);
* `f_2 = x(x+1)(2x+1)/6` divides `f_n` for even `n ≥ 2` (also the root `-1/2`, from the
  symmetry `B_k(1-x) = (-1)^k B_k(x)` of the Bernoulli polynomials);
* `f_3 = x^2(x+1)^2/4` divides `f_n` for odd `n ≥ 3` (double roots at `0` and `-1`, since
  `f_n' = B_n(x+1)` and the odd Bernoulli numbers vanish).

`H1` is this lower bound; `H2` is the open core: the gcd has no further common factor.
-/

namespace OMA.R_mse_5049175_R1

open Polynomial

def H1 : Prop :=
  (∀ n : ℕ, 1 ≤ n → OMA.S_mse_5049175.f 1 ∣ OMA.S_mse_5049175.f n) ∧
  (∀ n : ℕ, 2 ≤ n → Even n → OMA.S_mse_5049175.f 2 ∣ OMA.S_mse_5049175.f n) ∧
  (∀ n : ℕ, 3 ≤ n → Odd n → OMA.S_mse_5049175.f 3 ∣ OMA.S_mse_5049175.f n)

def H2 : Prop :=
  ∀ n m : ℕ, 1 < n → 1 < m → n ≠ m → ¬ (n = 9 ∧ m = 10) → ¬ (n = 10 ∧ m = 9) →
    gcd (OMA.S_mse_5049175.f n) (OMA.S_mse_5049175.f m) ∣
      (if Odd n ∧ Odd m then OMA.S_mse_5049175.f 3
        else if Even n ∧ Even m then OMA.S_mse_5049175.f 2 else OMA.S_mse_5049175.f 1)

theorem main : H1 → H2 → type_of% @OMA.S_mse_5049175.main := by
  rintro ⟨h1, h2, h3⟩ hgcd n m hn hm hnm h910 h109
  refine associated_of_dvd_dvd (hgcd n m hn hm hnm h910 h109) ?_
  split_ifs with ho he
  · obtain ⟨hon, hom⟩ := ho
    have hn3 : 3 ≤ n := by obtain ⟨k, hk⟩ := hon; omega
    have hm3 : 3 ≤ m := by obtain ⟨k, hk⟩ := hom; omega
    exact dvd_gcd (h3 n hn3 hon) (h3 m hm3 hom)
  · exact dvd_gcd (h2 n hn he.1) (h2 m hm he.2)
  · exact dvd_gcd (h1 n (by omega)) (h1 m (by omega))

end OMA.R_mse_5049175_R1
