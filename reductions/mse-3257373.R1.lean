import OMAStatements.S_mse_3257373
import Mathlib

/-!
# Reduction of MSE 3257373: where can the floor of zeta at a negative integer be prime?

Classical slice, not progress on the conjecture. By the functional equation the values of zeta
at negative integers are `ζ(-n) = (-1)^n B_{n+1}/(n+1)`. Three classical facts settle every `n`
outside the class `n ≡ 3 (mod 4)` and the claimed exceptional value:

* `H1`, part 1: the trivial zeros, `ζ(-2k) = 0`, so the floor is `0` for even `n ≥ 2`;
* `H1`, part 2: the sign of the Bernoulli numbers, `(-1)^(k+1) B_{2k} > 0` (from Euler's
  formula for `ζ(2k) > 0`), so `ζ(-(4j+1)) = -B_{4j+2}/(4j+2) < 0` and the floor is negative;
* `H1`, part 3: `B_24 = -236364091/2730`, so `⌊ζ(-23)⌋ = ⌊236364091/65520⌋ = 3607` (prime).

`H2` is the open core: for `n ≡ 3 (mod 4)`, `n ≠ 23`, the positive value `⌊B_{n+1}/(n+1)⌋` is
never prime.
-/

namespace OMA.R_mse_3257373_R1

def H1 : Prop :=
  (∀ k : ℕ, 1 ≤ k → OMA.S_mse_3257373.floorZetaNeg (2 * k) = 0) ∧
  (∀ j : ℕ, OMA.S_mse_3257373.floorZetaNeg (4 * j + 1) < 0) ∧
  OMA.S_mse_3257373.floorZetaNeg 23 = 3607

def H2 : Prop :=
  ∀ n : ℕ, n % 4 = 3 → n ≠ 23 → ∀ p : ℕ, p.Prime →
    OMA.S_mse_3257373.floorZetaNeg n ≠ (p : ℤ)

theorem main : H1 → H2 → type_of% @OMA.S_mse_3257373.main := by
  rintro ⟨hev, hodd, h23⟩ h2 n hn
  constructor
  · rintro ⟨p, hp, hfp⟩
    by_contra hne
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have h0 := hev k (by omega)
      rw [show 2 * k = n by omega] at h0
      omega
    · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · have h0 := hodd j
        rw [show 4 * j + 1 = n by omega] at h0
        omega
      · exact h2 n (by omega) hne p hp hfp
  · rintro rfl
    exact ⟨3607, by norm_num, h23⟩

end OMA.R_mse_3257373_R1
