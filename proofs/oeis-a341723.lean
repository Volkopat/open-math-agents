import OMAStatements.S_oeis_a341723
import Mathlib

/-!
# a341723: divisibility of the triangle entries by `p` and by `2 ^ m`

Each entry is a binomial coefficient times an integer, so only the binomial matters.

* For a prime `p` and `0 < k < p`, `p ∣ C(p, k)`.
* For odd `k` with `0 < k < 2 ^ m`: `2 ^ m · C(2 ^ m - 1, k - 1) = C(2 ^ m, k) · k`, and `k` is
  coprime to `2 ^ m`, hence `2 ^ m ∣ C(2 ^ m, k)`.
-/

namespace OMA.S_oeis_a341723

/-- `2 ^ m` divides `C(2 ^ m, k)` for odd `k`. -/
lemma two_pow_dvd_choose (m k : ℕ) (hk : 0 < k) (hodd : Odd k) : 2 ^ m ∣ Nat.choose (2 ^ m) k := by
  have hpos : 0 < 2 ^ m := by positivity
  have h := Nat.add_one_mul_choose_eq (2 ^ m - 1) (k - 1)
  rw [Nat.sub_add_cancel hpos, Nat.sub_add_cancel hk] at h
  have hcop : Nat.Coprime (2 ^ m) k := Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hodd)
  exact hcop.dvd_of_dvd_mul_right ⟨_, h.symm⟩

end OMA.S_oeis_a341723

open OMA.S_oeis_a341723 in
theorem OMA.solution : type_of% @OMA.S_oeis_a341723.main := by
  refine ⟨fun p k hp hk hkp => ?_, fun m k hk _ hodd => ?_⟩
  · have h : (p : ℤ) ∣ (Nat.choose p k : ℤ) :=
      Int.natCast_dvd_natCast.mpr (hp.dvd_choose_self hk.ne' hkp)
    unfold a341723
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _
  · have h : ((2 ^ m : ℕ) : ℤ) ∣ (Nat.choose (2 ^ m) k : ℤ) :=
      Int.natCast_dvd_natCast.mpr (two_pow_dvd_choose m k hk hodd)
    unfold a341723
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _
