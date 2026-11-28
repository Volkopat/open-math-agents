import OMAStatements.S_oeis_a129995
import Mathlib

/-!
# A129995: `(n+1)(n²+2)(n³+3)(n⁴+4) / 4!` is an integer

The numerator is a polynomial in `n`, so its residue modulo `24` only depends on `n mod 24`;
checking the `24` residues shows that it is always divisible by `24 = 4!`.
-/

namespace OMA.S_oeis_a129995

/-- The numerator is divisible by `24`. -/
lemma dvd_numerator (n : ℕ) : 24 ∣ numerator n := by
  have hn : n ≡ n % 24 [MOD 24] := (Nat.mod_modEq n 24).symm
  have h := (((hn.add_right 1).mul ((hn.pow 2).add_right 2)).mul ((hn.pow 3).add_right 3)).mul
    ((hn.pow 4).add_right 4)
  have hr : ∀ r < 24, ((r + 1) * (r ^ 2 + 2) * (r ^ 3 + 3) * (r ^ 4 + 4)) % 24 = 0 := by decide
  have h' : numerator n % 24 =
      ((n % 24 + 1) * ((n % 24) ^ 2 + 2) * ((n % 24) ^ 3 + 3) * ((n % 24) ^ 4 + 4)) % 24 := h
  exact Nat.dvd_of_mod_eq_zero (h'.trans (hr _ (Nat.mod_lt _ (by norm_num))))

end OMA.S_oeis_a129995

open OMA.S_oeis_a129995 in
theorem OMA.solution : type_of% @OMA.S_oeis_a129995.main := by
  intro n
  obtain ⟨c, hc⟩ := dvd_numerator n
  refine ⟨c, ?_⟩
  have h4 : (Nat.factorial 4 : ℚ) = 24 := by norm_num [Nat.factorial]
  unfold a
  rw [hc, h4]
  push_cast
  field_simp
