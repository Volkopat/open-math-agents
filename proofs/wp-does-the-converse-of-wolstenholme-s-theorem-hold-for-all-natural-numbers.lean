import OMAStatements.S_wp_does_the_converse_of_wolstenholme_s_theorem_hold_for_all_natural_numbers

/-!
Disproof of the statement as formalized (statement loophole; it does NOT settle the converse of
Wolstenholme's theorem).

Wolstenholme's theorem is `C(2p-1, p-1) ≡ 1 (mod p^3)`; the open converse asks whether a composite
`n` can satisfy `C(2n-1, n-1) ≡ 1 (mod n^3)`. The formal statement instead uses the hypothesis
`n ^ 2 ∣ C(2n-1, n-1)` (which no prime satisfies), and claims every such `n > 4` is prime.
The composite number `n = 924 = 2^2 * 3 * 7 * 11` satisfies `924 ^ 2 ∣ C(1847, 923)`, checked by
kernel arithmetic through `C(1847, 923) = 1847! / (923! * 924!)`.
-/

namespace OMA.Proof_wp_wolstenholme_converse

theorem dvd924 : 924 ^ 2 ∣ Nat.choose (2 * 924 - 1) (924 - 1) := by
  rw [show 2 * 924 - 1 = 1847 from rfl, show 924 - 1 = 923 from rfl,
    Nat.choose_eq_factorial_div_factorial (by decide)]
  decide +kernel

end OMA.Proof_wp_wolstenholme_converse

theorem OMA.disproof : ¬ (type_of%
    @OMA.S_wp_does_the_converse_of_wolstenholme_s_theorem_hold_for_all_natural_numbers.main) := by
  intro H
  have h := H 924 (by decide) OMA.Proof_wp_wolstenholme_converse.dvd924
  exact absurd h (by norm_num)
