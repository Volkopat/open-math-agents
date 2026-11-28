import OMAStatements.S_oeis_a337818
import Mathlib.Tactic

namespace A337818
open OMA.S_oeis_a337818

-- Repeated squaring uses only small residues, even for the large witness.
private def powMod (m : ℕ) : (e : ℕ) → ℕ
  | 0 => 1 % m
  | e + 1 =>
      let r := powMod m ((e+1)/2)
      ((if (e+1)%2 = 0 then 1 else 2) * (r*r)) % m
termination_by e => e
decreasing_by omega

private lemma powMod_sound (m e : ℕ) : powMod m e ≡ 2^e [MOD m] := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    cases e with
    | zero => simpa [powMod] using Nat.mod_modEq 1 m
    | succ e =>
      have hr := ih ((e+1)/2) (by omega)
      have hbit : (if (e+1)%2 = 0 then 1 else 2 : ℕ) = 2^((e+1)%2) := by
        rcases Nat.mod_two_eq_zero_or_one (e+1) with h | h <;> simp [h]
      rw [powMod, hbit]
      have hsplit : 2 ^ ((e+1)%2) * (2^((e+1)/2) * 2^((e+1)/2)) = (2:ℕ)^(e+1) := by
        rw [← pow_add, ← pow_add]
        congr 1
        have hs := Nat.mod_add_div (e+1) 2
        omega
      rw [← hsplit]
      exact (Nat.mod_modEq _ _).trans ((Nat.ModEq.refl _).mul (hr.mul hr))

private lemma certified_term (k : ℕ) (hk : 3 ≤ k) (ho : Odd k)
    (hr : (powMod (k*(k-1)/2) ((k-1)/2) + 1) % (k*(k-1)/2) = 0) : IsTerm k := by
  refine ⟨hk, ho, Nat.modEq_zero_iff_dvd.mp ?_⟩
  have h := (powMod_sound (k*(k-1)/2) ((k-1)/2)).add_right 1
  exact h.symm.trans (by simpa [Nat.ModEq] using hr)

end A337818

open OMA.S_oeis_a337818 A337818 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a337818.main) := by
  intro h
  have hb : IsTerm 48269073907 := certified_term _ (by decide) (by decide) (by decide +kernel)
  let smaller : Finset ℕ := {3, 19, 163, 1459, 370387}
  have hsub : smaller ⊆ (Finset.range 48269073907).filter (fun j =>
      3 ≤ j ∧ Odd j ∧ (j*(j-1)/2) ∣ (2^((j-1)/2)+1)) := by
    intro j hj
    simp only [smaller, Finset.mem_insert, Finset.mem_singleton] at hj
    apply Finset.mem_filter.mpr
    rcases hj with rfl | rfl | rfl | rfl | rfl
    all_goals
      exact ⟨Finset.mem_range.mpr (by decide),
        certified_term _ (by decide) (by decide) (by decide +kernel)⟩
  have hcard : smaller.card = 5 := by decide
  have hind := Finset.card_le_card hsub
  rw [hcard] at hind
  exact (by decide : ¬ (48269073907 : ℕ) % 162 = 1) (h _ hb hind)
