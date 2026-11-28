import OMAStatements.S_oeis_a242533
import Mathlib

/-!
# A242533: no "coprime difference/sum" cycles of odd length

If `|a - b|` and `a + b` are coprime then `a + b` is odd (otherwise both are even), so adjacent
entries of a valid cycle have opposite parity.  Going once around a cycle of odd length `m`
the parity would have to flip `m` times and come back to itself, which is impossible.  So for
odd `m` there is no valid cycle at all, and the number of equivalence classes is `0`.
-/

namespace OMA.S_oeis_a242533

/-- Adjacent entries of a valid cycle have odd sum. -/
lemma adj_odd {m : ℕ} {σ : Equiv.Perm (Fin m)} (h : IsValidCycle m σ) (i j : Fin m)
    (hj : j.val = (i.val + 1) % m) : ((σ i).val + (σ j).val) % 2 = 1 := by
  have hj' : j = ⟨(i.val + 1) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (Fin.pos i).ne')⟩ :=
    Fin.ext hj
  have hi := h i
  dsimp only at hi
  rw [← hj'] at hi
  by_contra hne
  have h2 : 2 ∣ Nat.gcd (Int.natAbs ((((σ i).val + 1 : ℕ) : ℤ) - (((σ j).val + 1 : ℕ) : ℤ)))
      (((σ i).val + 1) + ((σ j).val + 1)) := Nat.dvd_gcd (by omega) (by omega)
  rw [Nat.Coprime] at hi
  rw [hi] at h2
  omega

/-- There is no valid cycle of odd length. -/
lemma no_valid {m : ℕ} (hm : Odd m) (σ : Equiv.Perm (Fin m)) : ¬ IsValidCycle m σ := by
  intro h
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
  have hm0 : 0 < m := by omega
  -- walking from position `0`, the parity of the entry at position `n` is shifted by `n`
  have walk : ∀ n (hn : n < m), ((σ ⟨n, hn⟩).val + n) % 2 = (σ ⟨0, hm0⟩).val % 2 := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 := adj_odd h ⟨n, by omega⟩ ⟨n + 1, hn⟩ (Nat.mod_eq_of_lt hn).symm
      omega
  -- closing the cycle from position `m - 1` back to position `0`
  have hlast := walk (m - 1) (by omega)
  have hclose := adj_odd h ⟨m - 1, by omega⟩ ⟨0, hm0⟩
    (by simp [Nat.sub_add_cancel hm0])
  omega

end OMA.S_oeis_a242533

open OMA.S_oeis_a242533 in
theorem OMA.solution : type_of% @OMA.S_oeis_a242533.main := by
  intro m hm
  have : IsEmpty {σ : Equiv.Perm (Fin m) // IsValidCycle m σ} :=
    ⟨fun x => no_valid hm x.1 x.2⟩
  unfold NPC
  simp
