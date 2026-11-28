import OMAStatements.S_oeis_a344734
import Mathlib

-- Original proof by @caa1982.

open OMA.S_oeis_a344734

namespace OMA.P_oeis_a344734

lemma shift (q k : ℕ) : Nat.Coprime (10 * q + k) 10 ↔ Nat.Coprime k 10 := by
  rw [show 10 * q + k = k + q * 10 by ring]
  exact Nat.coprime_add_mul_right_left k 10 q

lemma count_shift (q b : ℕ) :
    Nat.count (fun k => Nat.Coprime (10 * q + k) 10) b = Nat.count (fun k => Nat.Coprime k 10) b := by
  simp only [shift]

lemma count10 (q : ℕ) : Nat.count (fun k => Nat.Coprime k 10) (10 * q) = 4 * q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 10 * (q + 1) = 10 * q + 10 by ring, Nat.count_add, ih, count_shift]
    have : Nat.count (fun k => Nat.Coprime k 10) 10 = 4 := by decide
    omega

lemma c_val (q r d : ℕ) (hd : Nat.Coprime d 10) (hr : Nat.count (fun k => Nat.Coprime k 10) d = r) :
    c (4 * q + r + 1) = 10 * q + d := by
  have hp : Nat.Coprime (10 * q + d) 10 := (shift q d).2 hd
  have hc : Nat.count (fun k => Nat.Coprime k 10) (10 * q + d) = 4 * q + r := by
    rw [Nat.count_add, count10, count_shift, hr]
  unfold c
  rw [show 4 * q + r + 1 - 1 = 4 * q + r by omega, ← hc]
  exact Nat.nth_count hp

-- In residue class r, d is the unit modulo 10 and k is its positive inverse.
private def residue : Fin 4 → ℕ := ![1, 3, 7, 9]
private def inverse : Fin 4 → ℕ := ![1, 7, 3, 9]
private def offset : Fin 4 → ℕ := ![0, 2, 2, 8]

private lemma table : ∀ r : Fin 4,
    Nat.Coprime (residue r) 10 ∧ Nat.count (Nat.Coprime · 10) (residue r) = r.val ∧
      residue r * inverse r = 10 * offset r + 1 ∧ 1 ≤ inverse r ∧ inverse r < 10 ∧
      r.val ≤ offset r := by decide

private lemma affine (q : ℕ) (r : Fin 4) (hn : 0 < 4 * q + r.val) :
    a (4 * q + r.val + 1) = inverse r * q + offset r := by
  obtain ⟨hc, hr, hd, hk, hk10, hb⟩ := table r
  unfold a
  rw [c_val q r.val _ hc hr]
  have hq : q ≤ inverse r * q := by simpa using Nat.mul_le_mul_right q hk
  have he : 10 * (inverse r * q + offset r) + 1 = (10 * q + residue r) * inverse r := by
    nlinarith
  refine IsLeast.csInf_eq ⟨⟨by omega, ⟨inverse r, he⟩⟩, ?_⟩
  rintro x ⟨_, j, hj⟩
  have hm : (10 * q + residue r) * inverse r ≡ (10 * q + residue r) * j [MOD 10] := by
    rw [← he, ← hj]
    simp [Nat.ModEq, Nat.add_mod]
  have hmod := Nat.ModEq.cancel_left_of_coprime ((shift q _).2 hc).symm hm
  change inverse r % 10 = j % 10 at hmod
  rw [Nat.mod_eq_of_lt hk10] at hmod
  have hij := hmod.trans_le (Nat.mod_le j 10)
  have := Nat.mul_le_mul_left (10 * q + residue r) hij
  omega

end OMA.P_oeis_a344734

open OMA.P_oeis_a344734 in
theorem OMA.solution : type_of% @OMA.S_oeis_a344734.main := by
  intro n hn
  obtain ⟨q, r, rfl⟩ : ∃ q : ℕ, ∃ r : Fin 4, n = 4 * q + r.val + 1 :=
    ⟨(n - 1) / 4, ⟨(n - 1) % 4, by omega⟩, by
      change n = 4 * ((n - 1) / 4) + (n - 1) % 4 + 1
      omega⟩
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by have := r.isLt; omega⟩
  have e4 : 4 * (p + 2) + r.val + 1 - 4 = 4 * (p + 1) + r.val + 1 := by omega
  have e8 : 4 * (p + 2) + r.val + 1 - 8 = 4 * p + r.val + 1 := by omega
  rw [e4, e8, affine _ _ (by omega), affine _ _ (by omega), affine _ _ (by omega)]
  push_cast
  ring
