import OMAStatements.S_oeis_a397621
import Mathlib.Algebra.CharP.Lemmas

open Polynomial

namespace OMA.A397621

private noncomputable abbrev Base : (ZMod 2)[X] := 1 + X

private theorem base_pow_degree (m : ℕ) : (Base ^ m).natDegree ≤ m := by
  have hbase : Base.natDegree ≤ 1 := (natDegree_add_le _ _).trans (by simp)
  simpa using natDegree_pow_le_of_le m hbase

private theorem base_pow_constant (m : ℕ) : (Base ^ m).coeff 0 = 1 := by
  induction m with
  | zero => simp
  | succ m ih => simp [pow_succ, mul_coeff_zero, ih, Base]

private theorem base_pow_two (k : ℕ) : Base ^ (2 ^ k) = 1 + X ^ (2 ^ k) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simpa only [one_pow] using
    add_pow_char_pow (1 : (ZMod 2)[X]) (X : (ZMod 2)[X]) 2 k

end OMA.A397621

open OMA.A397621

theorem OMA.solution : type_of% @OMA.S_oeis_a397621.main := by
  intro n hn
  let M : ℕ := 2 ^ n.log2
  have hM : M ≤ n := Nat.log2_self_le hn.ne'
  have hdouble : 2 ^ (n.log2 + 1) = 2 * M := by
    rw [pow_succ, Nat.mul_comm]
  have hnupper : n < 2 * M := hdouble ▸ Nat.lt_log2_self
  have hMpos : 0 < M := Nat.two_pow_pos _
  rw [hdouble]
  let L₀ := 2 * M - n
  change IsLeast {L : ℕ | OMA.S_oeis_a397621.RecurrenceOrder n L} L₀
  refine ⟨?_, ?_⟩
  · change OMA.S_oeis_a397621.RecurrenceOrder n L₀
    refine ⟨Base ^ L₀, base_pow_constant _, base_pow_degree _, ?_⟩
    intro j hjlo hjhi
    change (Base ^ L₀ * Base ^ n).coeff j = 0
    have hexp : L₀ + n = 2 * M := by dsimp [L₀]; omega
    rw [← pow_add, hexp, ← hdouble, base_pow_two, hdouble]
    have hj0 : j ≠ 0 := by dsimp [L₀] at hjlo; omega
    have hjM : j ≠ 2 * M := by omega
    simp [coeff_one, coeff_X_pow, hj0, hjM]
  · intro L hL
    change OMA.S_oeis_a397621.RecurrenceOrder n L at hL
    apply le_of_not_gt
    intro hLsmall
    obtain ⟨Q, hQ0, hQdegree, hQ⟩ := hL
    let r := n - M
    let F := Q * Base ^ r
    have hn' : n = M + r := by dsimp [r]; omega
    have hdegree : F.natDegree < M := by
      have hFdeg : F.natDegree ≤ L + r :=
        (natDegree_mul_le).trans (Nat.add_le_add hQdegree (base_pow_degree _))
      dsimp [L₀, r] at hLsmall hFdeg
      omega
    have hF0 : F.coeff 0 = 1 := by
      simp [F, mul_coeff_zero, hQ0, base_pow_constant]
    have hprod : Q * Base ^ n = F + X ^ M * F := by
      calc
        Q * Base ^ n = Q * Base ^ (M + r) :=
          congrArg (fun m : ℕ => Q * Base ^ m) hn'
        _ = F + X ^ M * F := by
          rw [pow_add, show Base ^ M = 1 + X ^ M from base_pow_two n.log2]
          dsimp [F]
          rw [add_mul, one_mul, mul_add]
          congr 1
          ac_rfl
    have hLM : L ≤ M := by dsimp [L₀] at hLsmall; omega
    have hzero := hQ M hLM hM
    change (Q * Base ^ n).coeff M = 0 at hzero
    have hshift : (X ^ M * F).coeff M = 1 := by
      simpa using (coeff_X_pow_mul F M 0).trans hF0
    rw [hprod, coeff_add, coeff_eq_zero_of_natDegree_lt hdegree, hshift, zero_add] at hzero
    exact one_ne_zero hzero
