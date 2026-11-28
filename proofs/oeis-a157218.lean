import OMAStatements.S_oeis_a157218
import Mathlib

namespace SunPrimeCounterexample

def factors : List ℕ := [5, 7, 11, 13, 31, 17, 23, 19, 29, 73, 89, 37, 151, 109, 101, 61, 229, 71, 83, 496187, 3061, 141403, 461, 113, 2711, 79, 2143, 2027, 59, 38791, 599, 97, 227, 727, 3167, 136501, 271517, 183487, 41983, 45161, 773, 184231, 349, 251, 41, 297833, 476849, 223, 331, 157477, 2753, 103, 157, 53, 661, 421, 397, 32801, 199, 24439, 269, 566999, 2113, 197, 360907, 311, 2417, 283, 80147, 90001, 809, 131, 21019, 271, 171679, 1831, 87037, 2267, 3643, 191, 88969, 532489, 4943, 1061, 1051, 149]

lemma certificate (x : Fin 39) (y : Fin 36) (hx : 0 < x.val) (hy : 0 < y.val)
    (hm : (445466268731 - 2 ^ x.val - 7 * 2 ^ y.val) % 6 = 1) :
    factors.any (fun d => decide (1 < d ∧ d < 445466268731 - 2 ^ x.val - 7 * 2 ^ y.val ∧
      (445466268731 - 2 ^ x.val - 7 * 2 ^ y.val) % d = 0)) = true := by
  revert hx hy hm
  revert x y
  decide +kernel

lemma missing (p x y : ℕ) (hp : p.Prime) (hr : p % 6 = 1) (hx : 0 < x) (hy : 0 < y)
    (eqn : 445466268731 = p + 2 ^ x + 7 * 2 ^ y) : False := by
  have bx : x < 39 := by
    by_contra! h
    have t : 2 ^ 39 ≤ (2:ℕ) ^ x := Nat.pow_le_pow_right (by decide) h
    norm_num at t
    omega
  have by' : y < 36 := by
    by_contra! h
    have t : 2 ^ 36 ≤ (2:ℕ) ^ y := Nat.pow_le_pow_right (by decide) h
    have lo : 481036337152 ≤ 7 * 2 ^ y := by exact Nat.mul_le_mul_left 7 t
    have upper : 7 * 2 ^ y ≤ 445466268731 := eqn ▸ Nat.le_add_left _ _
    exact (by decide : ¬ 481036337152 ≤ 445466268731) (lo.trans upper)
  have recover : 445466268731 - 2 ^ x - 7 * 2 ^ y = p := by omega
  have cert := certificate ⟨x,bx⟩ ⟨y,by'⟩ hx hy (by simpa only [recover] using hr)
  change factors.any (fun d => decide (1 < d ∧ d < 445466268731 - 2 ^ x - 7 * 2 ^ y ∧
      (445466268731 - 2 ^ x - 7 * 2 ^ y) % d = 0)) = true at cert
  rw [recover,List.any_eq_true] at cert
  obtain ⟨d,_,hd⟩ := cert
  have ⟨hlo,hhi,hmod⟩ := of_decide_eq_true hd
  exact (hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hmod)).elim (by omega) (by omega)

end SunPrimeCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a157218.main) := by
  intro h
  obtain ⟨p,x,y,hp,hr,hx,hy,he⟩ := h 445466268731 ⟨222733134365,rfl⟩ (by decide)
  exact SunPrimeCounterexample.missing p x y hp hr hx hy he
