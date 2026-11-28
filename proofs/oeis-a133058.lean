import OMAStatements.S_oeis_a133058

-- Problem: A133058 (Fly straight, dammit): the loop (1, x, 2x, 2) from index 638.
-- Credit: @a5teri5k (the owner of the agent is credited as the solver)

namespace OMA.A133058

open OMA.S_oeis_a133058

lemma step (n : ℕ) : a133058 (n + 2) = aStep133058 (a133058 (n + 1)) (n + 2) := rfl

lemma base : a133058 638 = 1 := by
  set_option maxRecDepth 100000 in decide

lemma s1 (s : ℕ) (h : a133058 (638 + 4 * s) = 1) : a133058 (639 + 4 * s) = 641 + 4 * s := by
  rw [show 639 + 4 * s = 637 + 4 * s + 2 by omega, step, show 637 + 4 * s + 1 = 638 + 4 * s by omega, h]
  simp [aStep133058]
  omega

lemma s2 (s : ℕ) (h : a133058 (639 + 4 * s) = 641 + 4 * s) :
    a133058 (640 + 4 * s) = 2 * (641 + 4 * s) := by
  rw [show 640 + 4 * s = 638 + 4 * s + 2 by omega, step, show 638 + 4 * s + 1 = 639 + 4 * s by omega, h]
  have : Nat.gcd (641 + 4 * s) (638 + 4 * s + 2) = 1 := by
    rw [show 641 + 4 * s = 1 + (638 + 4 * s + 2) by omega, Nat.gcd_add_self_left]; simp
  simp only [aStep133058, this, if_true]
  omega

lemma s3 (s : ℕ) (h : a133058 (640 + 4 * s) = 2 * (641 + 4 * s)) : a133058 (641 + 4 * s) = 2 := by
  rw [show 641 + 4 * s = 639 + 4 * s + 2 by omega, step, show 639 + 4 * s + 1 = 640 + 4 * s by omega, h]
  have hg : Nat.gcd (2 * (641 + 4 * s)) (639 + 4 * s + 2) = 641 + 4 * s := by
    rw [show 639 + 4 * s + 2 = 641 + 4 * s by omega]; exact Nat.gcd_mul_left_left _ _
  simp only [aStep133058, hg]
  rw [if_neg (by omega), Nat.mul_div_cancel _ (by omega)]

lemma s0 (s : ℕ) (h : a133058 (641 + 4 * s) = 2) : a133058 (638 + 4 * (s + 1)) = 1 := by
  rw [show 638 + 4 * (s + 1) = 640 + 4 * s + 2 by omega, step, show 640 + 4 * s + 1 = 641 + 4 * s by omega, h]
  have hg : Nat.gcd 2 (640 + 4 * s + 2) = 2 := Nat.gcd_eq_left ⟨321 + 2 * s, by omega⟩
  simp only [aStep133058, hg]
  simp

lemma ones (t : ℕ) : a133058 (638 + 4 * t) = 1 := by
  induction t with
  | zero => exact base
  | succ t ih => exact s0 t (s3 t (s2 t (s1 t ih)))

end OMA.A133058

theorem OMA.solution : type_of% @OMA.S_oeis_a133058.main := fun t =>
  ⟨OMA.A133058.ones t, OMA.A133058.s1 t (OMA.A133058.ones t),
    OMA.A133058.s2 t (OMA.A133058.s1 t (OMA.A133058.ones t)),
    OMA.A133058.s3 t (OMA.A133058.s2 t (OMA.A133058.s1 t (OMA.A133058.ones t)))⟩
