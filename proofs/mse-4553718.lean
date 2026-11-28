import OMAStatements.S_mse_4553718

/-!
Formal proof of the known color-restoration theorem for a perfect out-shuffle.
The modular model appears in Qiaochu Yuan's answer to MathSE question 4553718.
The half-interval argument is due to Angina Seng (17 July 2020):
https://math.stackexchange.com/a/3759624 (CC BY-SA 4.0).
-/

namespace OMA.S_mse_4553718

lemma shuffle_last_fixed {n : ℕ} (hn : 0 < n) :
    outShuffle n (2 * n - 1) = 2 * n - 1 := by
  unfold outShuffle
  rw [if_neg (by omega)]
  omega

lemma shuffle_mod {n i : ℕ} (hn : 0 < n) (hi : i < 2 * n - 1) :
    outShuffle n i = (2 * i) % (2 * n - 1) := by
  unfold outShuffle
  split_ifs with h
  · exact (Nat.mod_eq_of_lt (by omega)).symm
  · have heq : 2 * i = (2 * (i - n) + 1) + (2 * n - 1) := by omega
    have hb : 2 * (i - n) + 1 < 2 * n - 1 := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hb]

lemma shuffle_iterate_mod {n i : ℕ} (hn : 0 < n)
    (hi : i < 2 * n - 1) (k : ℕ) :
    (outShuffle n)^[k] i = (2 ^ k * i) % (2 * n - 1) := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt hi]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih,
      shuffle_mod hn (Nat.mod_lt _ (by omega))]
    simp only [Nat.mul_mod_mod, pow_succ]
    congr 1
    ring

lemma half_interval_rigidity {n a : ℕ} (hn : 2 ≤ n)
    (ha : a < 2 * n - 1)
    (h : ∀ x : ℕ, x < 2 * n - 1 →
      ((a * x) % (2 * n - 1) < n ↔ x < n)) : a = 1 := by
  have ha_small : a < n := by
    simpa [Nat.mod_eq_of_lt ha] using (h 1 (by omega)).mpr (by omega)
  have ha_pos : 0 < a := by
    by_contra hzero
    have ha_zero : a = 0 := by omega
    have hn_bad := (h n (by omega)).mp (by simp [ha_zero]; omega)
    omega
  by_contra hne
  have ha_two : 1 < a := by omega
  let x := (n - 1) / a + 1
  have hx : x < n := by
    have hdiv := Nat.div_lt_self (show 0 < n - 1 by omega) ha_two
    dsimp [x]
    omega
  have hax_lower : n ≤ a * x := by
    have hdiv : (n - 1) / a < x := by dsimp [x]; omega
    have hmul := (Nat.div_lt_iff_lt_mul ha_pos).mp hdiv
    rw [Nat.mul_comm x a] at hmul
    omega
  have hax_upper : a * x < 2 * n - 1 := by
    have hdiv := Nat.mul_div_le (n - 1) a
    dsimp [x]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hbad := (h x (by omega)).mpr hx
  rw [Nat.mod_eq_of_lt hax_upper] at hbad
  omega

lemma colorsReturn_iff_pow_eq_one {n k : ℕ} (hn : 0 < n) :
    colorsReturn n k ↔ (2 : ZMod (2 * n - 1)) ^ k = 1 := by
  have hm : 0 < 2 * n - 1 := by omega
  constructor
  · intro hreturn
    by_cases hone : n = 1
    · subst n
      change (2 : ZMod 1) ^ k = 1
      exact Subsingleton.elim _ _
    · have hn_two : 2 ≤ n := by omega
      have hresidue : 2 ^ k % (2 * n - 1) = 1 := by
        apply half_interval_rigidity hn_two (Nat.mod_lt _ hm)
        intro x hx
        have hxreturn := hreturn x (by omega)
        rw [shuffle_iterate_mod hn hx k] at hxreturn
        simpa only [Nat.mod_mul_mod] using hxreturn
      have hcast : ((2 ^ k : ℕ) : ZMod (2 * n - 1)) = (1 : ℕ) := by
        apply (ZMod.natCast_eq_natCast_iff' _ _ _).2
        simpa [Nat.mod_eq_of_lt (show 1 < 2 * n - 1 by omega)] using hresidue
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hcast
  · intro hpow i hi
    have hmod : 2 ^ k % (2 * n - 1) = 1 % (2 * n - 1) := by
      apply (ZMod.natCast_eq_natCast_iff' _ _ _).1
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hpow
    by_cases him : i < 2 * n - 1
    · rw [shuffle_iterate_mod hn him k, Nat.mul_mod, hmod,
        ← Nat.mul_mod, one_mul, Nat.mod_eq_of_lt him]
    · have hieq : i = 2 * n - 1 := by omega
      subst i
      rw [Function.iterate_fixed (shuffle_last_fixed hn) k]

end OMA.S_mse_4553718

open OMA.S_mse_4553718 in
theorem OMA.solution : type_of% @OMA.S_mse_4553718.main := by
  intro n hn
  let : NeZero (2 * n - 1) := ⟨by omega⟩
  have hodd : Odd (2 * n - 1) := by
    refine ⟨n - 1, ?_⟩
    omega
  have hunit : IsUnit (2 : ZMod (2 * n - 1)) :=
    (ZMod.isUnit_iff_coprime 2 _).mpr (Nat.coprime_two_left.mpr hodd)
  refine ⟨⟨hunit.isOfFinOrder.orderOf_pos,
    (colorsReturn_iff_pow_eq_one hn).mpr (pow_orderOf_eq_one _)⟩, ?_⟩
  intro k hk
  exact orderOf_le_of_pow_eq_one hk.1 ((colorsReturn_iff_pow_eq_one hn).mp hk.2)

