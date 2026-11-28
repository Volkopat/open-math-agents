import OMAStatements.S_oeis_a374105
import Mathlib

private def q (k : ℕ) : ℕ := 9^k + 3^k + 1

private theorem three_reduce {R : Type*} [Monoid R] (x : R)
    (h : x^3 = 1) (n : ℕ) : x^n = x^(n%3) := by
  calc
    x^n = x^(3*(n/3) + n%3) := congrArg (x^·) (by omega)
    _ = x^(n%3) := by rw [pow_add, pow_mul, h, one_pow, one_mul]

private theorem q_cast (k m : ℕ) :
    (q k : ZMod m) = ((3 : ZMod m)^k)^2 + (3 : ZMod m)^k + 1 := by
  unfold q
  push_cast
  rw [← pow_mul, mul_comm k 2, pow_mul]
  norm_num

private theorem q13 (k : ℕ) : 13 ∣ q k ↔ k%3 ≠ 0 := by
  rw [← ZMod.natCast_eq_zero_iff, q_cast, three_reduce (3 : ZMod 13) (by decide)]
  have h : ∀ (r : Fin 3),
      ((3 : ZMod 13)^(r : ℕ))^2 + (3 : ZMod 13)^(r : ℕ) + 1 = 0 ↔ (r : ℕ) ≠ 0 := by
    decide +kernel
  exact h ⟨k%3, Nat.mod_lt _ (by decide)⟩

private theorem q_dvd (d r : ℕ) (hr : r%3 ≠ 0) : q d ∣ q (d*r) := by
  rw [← ZMod.natCast_eq_zero_iff, q_cast]
  let x : ZMod (q d) := 3^d
  have hq : x^2 + x + 1 = 0 :=
    by
      change ((3 : ZMod (q d))^d)^2 + (3 : ZMod (q d))^d + 1 = 0
      rw [← q_cast, ZMod.natCast_self]
  have h3 : x^3 = 1 := by
    calc
      x^3 = (x-1)*(x^2+x+1)+1 := by ring
      _ = 1 := by rw [hq, mul_zero, zero_add]
  rw [pow_mul]
  change (x^r)^2 + x^r + 1 = 0
  rw [three_reduce x h3 r]
  have hr' : r%3 = 1 ∨ r%3 = 2 := by omega
  rcases hr' with h | h
  · rwa [h, pow_one]
  · rw [h, ← pow_mul, show (2:ℕ)*2 = 3+1 by decide, pow_add, h3, one_mul, pow_one]
    rw [add_comm x, hq]

private theorem q_strict : StrictMono q := by
  intro a b hab
  unfold q
  have h₁ : 9^a < 9^b := Nat.pow_lt_pow_right (by decide) hab
  have h₂ : 3^a < 3^b := Nat.pow_lt_pow_right (by decide) hab
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a374105.main := by
  intro k p hp heq
  change q k = 13*p at heq
  have hk : k%3 ≠ 0 := (q13 k).mp ⟨p, heq⟩
  have hk2 : 2 ≤ k := by
    by_contra! hh
    interval_cases k
    · exact hk rfl
    · have h : q 1 = 13 := by decide
      have := hp.two_le
      omega
  by_contra hnp
  obtain ⟨d, hd, hd2, hdk⟩ := Nat.exists_dvd_of_not_prime2 hk2 hnp
  obtain ⟨r, hr⟩ := hd
  have hkd : ¬ 3 ∣ k := by
    intro h
    exact hk (Nat.mod_eq_zero_of_dvd h)
  have hd3 : d%3 ≠ 0 := fun h =>
    hkd (by rw [hr]; exact dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero h) r)
  have hr3 : r%3 ≠ 0 := fun h =>
    hkd (by rw [hr]; exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero h) d)
  have hdiv : q d ∣ q k := by rw [hr]; exact q_dvd d r hr3
  obtain ⟨u, hu⟩ := (q13 d).mpr hd3
  obtain ⟨v, hv⟩ := hdiv
  have hv' : p = u*v := by
    rw [heq, hu, mul_assoc] at hv
    omega
  have hul : 1 < u := by
    have ht := q_strict (show 1 < d by omega)
    have h : q 1 = 13 := by decide
    omega
  have hup : u < p := by
    have ht := q_strict hdk
    omega
  exact (Nat.prime_def_lt'.mp hp).2 u (by omega) hup ⟨v, hv'⟩