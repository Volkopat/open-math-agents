import OMAStatements.S_oeis_a249968

namespace OMA.S_oeis_a249968



lemma sq_mod_100 : ∀ x : ℕ, x < 100 → (x * x) % 100 = 25 → x % 10 = 5 := by decide

lemma common_residues : ∀ a : ℕ, a < 100 → ∀ b : ℕ, b < 100 →
    (a * a) % 100 = (b * b + b) % 100 → (a * a) % 100 = 0 ∨ (a * a) % 100 = 56 := by
  decide +kernel

/-- Controls from the entry: 16 and 14130 are terms (16^2 = 256, 225625 = 475^2; 14130^2 = 199656900,
219965690025 = 469005^2), and 1, 2, 3 are not. -/
example : InA249968 16 ∧ InA249968 14130 ∧ ¬ InA249968 1 ∧ ¬ InA249968 2 ∧ ¬ InA249968 3 := by
  unfold InA249968
  decide +kernel

/-- Wu's conjecture: for every term n, n^2 has at least three digits and ends in 00 or 56. -/
theorem conjecture : ∀ n : ℕ, InA249968 n → 100 ≤ n ^ 2 ∧ (n ^ 2 % 100 = 0 ∨ n ^ 2 % 100 = 56) := by
  rintro n ⟨hn, r, hr⟩
  unfold wrap at hr
  set D := (Nat.digits 10 (n ^ 2)).length with hD
  have hn2 : 0 < n ^ 2 := by positivity
  -- r ends in 5
  have hr25 : (r * r) % 100 = 25 := by
    rw [← hr, pow_add]
    omega
  have hr5 : r % 10 = 5 := by
    have h := sq_mod_100 (r % 100) (Nat.mod_lt _ (by norm_num))
      (by rw [← Nat.mul_mod]; exact hr25)
    omega
  set k := r / 10 with hk
  have hrk : r = 10 * k + 5 := by omega
  have hkey : k * k + k = n ^ 2 + 2 * 10 ^ D := by
    have : (10 * k + 5) * (10 * k + 5) = 2 * 10 ^ (D + 2) + 100 * n ^ 2 + 25 := by
      rw [← hrk]; exact hr.symm
    rw [pow_add] at this
    nlinarith
  -- the number of digits of n^2 is at least 1
  have hD1 : 1 ≤ D := by
    rw [hD]
    have : Nat.digits 10 (n ^ 2) ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn2.ne'
    exact List.length_pos_iff.mpr this
  rcases Nat.lt_or_ge D 2 with hD2 | hD2
  · -- d = 1: n^2 < 10 and k(k+1) = 20 + n^2 is impossible
    have hD' : D = 1 := by omega
    have hlt : n ^ 2 < 10 ^ D := Nat.lt_base_pow_length_digits (by norm_num)
    rw [hD'] at hlt hkey
    exfalso
    rcases Nat.lt_or_ge k 5 with hk5 | hk5
    · interval_cases k <;> omega
    · nlinarith
  · -- d >= 2: n^2 and k(k+1) agree mod 100
    have h100 : (2 * 10 ^ D) % 100 = 0 := by
      obtain ⟨e, he⟩ : ∃ e, D = e + 2 := ⟨D - 2, by omega⟩
      rw [he, pow_add]
      omega
    have hmod : (n ^ 2) % 100 = (k * k + k) % 100 := by
      rw [hkey]
      omega
    have h1 : (n % 100) * (n % 100) % 100 = n ^ 2 % 100 := by rw [← Nat.mul_mod, sq]
    have h2 : ((k % 100) * (k % 100) + k % 100) % 100 = (k * k + k) % 100 := by
      rw [Nat.add_mod, ← Nat.mul_mod, Nat.mod_mod, ← Nat.add_mod]
    have hres := common_residues (n % 100) (Nat.mod_lt _ (by norm_num)) (k % 100)
      (Nat.mod_lt _ (by norm_num)) (by rw [h1, h2]; exact hmod)
    rw [h1] at hres
    refine ⟨?_, hres⟩
    have hge : 10 ≤ n ^ 2 := by
      by_contra hlt
      have h1 : (Nat.digits 10 (n ^ 2)).length ≤ 1 := by
        rw [Nat.digits_of_lt 10 (n ^ 2) hn2.ne' (by omega)]
        simp
      omega
    rcases hres with h | h
    · omega
    · by_contra hlt
      have hn9 : n ≤ 9 := by nlinarith
      interval_cases n <;> omega

end OMA.S_oeis_a249968

theorem OMA.solution : type_of% @OMA.S_oeis_a249968.main :=
  OMA.S_oeis_a249968.conjecture
