import OMAReductions.R_OeisA5153_conjecture_R1

/-!
# Step H1 of the reduction OeisA5153.conjecture.R1

Doubling preserves practicality: write `m ≤ 2 q` as `2 a + b` with `b ≤ 1` and `a ≤ q`, represent
`a` by distinct divisors `d` of `q`, and use the divisors `2 d` of `2 q` together with `1` when
`b = 1`. Starting from the practical numbers `1` and `6`, every `2 ^ k` and every `3 * 2 ^ (k + 1)`
is practical, so `n = (n - q) + q` for the relevant `q`.
-/

namespace OMA.H5153

theorem practical_double {q : ℕ} (hq : 0 < q) (h : Nat.IsPractical q) :
    Nat.IsPractical (2 * q) := by
  intro m hm
  obtain ⟨B, hB, hsum⟩ := h (m / 2) (by omega)
  have hBd : ∀ d ∈ B, d ∣ q := fun d hd => (Nat.mem_divisors.1 (hB hd)).1
  have hinj : Set.InjOn (fun d : ℕ => 2 * d) (B : Set ℕ) := fun a _ b _ hab => by
    simp only at hab; omega
  have himg : ∀ x ∈ B.image (fun d => 2 * d), x ∈ (2 * q).divisors := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hx
    exact Nat.mem_divisors.2 ⟨Nat.mul_dvd_mul_left 2 (hBd d hd), by omega⟩
  have hsum2 : ∑ i ∈ B.image (fun d => 2 * d), i = 2 * (m / 2) := by
    rw [Finset.sum_image hinj, ← Finset.mul_sum, hsum]
  rcases Nat.even_or_odd m with he | ho
  · refine ⟨B.image (fun d => 2 * d), fun x hx => himg x hx, ?_⟩
    rw [hsum2]; obtain ⟨t, rfl⟩ := he; omega
  · have h1 : (1 : ℕ) ∉ B.image (fun d => 2 * d) := by
      intro h1
      obtain ⟨d, _, hd⟩ := Finset.mem_image.1 h1
      omega
    refine ⟨insert 1 (B.image (fun d => 2 * d)), ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Nat.mem_divisors.2 ⟨one_dvd _, by omega⟩
      · exact himg x hx
    · rw [Finset.sum_insert h1, hsum2]; obtain ⟨t, rfl⟩ := ho; omega

theorem practical_two_pow_mul {c : ℕ} (hc : 0 < c) (h : Nat.IsPractical c) (k : ℕ) :
    Nat.IsPractical (2 ^ k * c) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ, mul_comm (2 ^ k) 2, mul_assoc]
    exact practical_double (by positivity) ih

end OMA.H5153

open OMA.H5153 in
theorem OMA.solution : OMA.R_OeisA5153_conjecture_R1.H1 := by
  intro n k hk
  rcases hk with hp | hp
  · refine ⟨n - 2 ^ k, 2 ^ k, hp, ⟨by positivity, ?_⟩, ?_⟩
    · simpa using practical_two_pow_mul one_pos OeisA5153.a_1.2 k
    · have := hp.two_le; omega
  · refine ⟨n - 3 * 2 ^ (k + 1), 3 * 2 ^ (k + 1), hp, ⟨by positivity, ?_⟩, ?_⟩
    · have h6 := practical_two_pow_mul (by norm_num) OeisA5153.a_6.2 k
      have : 2 ^ k * 6 = 3 * 2 ^ (k + 1) := by ring
      rwa [this] at h6
    · have := hp.two_le; omega
