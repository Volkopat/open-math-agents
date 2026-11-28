import OMAStatements.S_oeis_a078173

namespace OMA.P_oeis_a078173

open OMA.S_oeis_a078173

lemma t_le {n r s t : ℕ} (h : Sol n r s t) : t ≤ n * (n + 2) := by
  obtain ⟨hr, hrs, hst, he⟩ := h
  have h1 : n + 1 ≤ r * s := by
    by_contra hc
    rw [not_le] at hc
    have : r * s * t ≤ n * t := Nat.mul_le_mul_right t (by omega)
    have : n * t < n * (r + s + t) := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        simp at he
        omega
      · exact Nat.mul_lt_mul_of_pos_left (by omega) h0
    omega
  obtain ⟨k, hk⟩ : ∃ k, r * s = n + 1 + k := ⟨r * s - (n + 1), by omega⟩
  have h2 : r + s ≤ r * s + 1 := by nlinarith
  have h3 : (k + 1) * t = n * (r + s) := by
    have : (n + (k + 1)) * t = n * (r + s + t) := by rw [← he, hk]; ring
    nlinarith
  by_contra hc
  rw [not_le] at hc
  have h4 : (k + 1) * (n * (n + 2) + 1) ≤ (k + 1) * t := Nat.mul_le_mul_left _ hc
  have h5 : n * (r + s) ≤ n * (n + k + 2) := Nat.mul_le_mul_left _ (by omega)
  rw [← h3] at h5
  have h6 := h4.trans h5
  ring_nf at h6
  nlinarith

lemma s_le {n r s t : ℕ} (h : Sol n r s t) : s ≤ 2 * n := by
  obtain ⟨hr, hrs, hst, he⟩ := h
  by_contra hc
  rw [not_le] at hc
  have h1 : r * (2 * n + 1) * t ≤ r * s * t :=
    Nat.mul_le_mul_right t (Nat.mul_le_mul_left r hc)
  have h2 : n * (r + s + t) ≤ n * r + 2 * n * t := by nlinarith
  have h3 : n * 1 * t ≤ n * r * t := Nat.mul_le_mul_right t (Nat.mul_le_mul_left n hr)
  have h4 : r * t ≤ n * r := by nlinarith
  have h5 : t ≤ n := by
    by_contra h6
    rw [not_le] at h6
    have : n * r < t * r := Nat.mul_lt_mul_of_pos_right h6 hr
    nlinarith
  omega

end OMA.P_oeis_a078173

open OMA.S_oeis_a078173 OMA.P_oeis_a078173 in
theorem OMA.solution : type_of% @OMA.S_oeis_a078173.main := by
  intro n hn
  refine ⟨⟨⟨1, n + 1, by refine ⟨by omega, by omega, by nlinarith, by ring⟩⟩, ?_⟩,
    ⟨⟨1, 2 * n + 1, by refine ⟨by omega, by omega, by omega, by ring⟩⟩, ?_⟩⟩
  · rintro t ⟨r, s, h⟩
    exact t_le h
  · rintro s ⟨r, t, h⟩
    exact s_le h
