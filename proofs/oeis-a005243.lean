import OMAStatements.S_oeis_a005243

/-!
Quantitative omission for Hofstadter's consecutive-sum sequence.
For every K there is a missing integer between K+1 and 8*(K+2)^4.
The infinitude assertion is a known theorem of Quanyu Tang, Journal of Integer
Sequences 29 (2026), Article 26.6.1. This proof works directly with the
set-based definition in the OEIS statement.
-/

namespace OMA.HofstadterOmissions

open Finset Classical

private theorem double_prefix (y : ℕ) :
    (∑ i ∈ range (y + 1), i) * 2 = y * (y + 1) := by
  simpa [Nat.mul_comm] using sum_range_id_mul_two (y + 1)

private theorem double_block (x y : ℕ) (hx : 0 < x) (hxy : x ≤ y) :
    (∑ i ∈ Icc x y, i) * 2 = (y - x + 1) * (x + y) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ x by omega)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hxy
  have he : Ico (1+a) (1+a+b+1) = Icc (1+a) (1+a+b) := by
    ext i
    simp only [mem_Ico, mem_Icc]
    omega
  have h := sum_range_add_sum_Ico (fun i : ℕ => i) (show 1+a ≤ 1+a+b+1 by omega)
  rw [he] at h
  have h₁ := double_prefix a
  rw [Nat.add_comm a 1] at h₁
  have h₂ := double_prefix (1+a+b)
  rw [show 1+a+b-(1+a) = b by omega]
  nlinarith

private theorem block_ne_pow (x y e : ℕ) (hx : 0 < x) (hxy : x < y) :
    (∑ i ∈ Icc x y, i) ≠ 2^e := by
  intro h
  have hfac := double_block x y hx hxy.le
  rw [h, ← pow_succ] at hfac
  have odd_factor {d : ℕ} (hd : Odd d) (hdiv : d ∣ 2^(e+1)) : d = 1 :=
    ((Nat.coprime_two_right.mpr hd).pow_right _).eq_one_of_dvd hdiv
  have hpar : Odd (y-x+1) ∨ Odd (x+y) := by
    simp only [Nat.odd_iff]
    omega
  rcases hpar with hl | hr
  · have hone := odd_factor hl (hfac ▸ Nat.dvd_mul_right (y-x+1) (x+y))
    omega
  · have hone := odd_factor hr (hfac ▸ Nat.dvd_mul_left (x+y) (y-x+1))
    omega

private theorem prefix_avoids (y v b : ℕ) (hb : b < v)
    (lo : 2*v^2 ≤ ∑ i ∈ range (y+1), i)
    (hi : (∑ i ∈ range (y+1), i) ≤ 2*v^2 + b) : False := by
  have h := double_prefix y
  by_cases hy : y < 2*v
  · have h₁ := Nat.mul_le_mul_left y (show y+1 ≤ 2*v by omega)
    have h₂ := Nat.mul_lt_mul_of_pos_right hy (show 0 < 2*v by omega)
    nlinarith
  · have h₁ := Nat.mul_le_mul (show 2*v ≤ y by omega) (show 2*v+1 ≤ y+1 by omega)
    nlinarith

/-- An explicit upper bound for the next omitted positive integer. -/
theorem missing_in_interval {S : Set ℕ}
    (gen : ∀ m ∈ S, 2 < m → ∃ x y : ℕ, x < y ∧ y < m ∧
      ∑ z ∈ (Icc x y).filter (· ∈ S), z = m) (K : ℕ) :
    ∃ z : ℕ, K < z ∧ z ≤ 8*(K+2)^4 ∧ z ∉ S := by
  classical
  let T := (K+2)^2
  let e := Nat.log 2 T + 1
  let v := 2^e
  let N := 2*v^2
  have hv : T < v := Nat.lt_pow_succ_log_self (by decide : 1 < 2) T
  have hv' : v ≤ 2*T := by
    dsimp [v,e]
    rw [pow_succ]
    have ht : T ≠ 0 := by dsimp [T]; positivity
    have h := Nat.pow_log_le_self 2 ht
    omega
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hv0 : 1 < v := by omega
  have hnK : K < N := by dsimp [N,T] at *; nlinarith
  have hn2 : 2 < N := by dsimp [N]; nlinarith
  have hupper : N ≤ 8*(K+2)^4 := by
    have hs := Nat.pow_le_pow_left hv' 2
    dsimp [N,T] at *
    nlinarith
  by_contra! hall
  have mem {z : ℕ} (lo : K < z) (hi : z ≤ N) : z ∈ S :=
    hall z lo (hi.trans hupper)
  obtain ⟨x,y,hxy,hy,hsum⟩ := gen N (mem hnK le_rfl) hn2
  by_cases hx : K < x
  · have he : (Icc x y).filter (· ∈ S) = Icc x y := by
      apply filter_eq_self.mpr
      intro z hz
      obtain ⟨h₁,h₂⟩ := mem_Icc.mp hz
      exact mem (hx.trans_le h₁) (h₂.trans hy.le)
    rw [he] at hsum
    have hpow : N = 2^(2*e+1) := by
      calc
        N = 2*(2^e)^2 := rfl
        _ = 2^(e*2)*2 := by rw [pow_mul]; ring
        _ = 2^(2*e+1) := by rw [pow_succ 2 (2*e), Nat.mul_comm 2 e]
    exact block_ne_pow x y (2*e+1) (by omega) hxy (hsum.trans hpow)
  · let A := (Icc x y).filter (· ∈ S)
    have hA : A ⊆ range (y+1) := by
      intro z hz
      exact mem_range.mpr (by have h := (mem_Icc.mp (mem_filter.mp hz).1).2; omega)
    have hdiff : range (y+1) \ A ⊆ range (K+1) := by
      intro z hz
      obtain ⟨hz,hout⟩ := mem_sdiff.mp hz
      have hz' := mem_range.mp hz
      apply mem_range.mpr
      by_contra! h
      exact hout (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,mem (by omega) (by omega)⟩)
    have h₁ := sum_le_sum_of_subset (f := fun z : ℕ => z) hdiff
    have h₂ := sum_sdiff (f := fun z : ℕ => z) hA
    have h₃ : (∑ z ∈ A, z) = N := hsum
    rw [h₃] at h₂
    have hB : (∑ i ∈ range (K+1), i) < v := by
      have h := double_prefix K
      dsimp [T] at hv
      nlinarith
    exact prefix_avoids y v _ hB (by dsimp [N] at h₂; omega) (by dsimp [N] at h₂; omega)

end OMA.HofstadterOmissions

theorem OMA.solution : type_of% @OMA.S_oeis_a005243.main := by
  classical
  intro S rule
  apply Set.infinite_of_forall_exists_gt
  intro K
  have gen (m : ℕ) (hm : m ∈ S) (hlarge : 2 < m) := (rule m).mp hm
  obtain ⟨z,hz,-,hout⟩ := OMA.HofstadterOmissions.missing_in_interval (S := S) (by
    intro m hm hlarge
    rcases gen m hm hlarge with h | h | ⟨x,-,y,-,hxy,hy,hs⟩
    · omega
    · omega
    · exact ⟨x,y,hxy,hy,hs⟩) K
  exact ⟨z,⟨by omega,hout⟩,hz⟩
