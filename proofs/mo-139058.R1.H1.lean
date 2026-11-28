import OMAReductions.R_mo_139058_R1

/-!
Proof of `OMA.R_mo_139058_R1.H1`.
For `p < q`, an integer `s` lies in `A(p, q)` iff `q - p` divides `1 - s p` (write `m = s - n`),
and `A(p, q) = A(q, p)`, so `f` is symmetric. Hence for `q - p = 1` every integer is in
`A(p, q)` and `f(p, q) = (2, 3)`; for `q - p = 2` (so `p` is odd) `A(p, q)` is the odd
integers and `f(p, q) = (3, 5)`; for `q - p = 4` (so `p` is odd) `A(p, q)` is the class of `p`
modulo `4`, giving `f(p, q) = (5, 13)` when `p = 1 mod 4` and `(3, 7)` when `p = 3 mod 4`.
Each of `(2, 3)`, `(3, 5)`, `(3, 7)` and `(5, 13)` is a fixed point of `f` (for `(5, 13)`
the class is `5 mod 8`), so `f^[1] (p, q) = f^[2] (p, q)`.
-/

namespace OMAProof.Mo139058

open OMA.S_mo_139058

theorem mem_A (p q : ℕ) (s : ℤ) : s ∈ A p q ↔ ((q : ℤ) - p) ∣ 1 - s * p := by
  constructor
  · rintro ⟨m, n, h, rfl⟩
    exact ⟨n, by linear_combination -h⟩
  · rintro ⟨k, hk⟩
    exact ⟨s - k, k, by linear_combination -hk, by ring⟩

theorem A_comm (p q : ℕ) : A p q = A q p := by
  ext s
  constructor
  · rintro ⟨m, n, h, rfl⟩
    exact ⟨n, m, by linarith, by ring⟩
  · rintro ⟨m, n, h, rfl⟩
    exact ⟨n, m, by linarith, by ring⟩

theorem f_comm (p q : ℕ) : f (p, q) = f (q, p) := by
  simp only [f, first, second, A_comm p q]

theorem sInf_eq {s : Set ℕ} {x : ℕ} (hx : x ∈ s) (hmin : ∀ y ∈ s, x ≤ y) : sInf s = x :=
  le_antisymm (Nat.sInf_le hx) (hmin _ (Nat.sInf_mem ⟨x, hx⟩))

theorem f_eq {p q a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a < b)
    (hA : (a : ℤ) ∈ A p q) (hB : (b : ℤ) ∈ A p q)
    (h1 : ∀ y < a, y.Prime → (y : ℤ) ∉ A p q)
    (h2 : ∀ y, a < y → y < b → y.Prime → (y : ℤ) ∉ A p q) : f (p, q) = (a, b) := by
  have e1 : first p q = a := by
    refine sInf_eq ⟨ha, hA⟩ (fun y hy => ?_)
    by_contra h
    exact h1 y (by omega) hy.1 hy.2
  refine Prod.ext e1 ?_
  change second p q = b
  unfold second
  rw [e1]
  refine sInf_eq ⟨hb, hB, hab⟩ (fun y hy => ?_)
  by_contra h
  exact h2 y hy.2.2 (by omega) hy.1 hy.2.1

theorem f_one {p q : ℕ} (h : (q : ℤ) - p = 1) : f (p, q) = (2, 3) := by
  apply f_eq (by norm_num) (by norm_num) (by norm_num)
  · rw [mem_A, h]; exact one_dvd _
  · rw [mem_A, h]; exact one_dvd _
  · intro y hy hyp
    interval_cases y <;> norm_num at hyp
  · intro y h1 h2
    omega

theorem f_two {p q : ℕ} (h : (q : ℤ) - p = 2) (hp : p % 2 = 1) : f (p, q) = (3, 5) := by
  apply f_eq (by norm_num) (by norm_num) (by norm_num)
  · rw [mem_A, h]; push_cast; omega
  · rw [mem_A, h]; push_cast; omega
  · intro y hy hyp hm
    rw [mem_A, h] at hm
    interval_cases y <;> first | (push_cast at hm; omega) | norm_num at hyp
  · intro y h1 h2 hyp hm
    interval_cases y; norm_num at hyp

theorem f_four_one {p q : ℕ} (h : (q : ℤ) - p = 4) (hp : p % 4 = 1) : f (p, q) = (5, 13) := by
  apply f_eq (by norm_num) (by norm_num) (by norm_num)
  · rw [mem_A, h]; push_cast; omega
  · rw [mem_A, h]; push_cast; omega
  · intro y hy hyp hm
    rw [mem_A, h] at hm
    interval_cases y <;> first | (push_cast at hm; omega) | norm_num at hyp
  · intro y h1 h2 hyp hm
    rw [mem_A, h] at hm
    interval_cases y <;> first | (push_cast at hm; omega) | norm_num at hyp

theorem f_four_three {p q : ℕ} (h : (q : ℤ) - p = 4) (hp : p % 4 = 3) : f (p, q) = (3, 7) := by
  apply f_eq (by norm_num) (by norm_num) (by norm_num)
  · rw [mem_A, h]; push_cast; omega
  · rw [mem_A, h]; push_cast; omega
  · intro y hy hyp hm
    rw [mem_A, h] at hm
    interval_cases y <;> (push_cast at hm; omega)
  · intro y h1 h2 hyp hm
    rw [mem_A, h] at hm
    interval_cases y <;> (push_cast at hm; omega)

theorem f_eight {p q : ℕ} (h : (q : ℤ) - p = 8) (hp : p % 8 = 5) : f (p, q) = (5, 13) := by
  apply f_eq (by norm_num) (by norm_num) (by norm_num)
  · rw [mem_A, h]; push_cast; omega
  · rw [mem_A, h]; push_cast; omega
  · intro y hy hyp hm
    rw [mem_A, h] at hm
    interval_cases y <;> (push_cast at hm; omega)
  · intro y h1 h2 hyp hm
    rw [mem_A, h] at hm
    interval_cases y <;> (push_cast at hm; omega)

/-- For `p < q` at distance `1`, `2` or `4`, the first image is a fixed point. -/
theorem key (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : q = p + 1 ∨ q = p + 2 ∨ q = p + 4) :
    f (p, q) = f (f (p, q)) := by
  rcases h with rfl | rfl | rfl
  · rw [f_one (by push_cast; ring)]
    exact (f_one (by norm_num)).symm
  · rcases hp.eq_two_or_odd with rfl | hodd
    · norm_num at hq
    rw [f_two (by push_cast; ring) hodd]
    exact (f_two (by norm_num) (by norm_num)).symm
  · rcases hp.eq_two_or_odd with rfl | hodd
    · norm_num at hq
    rcases (show p % 4 = 1 ∨ p % 4 = 3 by omega) with h4 | h4
    · rw [f_four_one (by push_cast; ring) h4]
      exact (f_eight (by norm_num) (by norm_num)).symm
    · rw [f_four_three (by push_cast; ring) h4]
      exact (f_four_three (by norm_num) (by norm_num)).symm

end OMAProof.Mo139058

open OMAProof.Mo139058 in
theorem OMA.solution : OMA.R_mo_139058_R1.H1 := by
  intro p q hp hq h
  refine ⟨1, 2, by norm_num, ?_⟩
  change OMA.S_mo_139058.f (p, q) = OMA.S_mo_139058.f (OMA.S_mo_139058.f (p, q))
  rcases h with h | h | h | h | h | h
  · exact key p q hp hq (Or.inl h)
  · exact key p q hp hq (Or.inr (Or.inl h))
  · exact key p q hp hq (Or.inr (Or.inr h))
  · rw [f_comm p q]; exact key q p hq hp (Or.inl h)
  · rw [f_comm p q]; exact key q p hq hp (Or.inr (Or.inl h))
  · rw [f_comm p q]; exact key q p hq hp (Or.inr (Or.inr h))
