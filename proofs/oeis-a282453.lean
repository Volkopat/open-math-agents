import OMAStatements.S_oeis_a282453

/-! Chai Wah Wu's recurrence and generating function for OEIS A282453
(https://oeis.org/A282453), the horizontal axis of Rule 475.
The four columns next to the moving left edge have period four in moving
coordinates. On the interior of the axis, reflection makes the vertical
neighbors equal, so a uniform horizontal triple flips its central bit. -/

namespace Rule475
open OMA.S_oeis_a282453

private abbrev C := cell 475
private def step (c r l u d : Bool) : Bool :=
  (475 : ℕ).testBit (c.toNat + 2*(r.toNat + l.toNat + u.toNat + d.toNat))
private lemma next (t : ℕ) (x y : ℤ) : C (t+1) x y =
    step (C t x y) (C t (x+1) y) (C t (x-1) y) (C t x (y+1)) (C t x (y-1)) := rfl
private def bg (t : ℕ) : Bool := decide (t % 2 = 1)
private lemma flip (b v : Bool) : step b b b v v = !b := by cases b <;> cases v <;> decide
private lemma bg_next (t : ℕ) : bg (t+1) = !bg t := by
  rcases (show t%2=0 ∨ t%2=1 by omega) with h | h <;>
    simp [bg, h, show (t+1)%2 = 1-t%2 by omega]

private lemma outside (t : ℕ) (x y : ℤ)
    (h : x < -(t:ℤ) ∨ (t:ℤ) < x ∨ y < -(t:ℤ) ∨ (t:ℤ) < y) : C t x y = bg t := by
  induction t generalizing x y with
  | zero =>
    change decide (x=0 ∧ y=0) = false
    simp only [decide_eq_false_iff_not]
    omega
  | succ t ih =>
    push_cast at h
    rw [next, ih x y (by omega), ih (x+1) y (by omega), ih (x-1) y (by omega),
      ih x (y+1) (by omega), ih x (y-1) (by omega), flip, bg_next]

private lemma reflectX (t : ℕ) (x y : ℤ) : C t (-x) y = C t x y := by
  induction t generalizing x y with
  | zero => simp [C, cell]
  | succ t ih =>
    rw [next,next, show -x+1 = -(x-1) by ring, show -x-1 = -(x+1) by ring]
    simp only [ih,step, Nat.add_comm (C t (x-1) y).toNat (C t (x+1) y).toNat]

private lemma reflectY (t : ℕ) (x y : ℤ) : C t x (-y) = C t x y := by
  induction t generalizing x y with
  | zero => simp [C, cell]
  | succ t ih =>
    rw [next,next, show -y+1 = -(y-1) by ring, show -y-1 = -(y+1) by ring]
    simp only [ih,step,Nat.add_assoc, Nat.add_comm (C t x (y-1)).toNat (C t x (y+1)).toNat]

/-- The listed vertical coordinates differ from the background. Row h of each
list describes the column at x = -t+h, at the indicated phase t modulo four. -/
private def changes (p : ℕ) : List (List ℤ) :=
  match p with
  | 0 => [[0], [0], [-1,0,1], [-2,-1,0,1,2]]
  | 1 => [[0], [-1,1], [0], [-1,0,1]]
  | 2 => [[0], [0], [-2,-1,0,1,2], [-1,0,1]]
  | _ => [[0], [-1,1], [-2,0,2], [-3,0,3]]

private def front (p : ℕ) (h y : ℤ) : Bool :=
  if h < 0 ∨ 3 < h ∨ y < -3 ∨ 3 < y then bg p
  else xor (bg p) (((changes p).getD h.toNat []).contains y)

private lemma bounded {z : ℤ} {a : ℤ} {N : ℕ} (lo : a ≤ z) (hi : z < a+N) :
    ∃ i : Fin N, z = (i:ℤ) + a :=
  ⟨⟨(z-a).toNat, by omega⟩, by simp; omega⟩

private lemma front_step (p : Fin 4) (h y : ℤ) (hh : h ≤ 3) :
    step (front p (h-1) y) (front p h y) (front p (h-2) y)
      (front p (h-1) (y+1)) (front p (h-1) (y-1)) = front ((p.val+1)%4) h y := by
  by_cases small : 0 ≤ h ∧ -4 ≤ y ∧ y ≤ 4
  · obtain ⟨i, hi⟩ := bounded (N:=4) small.1 (by omega)
    obtain ⟨j, rfl⟩ := bounded (N:=9) small.2.1 (by omega)
    simp only [add_zero] at hi
    subst h
    exact (by decide : ∀ (q i : Fin 4) (j : Fin 9),
      step (front q ((i:ℤ)-1) (j + (-4:ℤ))) (front q i (j + (-4:ℤ)))
        (front q ((i:ℤ)-2) (j + (-4:ℤ))) (front q ((i:ℤ)-1) (j + (-4:ℤ)+1))
        (front q ((i:ℤ)-1) (j + (-4:ℤ)-1)) = front ((q.val+1)%4) i (j + (-4:ℤ))) p i j
  · simp only [front, if_pos (by omega : h-1 < 0 ∨ 3 < h-1 ∨ y < -3 ∨ 3 < y),
      if_pos (by omega : h < 0 ∨ 3 < h ∨ y < -3 ∨ 3 < y),
      if_pos (by omega : h-2 < 0 ∨ 3 < h-2 ∨ y < -3 ∨ 3 < y),
      if_pos (by omega : h-1 < 0 ∨ 3 < h-1 ∨ y+1 < -3 ∨ 3 < y+1),
      if_pos (by omega : h-1 < 0 ∨ 3 < h-1 ∨ y-1 < -3 ∨ 3 < y-1), flip]
    exact (by decide : ∀ q : Fin 4, (!bg q.val) = bg ((q.val+1)%4)) p

private lemma front_four (h y : ℤ) (hh : h ≤ 3) : C 4 (h-4) y = front 0 h y := by
  by_cases small : 0 ≤ h ∧ -4 ≤ y ∧ y ≤ 4
  · obtain ⟨i, hi⟩ := bounded (N:=4) small.1 (by omega)
    obtain ⟨j, rfl⟩ := bounded (N:=9) small.2.1 (by omega)
    simp only [add_zero] at hi
    subst h
    exact (by decide : ∀ (i : Fin 4) (j : Fin 9),
      C 4 ((i:ℤ)-4) (j+(-4:ℤ)) = front 0 i (j+(-4:ℤ))) i j
  · rw [outside 4 (h-4) y (by omega : h-4 < -(4:ℤ) ∨ (4:ℤ) < h-4 ∨ y < -(4:ℤ) ∨ 4 < y)]
    simp [front, show h < 0 ∨ 3 < h ∨ y < -3 ∨ 3 < y by omega, bg]

private lemma front_correct (t : ℕ) (ht : 4 ≤ t) : ∀ h y : ℤ, h ≤ 3 →
    C t (h-t) y = front (t%4) h y := by
  induction t, ht using Nat.le_induction with
  | base => exact front_four
  | succ t ht ih =>
    intro h y hh
    push_cast
    rw [next, show h-((t:ℤ)+1) = (h-1)-t by ring,
      show h-1-(t:ℤ)+1 = h-t by ring, show h-1-(t:ℤ)-1 = (h-2)-t by ring]
    rw [ih (h-1) y (by omega), ih h y hh, ih (h-2) y (by omega),
      ih (h-1) (y+1) (by omega), ih (h-1) (y-1) (by omega)]
    simpa [show (t%4+1)%4 = (t+1)%4 by omega] using
      front_step ⟨t%4, by omega⟩ h y hh

private lemma phase_bg (t : ℕ) : bg (t%4) = bg t := by
  simp only [bg, show t%4%2 = t%2 by omega]

private lemma interior (t : ℕ) (ht : 4 ≤ t) :
    ∀ x : ℤ, -(t:ℤ)+2 ≤ x → x ≤ t-2 → C t x 0 = !bg t := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro x lo hi
    norm_num at lo hi
    interval_cases x <;> decide
  | succ t ht ih =>
    intro x lo hi
    push_cast at lo hi
    have side (z : ℤ) (hz : -(t:ℤ)-1+2 ≤ z) (hz' : z ≤ -(t:ℤ)+2) :
        C (t+1) z 0 = !bg (t+1) := by
      let h := z+(t+1)
      have hf := front_correct (t+1) (by omega) h 0 (by dsimp [h]; omega)
      have hcoord : h-((t+1:ℕ):ℤ) = z := by dsimp [h]; ring
      rw [hcoord] at hf
      rw [hf, ← phase_bg (t+1)]
      have tab : ∀ p : Fin 4, front p 2 0 = !bg p ∧ front p 3 0 = !bg p := by decide
      rcases (show h = 2 ∨ h = 3 by dsimp [h]; omega) with e | e
      · exact e ▸ (tab ⟨(t+1)%4, by omega⟩).1
      · exact e ▸ (tab ⟨(t+1)%4, by omega⟩).2
    by_cases left : x ≤ -(t:ℤ)+2
    · exact side x (by omega) left
    by_cases right : (t:ℤ)-2 ≤ x
    · rw [← reflectX (t+1) x 0]
      exact side (-x) (by omega) (by omega)
    rw [next, ih x (by omega) (by omega), ih (x+1) (by omega) (by omega),
      ih (x-1) (by omega) (by omega)]
    change step (!bg t) (!bg t) (!bg t) (C t x 1) (C t x (-1)) = !bg (t+1)
    rw [reflectY t x 1, flip, bg_next]

/-- At an even stage every cell from the left edge to the origin is on. At an odd stage its unique
one is one place in from the moving edge. -/
private lemma halfAxis (t k : ℕ) (hk : k ≤ t) :
    cell 475 t ((k:ℤ)-t) 0 = if t%2 = 0 then true else decide (k=1) := by
  by_cases ht : t < 4
  · interval_cases t <;> interval_cases k <;> decide
  by_cases small : k ≤ 1
  · change C t ((k:ℤ)-t) 0 = _
    rw [front_correct t (by omega) k 0 (by omega)]
    have tab : ∀ (p : Fin 4) (i : Fin 2),
        front p i 0 = if p.val%2=0 then true else decide (i.val=1) := by decide
    simpa [show t%4%2=t%2 by omega] using tab ⟨t%4, by omega⟩ ⟨k, by omega⟩
  change C t ((k:ℤ)-t) 0 = _
  rw [interior t (by omega) _ (by omega) (by omega)]
  rcases (show t%2=0 ∨ t%2=1 by omega) with e | e <;> simp [bg,e,show k≠1 by omega]

private lemma allOnes (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (2:ℤ)^(n-k)) = 2^(n+1)-1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, ih, pow_succ]
    ring

private lemma even_value (n : ℕ) (h : n%2=0) : a n = 2^(n+1)-1 := by
  rw [a, ← allOnes]
  apply Finset.sum_congr rfl
  intro k hk
  rw [halfAxis n k (by simpa using Finset.mem_range.mp hk)]
  simp [h]

private lemma odd_value (n : ℕ) (h : n%2=1) : a n = 2^(n-1) := by
  rw [a, Finset.sum_eq_single 1]
  · rw [halfAxis n 1 (by omega)]
    simp [h]
  · intro k hk hne
    rw [halfAxis n k (by simpa using Finset.mem_range.mp hk)]
    simp [h, hne]
  · simp [show 1 < n+1 by omega]

private lemma recurrence (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℚ) = 5*a (n-2)-4*a (n-4) := by
  suffices hz : a n = 5*a (n-2)-4*a (n-4) by exact_mod_cast hz
  rcases (show n%2=0 ∨ n%2=1 by omega) with he | ho
  · rw [even_value n he, even_value (n-2) (by omega), even_value (n-4) (by omega),
      show n+1=(n-4+1)+4 by omega, show n-2+1=(n-4+1)+2 by omega, pow_add, pow_add]
    ring
  · rw [odd_value n ho, odd_value (n-2) (by omega), odd_value (n-4) (by omega),
      show n-1=(n-4-1)+4 by omega, show n-2-1=(n-4-1)+2 by omega, pow_add, pow_add]
    ring

open PowerSeries in
private lemma generating_function :
    mk (fun n => (a n : ℚ)) * (4*X^4-5*X^2+1 : PowerSeries ℚ) = -X^3+2*X^2+X+1 := by
  let F := mk (fun n => (a n : ℚ))
  change F * _ = _
  rw [show F * (4*X^4-5*X^2+1) = 4 • (F*X^4) - 5 • (F*X^2) + F by
    simp only [nsmul_eq_mul]; ring]
  rw [show (-X^3+2*X^2+X+1 : PowerSeries ℚ) = -X^3+(X^2+X^2)+X^1+1 by ring]
  ext n
  simp only [map_add, map_sub, map_neg, map_nsmul]
  simp only [coeff_mul_X_pow', coeff_X_pow,
    coeff_one, F, coeff_mk, nsmul_eq_mul]
  by_cases hn : 4 ≤ n
  · simp [hn, show 2 ≤ n by omega, show n ≠ 3 by omega, show n ≠ 2 by omega,
      show n ≠ 1 by omega, show n ≠ 0 by omega]
    linarith [recurrence n hn]
  · interval_cases n <;> norm_num [show a 0=1 by decide, show a 1=1 by decide,
      show a 2=7 by decide, show a 3=4 by decide]

end Rule475

theorem OMA.solution : type_of% @OMA.S_oeis_a282453.main :=
  ⟨Rule475.recurrence, Rule475.generating_function⟩
