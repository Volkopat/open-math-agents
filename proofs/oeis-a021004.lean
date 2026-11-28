import OMAStatements.S_oeis_a021004

namespace A021004Proof

/-- Six consecutive terms of the proposed linear recurrence. -/
private def terms : ℕ → ℤ × ℤ × ℤ × ℤ × ℤ × ℤ
  | 0 => (4,10,25,62,154,383)
  | n+1 =>
    let (a,b,c,d,e,f) := terms n
    (b,c,d,e,f,2*f+e+d-c-a)

private def u (n : ℕ) : ℤ := (terms n).1

private theorem recurrence (n : ℕ) :
    u (n+6) = 2*u (n+5)+u (n+4)+u (n+3)-u (n+2)-u n := by
  simp only [u, terms]

/-- Successive terms grow by a factor between 99/40 and 5/2. -/
private theorem growth (n : ℕ) :
    0 < u n ∧ 99 * u n ≤ 40 * u (n+1) ∧ 2 * u (n+1) ≤ 5 * u n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n < 5
    · interval_cases n <;> decide
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n-5, by omega⟩
      obtain ⟨p0, l0, h0⟩ := ih k (by omega)
      obtain ⟨p1, l1, h1⟩ := ih (k+1) (by omega)
      obtain ⟨p2, l2, h2⟩ := ih (k+2) (by omega)
      obtain ⟨p3, l3, h3⟩ := ih (k+3) (by omega)
      obtain ⟨p4, l4, h4⟩ := ih (k+4) (by omega)
      change 0 < u (k+5) ∧ 99 * u (k+5) ≤ 40 * u (k+6) ∧ 2 * u (k+6) ≤ 5 * u (k+5)
      rw [recurrence]
      constructor
      · linarith
      · constructor <;> linarith

/-- Transition matrix for the fifteen minors. The identity is proved in wstep. -/
private def C (i j : Fin 15) : ℤ :=
  match i.val, j.val with
  | 0, 5 => 1
  | 1, 6 => 1
  | 2, 7 => 1
  | 3, 8 => 1
  | 4, 0 => 1
  | 4, 5 => -1
  | 4, 6 => 1
  | 4, 7 => 1
  | 4, 8 => 2
  | 5, 9 => 1
  | 6, 10 => 1
  | 7, 11 => 1
  | 8, 1 => 1
  | 8, 9 => 1
  | 8, 10 => 1
  | 8, 11 => 2
  | 9, 12 => 1
  | 10, 13 => 1
  | 11, 2 => 1
  | 11, 9 => 1
  | 11, 12 => 1
  | 11, 13 => 2
  | 12, 14 => 1
  | 13, 3 => 1
  | 13, 10 => 1
  | 13, 12 => -1
  | 13, 14 => 2
  | 14, 4 => 1
  | 14, 11 => 1
  | 14, 13 => -1
  | 14, 14 => -1
  | _, _ => 0

/-- Alternating minors of two adjacent length-six windows, in lexicographic order. -/
private def minor (n r s : ℕ) : ℤ :=
  u (n+r)*u (n+s+1) - u (n+r+1)*u (n+s)

private def w (n : ℕ) : Fin 15 → ℤ :=
  ![minor n 0 1, minor n 0 2, minor n 0 3, minor n 0 4, minor n 0 5,
    minor n 1 2, minor n 1 3, minor n 1 4, minor n 1 5,
    minor n 2 3, minor n 2 4, minor n 2 5, minor n 3 4, minor n 3 5, minor n 4 5]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem wstep (n : ℕ) (i : Fin 15) :
    w (n+1) i = ∑ j : Fin 15, C i j * w n j := by
  have h7 : u (n+7) = 2*u (n+6)+u (n+5)+u (n+4)-u (n+3)-u (n+1) := recurrence (n+1)
  fin_cases i <;> norm_num [Fin.sum_univ_succ, C, w, minor, Nat.add_assoc] <;>
    simp only [h7, recurrence n] <;> ring

/-- Storing each square as a table allows the kernel to reuse its entries. -/
private def square (M : Matrix (Fin 15) (Fin 15) ℤ) : Matrix (Fin 15) (Fin 15) ℤ :=
  let rows := Vector.ofFn (fun i : Fin 15 => Vector.ofFn ((M * M) i))
  fun i j => (rows.get i).get j

private theorem square_eq (M : Matrix (Fin 15) (Fin 15) ℤ) : square M = M * M := by
  ext i j
  simp [square]

private abbrev A : Matrix (Fin 15) (Fin 15) ℤ := C

private def m16 := square (square (square (square A)))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem cap (i : Fin 15) : (∑ j : Fin 15, |m16 i j|) ≤ 1966352 := by
  revert i
  decide +kernel

private theorem block (n : ℕ) (V : ℤ) (hV : 0 ≤ V)
    (h : ∀ i, |w n i| ≤ V) : ∀ i, |w (n + 16) i| ≤ 1966352 * V := by
  have step (t : ℕ) : w (t+1) = A.mulVec (w t) := funext (wstep t)
  have iter (k : ℕ) : w (n+k) = (A ^ k).mulVec (w n) := by
    induction k with
    | zero => simp
    | succ k ih => rw [← Nat.add_assoc, step, ih, Matrix.mulVec_mulVec, pow_succ']
  have sixteen : A ^ 16 = m16 := by
    simp only [m16, square_eq, ← pow_two, ← pow_mul]
    rfl
  intro i
  rw [iter 16, sixteen]
  change |∑ j : Fin 15, m16 i j * w n j| ≤ 1966352 * V
  calc
    _ ≤ ∑ j : Fin 15, |m16 i j * w n j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 15, |m16 i j| * V := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (h j) (abs_nonneg _)
    _ = (∑ j : Fin 15, |m16 i j|) * V := (Finset.sum_mul _ _ _).symm
    _ ≤ 1966352 * V := mul_le_mul_of_nonneg_right (cap i) hV

private theorem growth16 (n : ℕ) : 1966352 * u n < u (n+16) := by
  have grow (k : ℕ) : 99^k * u n ≤ 40^k * u (n+k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have h := (growth (n+k)).2.1
      calc
        99^(k+1)*u n = 99*(99^k*u n) := by ring
        _ ≤ 99*(40^k*u (n+k)) := by linarith
        _ = 40^k*(99*u (n+k)) := by ring
        _ ≤ 40^k*(40*u (n+k+1)) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = 40^(k+1)*u (n+(k+1)) := by ring
  have h := grow 16
  have hp := (growth n).1
  norm_num at h
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem initialMinors : ∀ t : Fin 16, ∀ i : Fin 15,
    2 * |w (39+t.val) i| < u (39+t.val) := by decide +kernel

/-- Every residue class modulo 16 starts in the verified interval from 39 to 54. -/
private theorem bounded (n : ℕ) (hn : 39 ≤ n) : ∀ i : Fin 15, 2*|w n i| < u n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : n < 55
    · obtain ⟨t,ht⟩ : ∃ t : Fin 16, n=39+t.val := ⟨⟨n-39, by omega⟩, by simp; omega⟩
      rw [ht]
      exact initialMinors t
    · obtain ⟨k,rfl⟩ : ∃ k, n=k+16 := ⟨n-16, by omega⟩
      have hk := ih k (by omega) (by omega)
      let V := (u k-1)/2
      have hv : 0 ≤ V := by dsimp [V]; have := (growth k).1; omega
      have hw (i : Fin 15) : |w k i| ≤ V := by dsimp [V]; have := hk i; omega
      intro i
      have hb := block k V hv hw i
      have hg := growth16 k
      dsimp [V] at hb
      omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem initialWindow : ∀ n : Fin 39,
    -u n.val ≤ 2*(u n.val*u (n.val+2)-(u (n.val+1))^2) ∧
    2*(u n.val*u (n.val+2)-(u (n.val+1))^2) < u n.val := by decide +kernel

private theorem window (n : ℕ) :
    -u n ≤ 2*(u n*u (n+2)-(u (n+1))^2) ∧ 2*(u n*u (n+2)-(u (n+1))^2) < u n := by
  by_cases hn : n < 39
  · exact initialWindow ⟨n,hn⟩
  · have h := bounded n (by omega) 0
    change 2*|u n*u (n+2)-u (n+1)*u (n+1)| < u n at h
    rw [← sq] at h
    cases abs_cases (u n*u (n+2)-(u (n+1))^2) with
    | inl h' => rw [h'.1] at h; constructor <;> linarith [h'.2]
    | inr h' => rw [h'.1] at h; constructor <;> linarith [h'.2]

open OMA.S_oeis_a021004 PowerSeries

private theorem rounds_to_u (n : ℕ) : a n = u n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih0 ih1 =>
    rw [a, ih0, ih1, Int.ceil_eq_iff]
    have pos : 0 < (u n : ℚ) := by exact_mod_cast (growth n).1
    have lo : -(u n : ℚ) ≤ 2 * ((u n : ℚ) * u (n+2) - (u (n+1) : ℚ)^2) := by
      exact_mod_cast (window n).1
    have hi : 2 * ((u n : ℚ) * u (n+2) - (u (n+1) : ℚ)^2) < u n := by
      exact_mod_cast (window n).2
    constructor
    · rw [lt_sub_iff_add_lt, lt_div_iff₀ pos]
      linarith
    · rw [sub_le_iff_le_add, div_le_iff₀ pos]
      linarith

private theorem finish : type_of% @OMA.S_oeis_a021004.main := by
  simp_rw [rounds_to_u]
  have recurrenceAt (n : ℕ) (hn : 6 ≤ n) :
      u n = 2*u (n-1)+u (n-2)+u (n-3)-u (n-4)-u (n-6) := by
    obtain ⟨k,rfl⟩ : ∃ k, n = k+6 := ⟨n-6, by omega⟩
    simpa using recurrence k
  refine ⟨recurrenceAt, ?_⟩
  let A : ℚ⟦X⟧ := mk fun n => (u n : ℚ)
  change A * _ = _
  have den : A*(1-2*X-X^2-X^3+X^4+X^6) =
      A-(A*X^1+A*X^1)-A*X^2-A*X^3+A*X^4+A*X^6 := by ring
  have num : 4+2*(X : ℚ⟦X⟧)+X^2-2*X^3-X^4-2*X^5 =
      PowerSeries.C (4:ℚ)*X^0+PowerSeries.C (2:ℚ)*X^1+PowerSeries.C (1:ℚ)*X^2-PowerSeries.C (2:ℚ)*X^3-PowerSeries.C (1:ℚ)*X^4-PowerSeries.C (2:ℚ)*X^5 := by
    simp only [map_ofNat,map_one]
    ring
  rw [den,num]
  ext n
  simp only [map_sub,map_add,coeff_C_mul_X_pow]
  simp only [coeff_mul_X_pow',A,coeff_mk]
  by_cases small : n < 6
  · have u0 : u 0 = 4 := by decide
    have u1 : u 1 = 10 := by decide
    have u2 : u 2 = 25 := by decide
    have u3 : u 3 = 62 := by decide
    have u4 : u 4 = 154 := by decide
    have u5 : u 5 = 383 := by decide
    interval_cases n <;> norm_num [u0,u1,u2,u3,u4,u5]
  · simp (disch := omega) only [if_pos,if_neg]
    have h : (u n : ℚ) = 2*u (n-1)+u (n-2)+u (n-3)-u (n-4)-u (n-6) := by
      exact_mod_cast recurrenceAt n (by omega)
    linarith

end A021004Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a021004.main :=
  A021004Proof.finish
