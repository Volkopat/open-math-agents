import OMAStatements.S_oeis_a334765
import Mathlib.Tactic

open OMA.S_oeis_a334765

namespace DigitRuns

private def ones (n : ℕ) := (Nat.digits 2 n).sum

private lemma ones_step (n : ℕ) : ones n = n%2 + ones (n/2) := by
  by_cases h : n=0
  · subst n; simp [ones]
  · unfold ones
    rw [Nat.digits_eq_cons_digits_div (by decide) h, List.sum_cons]

private lemma balanced_step (n : ℕ) :
    balancedSum n = (n:ℤ) - 3*((n+1)/3 : ℕ) + balancedSum ((n+1)/3) := by
  by_cases h : n=0
  · subst n; norm_num
  · rw [balancedSum]; simp [h]

private lemma stable_trit (n : ℕ) (h : n%3 ≠ 1) :
    balancedSum (n+1) = balancedSum n + 1 := by
  have q : (n+1+1)/3=(n+1)/3 := by omega
  rw [balanced_step (n+1), balanced_step n, q]
  push_cast
  ring

private lemma even_bits (k : ℕ) : ones (2*k) = ones k := by
  rw [ones_step (2*k)]
  simp

private lemma odd_bits (k : ℕ) : ones (2*k+1) = 1 + ones k := by
  rw [ones_step (2*k+1), show (2*k+1)/2 = k by omega, show (2*k+1)%2 = 1 by omega]

-- A fall of one in the binary digit sum forces the two lowest bits to be 11.
private lemma binary_fall (n : ℕ) (h : (ones (n+1) : ℤ) = ones n - 1) : n%4=3 := by
  by_contra hn
  obtain ⟨k, hk⟩ : ∃ k, n=4*k ∨ n=4*k+1 ∨ n=4*k+2 := ⟨n/4, by omega⟩
  rcases hk with rfl | rfl | rfl
  · rw [show 4*k=2*(2*k) by omega] at h
    simp only [odd_bits, even_bits, Nat.cast_add, Nat.cast_one] at h
    omega
  · rw [show 4*k+1+1=2*(2*k+1) by omega, show 4*k+1=2*(2*k)+1 by omega,
        even_bits, odd_bits, odd_bits, even_bits] at h
    omega
  · rw [show 4*k+2=2*(2*k+1) by omega, odd_bits, even_bits] at h
    omega

private lemma match_value {n : ℕ} (h : digitMatch n=true) : (ones n:ℤ) = -balancedSum n :=
  of_decide_eq_true h

private lemma no_four (n : ℕ) : ¬ (∀ i : Fin 4, digitMatch (n+i.val)=true) := by
  intro hm
  have step (j : ℕ) (hj : j<3) : (n+j)%3=1 ∨ (n+j)%4=3 := by
    by_cases ht : (n+j)%3=1
    · exact Or.inl ht
    · right
      have ha := match_value (hm ⟨j, by omega⟩)
      have hb := match_value (hm ⟨j+1, by omega⟩)
      change (ones (n+j):ℤ) = -balancedSum (n+j) at ha
      change (ones (n+j+1):ℤ) = -balancedSum (n+j+1) at hb
      rw [stable_trit _ ht] at hb
      exact binary_fall _ (by omega)
  have h0 := step 0 (by decide)
  have h1 := step 1 (by decide)
  have h2 := step 2 (by decide)
  omega

-- Sixteen binary digits cover the finite range in the other three assertions.
private def bits : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d+1, n => n%2 + bits d (n/2)

private def trits : ℕ → ℕ → ℤ
  | 0, _ => 0
  | d+1, n => (n:ℤ) - 3*((n+1)/3 : ℕ) + trits d ((n+1)/3)

private lemma bounds (d n : ℕ) (h : n<2^d) :
    bits d n = ones n ∧ trits d n = balancedSum n := by
  induction d generalizing n with
  | zero =>
    have hn : n=0 := by simpa using h
    subst n
    have hz : balancedSum 0 = 0 := by rw [balancedSum, if_pos rfl]
    norm_num [bits, trits, ones, hz]
  | succ d ih =>
    rw [pow_succ] at h
    have h1 := (ih (n/2) (by omega)).1
    have h2 := (ih ((n+1)/3) (by omega)).2
    exact ⟨(congrArg (n%2 + ·) h1).trans (ones_step n).symm,
      (congrArg ((n:ℤ)-3*((n+1)/3 : ℕ) + ·) h2).trans (balanced_step n).symm⟩

private def flag (n : ℕ) : Bool := decide ((bits 16 n : ℤ) = -trits 16 n)

private lemma flag_eq (n : ℕ) (h : n<65536) : flag n = digitMatch n := by
  have h' : n<2^16 := h
  simp only [flag, (bounds 16 n h').1, (bounds 16 n h').2, digitMatch, ones]

private def triple (n : ℕ) := flag n && flag (n+1) && flag (n+2)

-- Evaluate finite counts in a balanced tree. Each leaf checks one starting index.
private def block (f : ℕ → Bool) (s : ℕ) : ℕ → ℕ
  | 0 => if f s then 1 else 0
  | d+1 => block f s d + block f (s + 2^d) d

private lemma count_block (f : ℕ → Bool) (s d : ℕ) :
    (List.range (s+2^d)).countP f = (List.range s).countP f + block f s d := by
  induction d generalizing s with
  | zero =>
    change (List.range (Nat.succ s)).countP f = (List.range s).countP f + (if f s then 1 else 0)
    rw [List.range_succ, List.countP_append]
    cases h : f s <;> simp [h]
  | succ d ih =>
    rw [show s+2^(d+1)=s+2^d+2^d by ring, ih (s+2^d), ih s, block, Nat.add_assoc]

private def checked (n terms : ℕ) : Prop :=
  (List.range n).countP flag = terms ∧ (List.range n).countP triple = 0

private lemma extend (s d c extra : ℕ) (old : checked s c)
    (v : block flag s d = extra ∧ block triple s d = 0) : checked (s+2^d) (c+extra) := by
  constructor
  · rw [count_block, old.1, v.1]
  · rw [count_block, old.2, v.2, Nat.zero_add]

-- Each certificate covers at most 1,024 starts so the kernel can release its
-- temporary evaluation data before verifying the next interval.
section

private lemma c0 : checked 0 0 := ⟨rfl, rfl⟩

set_option maxHeartbeats 2000000 in
private lemma c1024 : checked 1024 8 :=
  extend 0 10 0 8 c0 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c2048 : checked 2048 19 :=
  extend 1024 10 8 11 c1024 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c3072 : checked 3072 20 :=
  extend 2048 10 19 1 c2048 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c4096 : checked 4096 26 :=
  extend 3072 10 20 6 c3072 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c5120 : checked 5120 37 :=
  extend 4096 10 26 11 c4096 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c6144 : checked 6144 38 :=
  extend 5120 10 37 1 c5120 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c7168 : checked 7168 39 :=
  extend 6144 10 38 1 c6144 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c8192 : checked 8192 39 :=
  extend 7168 10 39 0 c7168 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c9216 : checked 9216 39 :=
  extend 8192 10 39 0 c8192 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c10240 : checked 10240 46 :=
  extend 9216 10 39 7 c9216 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c11264 : checked 11264 57 :=
  extend 10240 10 46 11 c10240 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c12288 : checked 12288 58 :=
  extend 11264 10 57 1 c11264 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c13312 : checked 13312 64 :=
  extend 12288 10 58 6 c12288 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c14336 : checked 14336 65 :=
  extend 13312 10 64 1 c13312 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c15360 : checked 15360 65 :=
  extend 14336 10 65 0 c14336 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c16384 : checked 16384 65 :=
  extend 15360 10 65 0 c15360 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c17408 : checked 17408 95 :=
  extend 16384 10 65 30 c16384 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c18432 : checked 18432 97 :=
  extend 17408 10 95 2 c17408 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c19456 : checked 19456 100 :=
  extend 18432 10 97 3 c18432 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c20480 : checked 20480 100 :=
  extend 19456 10 100 0 c19456 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c21504 : checked 21504 100 :=
  extend 20480 10 100 0 c20480 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c22528 : checked 22528 101 :=
  extend 21504 10 100 1 c21504 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c23552 : checked 23552 101 :=
  extend 22528 10 101 0 c22528 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c24576 : checked 24576 101 :=
  extend 23552 10 101 0 c23552 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c25600 : checked 25600 102 :=
  extend 24576 10 101 1 c24576 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c26624 : checked 26624 102 :=
  extend 25600 10 102 0 c25600 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c27648 : checked 27648 102 :=
  extend 26624 10 102 0 c26624 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c28672 : checked 28672 102 :=
  extend 27648 10 102 0 c27648 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c29696 : checked 29696 105 :=
  extend 28672 10 102 3 c28672 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c30720 : checked 30720 111 :=
  extend 29696 10 105 6 c29696 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c31744 : checked 31744 114 :=
  extend 30720 10 111 3 c30720 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c32768 : checked 32768 115 :=
  extend 31744 10 114 1 c31744 (by decide +kernel)

set_option maxHeartbeats 2000000 in
private lemma c32770 : checked 32770 115 :=
  extend 32768 1 115 0 c32768 (by decide +kernel)

end

private lemma how_many : (List.range 32770).countP digitMatch = 115 := by
  have h := List.countP_congr (l := List.range 32770) (p := digitMatch) (q := flag)
    (fun n hn => by rw [flag_eq n (by have := List.mem_range.mp hn; omega)])
  exact h.trans c32770.1

private lemma first_three (i : Fin 3) : digitMatch (32770+i.val) = true := by
  rw [← flag_eq _ (by have := i.isLt; omega)]
  fin_cases i <;> decide +kernel

private lemma no_earlier (n : Fin 32770) : ¬ (∀ i : Fin 3, digitMatch (n.val+i.val)=true) := by
  intro hm
  have hf (i : Fin 3) : flag (n.val+i.val) = true := by
    rw [flag_eq _ (by have := i.isLt; have := n.isLt; omega)]
    exact hm i
  apply List.countP_eq_zero.mp c32770.2 n.val (List.mem_range.mpr n.isLt)
  simp [triple, (show flag n.val=true from hf 0), (show flag (n.val+1)=true from hf 1),
    (show flag (n.val+2)=true from hf 2)]

end DigitRuns

theorem OMA.solution : type_of% @OMA.S_oeis_a334765.main :=
  ⟨DigitRuns.no_four, DigitRuns.first_three, DigitRuns.no_earlier, DigitRuns.how_many⟩
