import FormalConjectures.OEIS.«182510»

/-! # Lifting zeros across a dyadic block

The signed XOR forcing gains one binary digit of accuracy in a linear
convolution. Four convolutions suffice for exact recovery, and the final
correction reduces to a signed count of individual bits. A separate
four-by-four table controls translates of the eight initial roots.

The period argument and the finite-prefix certificate are adapted from
@marcusbuffett's reduction R1 for this conjecture.
-/

-- Credit: @MrSeizy
namespace OMA.R_OeisA182510_conjecture1_R2

open OeisA182510

private theorem xor_mod_two (x y : ℤ) : Int.xor x y ≡ x + y [ZMOD 2] := by
  induction x using Int.bitCasesOn with
  | h b x =>
    induction y using Int.bitCasesOn with
    | h c y =>
      rw [Int.lxor_bit]
      cases b <;> cases c <;> simp [Int.bit_val, Int.ModEq]
      all_goals omega

private theorem bit_translate (k : ℕ) (b : Bool) (x s : ℤ) :
    Int.bit b x + 2^(k+1) * s = Int.bit b (x + 2^k * s) := by
  simp only [Int.bit_val, pow_succ]
  ring

theorem xor_translate (k : ℕ) (x y s t : ℤ) :
    Int.xor (x + 2^k*s) (y + 2^k*t) ≡ Int.xor x y + 2^k*(s+t) [ZMOD 2^(k+1)] := by
  induction k generalizing x y with
  | zero =>
    norm_num only [pow_zero, one_mul, zero_add, pow_one]
    apply (xor_mod_two (x+s) (y+t)).trans
    have h := (xor_mod_two x y).symm.add_right (s+t)
    convert h using 1
    ring
  | succ k ih =>
    induction x using Int.bitCasesOn with
    | h b x =>
      induction y using Int.bitCasesOn with
      | h c y =>
        rw [bit_translate k b x s, bit_translate k c y t, Int.lxor_bit, Int.lxor_bit]
        have h := Int.ModEq.mul_left' (c := 2) (ih x y)
        have h' := h.add_right (cond (b ^^ c) (1:ℤ) 0)
        simp only [Int.bit_val]
        convert h' using 1 <;> ring

private theorem lifts_again (k : ℕ) (s : ℕ → ℤ)
    (hs : ∀ n, a (n + 3*2^k) = a n + (2:ℤ)^k * s n) :
    (∀ n, s (n+3) % 2 = s n % 2) ∧
    ∃ s' : ℕ → ℤ, ∀ n, a (n + 3*2^(k+1)) = a n + (2:ℤ)^(k+1) * s' n := by
  let M : ℤ := 2^k
  let P : ℕ := 3*2^k
  have hM : M ≠ 0 := by dsimp [M]; positivity
  have hP : (P : ℤ) = M*3 := by dsimp [P,M]; ring
  have shift : ∀ n, a (n+P) = a n + M*s n := hs
  have step (n : ℕ) : s (n+2) % 2 = (s (n+1) + 3 - s n) % 2 := by
    have hx := xor_translate k (a (n+1)) (n+2 : ℤ) (s (n+1)) 3
    obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp hx
    change (Int.xor (a (n+1)) (n+2) + M*(s (n+1)+3)) -
      Int.xor (a (n+1) + M*s (n+1)) ((n:ℤ)+2+M*3) = 2^(k+1)*c at hc
    have hrec : a (n+2+P) =
        Int.xor (a (n+1+P)) ((n:ℤ)+2+M*3) - a (n+P) := by
      rw [show n+2+P = (n+P)+2 by omega, show n+1+P = (n+P)+1 by omega, a]
      push_cast
      rw [hP]
      congr 2
      ring
    rw [shift (n+2), shift (n+1), shift n] at hrec
    change Int.xor (a (n+1)) (n+2) - a n + M*s (n+2) = _ at hrec
    rw [pow_succ] at hc
    change _ = M * 2 * c at hc
    have heq : M * s (n+2) = M * (s (n+1) + 3 - s n - 2*c) := by
      linear_combination hrec - hc
    have := mul_left_cancel₀ hM heq
    omega
  have three (n : ℕ) : s (n+3) % 2 = s n % 2 := by
    have h := step n
    have h' := step (n+1)
    change s (n+3) % 2 = (s (n+2) + 3 - s (n+1)) % 2 at h'
    omega
  refine ⟨three, fun n => (s n + s (n+P)) / 2, ?_⟩
  intro n
  have loop (t : ℕ) : s (n + 3*t) % 2 = s n % 2 := by
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, ← Nat.add_assoc, three, ih]
  have hp : s (n+P) % 2 = s n % 2 := loop (2^k)
  have he : s n + s (n+P) = 2 * ((s n + s (n+P))/2) := by omega
  have ht : n + 3*2^(k+1) = n+P+P := by dsimp [P]; rw [pow_succ]; omega
  rw [ht, shift (n+P), shift n, pow_succ]
  change a n + M*s n + M*s (n+P) = a n + M*2*((s n + s (n+P))/2)
  linear_combination M * he

theorem lifts (k : ℕ) : ∃ s : ℕ → ℤ, ∀ n, a (n+3*2^k) = a n + (2:ℤ)^k * s n := by
  induction k with
  | zero => exact ⟨fun n => a (n+3) - a n, by simp⟩
  | succ k ih =>
    obtain ⟨s, hs⟩ := ih
    exact (lifts_again k s hs).2

/-- Exact change in a signed XOR after modifying only the upper digits. -/
theorem upper_digits (k : ℕ) (x y s t : ℤ) :
    let M : ℤ := 2^k
    Int.xor (x+M*s) (y+M*t) - Int.xor x y =
      M * (Int.xor (x/M+s) (y/M+t) - Int.xor (x/M) (y/M)) := by
  dsimp only
  induction k generalizing x y with
  | zero => simp
  | succ k ih =>
    induction x using Int.bitCasesOn with
    | h b x =>
      induction y using Int.bitCasesOn with
      | h c y =>
        have half (d : Bool) (z : ℤ) : Int.bit d z / 2^(k+1) = z / 2^k := by
          rw [pow_succ', ← Int.ediv_ediv_of_nonneg (by decide : (0:ℤ) ≤ 2)]
          congr 1
          cases d <;> simp [Int.bit_val]
          all_goals omega
        rw [half,half,bit_translate,bit_translate,Int.lxor_bit,Int.lxor_bit]
        simp only [Int.bit_val, pow_succ]
        linear_combination 2 * ih x y

private theorem xor_zero_right (x : ℤ) : Int.xor x 0 = x := by
  cases x <;> simp [Int.xor]

/-- The XOR forcing gains a binary digit of precision. -/
theorem force_gain {x y : ℤ} (s : ℤ) (k : ℕ)
    (h : x ≡ y [ZMOD (2:ℤ)^k]) :
    Int.xor x s - x ≡ Int.xor y s - y [ZMOD (2:ℤ)^(k+1)] := by
  obtain ⟨c,hc⟩ := Int.modEq_iff_dvd.mp h
  have he : y = x + 2^k*c := by linarith
  have ht := (xor_translate k x s c 0).sub_right y
  simpa [he,add_sub_add_right_eq_sub] using ht.symm

private theorem force_exact {x y : ℤ} {s : ℕ} (k : ℕ)
    (h : x ≡ y [ZMOD (2:ℤ)^k]) (hs : (s : ℤ) < 2^k) :
    Int.xor x s - x = Int.xor y s - y := by
  obtain ⟨c,hc⟩ := Int.modEq_iff_dvd.mp h
  have he : y = x + 2^k*c := by linarith
  have hh := upper_digits k x s c 0
  have hdiv : (s:ℤ) / 2^k = 0 := Int.ediv_eq_zero_of_lt (by positivity) hs
  simp [hdiv,xor_zero_right] at hh
  rw [he]
  linarith

/-- The Green function of the homogeneous recurrence is periodic with period six.
The summand indexed by the last element of the range has weight zero. -/
private theorem green (P : ℕ) (f : ℕ → ℤ) :
    let g (i : ℕ) : ℤ := match i % 6 with
      | 1 | 2 => 1 | 4 | 5 => -1 | _ => 0
    let e (j : ℕ) := Int.xor (f (j+1)) ((P+j+2:ℕ):ℤ) - f (j+1)
    let L (r : ℕ) := g (r+2)*a P + g r*a (P+1) +
      ∑ j ∈ Finset.range r, g (r+5*(j+1)) * e j
    L 0 = a P ∧ L 1 = a (P+1) ∧ ∀ i, L (i+2) = L (i+1) - L i + e i := by
  intro g e L
  have hg (j : ℕ) : g (j+2) = g (j+1) - g j := by
    dsimp [g]
    rw [Nat.add_mod j 2, Nat.add_mod j 1]
    have := Nat.mod_lt j (by decide : 0 < 6)
    interval_cases j % 6 <;> decide
  have hz (i : ℕ) : g (i+1+5*(i+1)) = 0 := by
    change (match (i+1+5*(i+1)) % 6 with
      | 1 | 2 => (1:ℤ) | 4 | 5 => -1 | _ => 0) = 0
    rw [show (i+1+5*(i+1))%6 = 0 by omega]
    rfl
  have h1 (i : ℕ) : g (i+2+5*(i+1)) = 1 := by
    dsimp [g]
    rw [show (i+2+5*(i+1))%6 = 1 by omega]
    rfl
  refine ⟨by simp [L,g], by simp [L,g], ?_⟩
  intro i
  dsimp only [L]
  rw [Finset.sum_range_succ (n := i+1), Finset.sum_range_succ (n := i),
    Finset.sum_range_succ (n := i), hz (i+1), hz i, h1]
  have hsum : (∑ j ∈ Finset.range i, g (i+2+5*(j+1))*e j) =
      (∑ j ∈ Finset.range i, g (i+1+5*(j+1))*e j) -
      ∑ j ∈ Finset.range i, g (i+5*(j+1))*e j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [show i+2+5*(j+1) = (i+5*(j+1))+2 by omega, hg,
      show i+1+5*(j+1) = (i+5*(j+1))+1 by omega]
    ring
  rw [hsum, hg (i+2), hg i]
  ring

/-- Four explicit convolutions of the lower block recover the exact signed upper
block. All the sums in each pass depend only on values from the preceding pass. -/
theorem four_sweeps (k : ℕ) :
    let P := 3*2^k
    let g (i : ℕ) : ℤ := match i % 6 with
      | 1 | 2 => 1 | 4 | 5 => -1 | _ => 0
    let L (f : ℕ → ℤ) (r : ℕ) := g (r+2)*a P + g r*a (P+1) +
      ∑ j ∈ Finset.range r, g (r+5*(j+1)) *
        (Int.xor (f (j+1)) ((P+j+2:ℕ):ℤ) - f (j+1))
    ∀ r < P, L (L a) r ≡ a (P+r) [ZMOD (2:ℤ)^(k+2)] ∧
      L (L (L a)) r ≡ a (P+r) [ZMOD (2:ℤ)^(k+3)] ∧
      L (L (L (L a))) r = a (P+r) := by
  intro P g L
  have spec (f : ℕ → ℤ) := green P f
  change ∀ f, L f 0 = a P ∧ L f 1 = a (P+1) ∧ ∀ i,
    L f (i+2) = L f (i+1) - L f i +
      (Int.xor (f (i+1)) ((P+i+2:ℕ):ℤ) - f (i+1)) at spec
  have recA (i : ℕ) : a (P+(i+2)) = a (P+(i+1)) - a (P+i) +
      (Int.xor (a (P+(i+1))) ((P+i+2:ℕ):ℤ) - a (P+(i+1))) := by
    rw [show P+(i+2) = (P+i)+2 by omega, a]
    push_cast
    rw [Nat.add_assoc]
    ring
  have gain (f : ℕ → ℤ) (m : ℕ)
      (h : ∀ i < P, f i ≡ a (P+i) [ZMOD (2:ℤ)^m]) :
      ∀ i < P, L f i ≡ a (P+i) [ZMOD (2:ℤ)^(m+1)] := by
    intro i
    induction i using Nat.twoStepInduction with
    | zero => simp [(spec f).1]
    | one => simp [(spec f).2.1]
    | more i h0 h1 =>
      intro hi
      rw [(spec f).2.2, recA]
      exact ((h1 (by omega)).sub (h0 (by omega))).add
        (force_gain _ _ (h (i+1) (by omega)))
  obtain ⟨s,hs⟩ := lifts k
  have h0 (i : ℕ) (_ : i < P) : a i ≡ a (P+i) [ZMOD (2:ℤ)^k] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨s i, by rw [Nat.add_comm P, hs]; ring⟩
  have h2 := gain _ _ (gain _ _ h0)
  have h3 := gain _ _ h2
  intro r hr
  refine ⟨h2 r hr,h3 r hr,?_⟩
  suffices exactRow : ∀ i < P, L (L (L (L a))) i = a (P+i) from exactRow r hr
  intro i
  induction i using Nat.twoStepInduction with
  | zero => simp [(spec _).1]
  | one => simp [(spec _).2.1]
  | more i h0 h1 =>
    intro hi
    rw [(spec _).2.2, recA, h0 (by omega), h1 (by omega)]
    congr 1
    apply force_exact (k+3) (h3 (i+1) (by omega))
    have hnat : P+i+2 < 2^(k+3) := by
      dsimp only [P] at hi ⊢
      rw [pow_add]
      omega
    exact_mod_cast hnat

private theorem xor_one (z : ℤ) : Int.xor z 1 = z + 1 - 2*(z%2) := by
  induction z using Int.bitCasesOn with
  | h b z =>
    change Int.xor (Int.bit b z) (Int.bit true 0) = _
    rw [Int.lxor_bit, xor_zero_right]
    cases b <;> simp [Int.bit_val]
    all_goals omega

/-- When two inputs already agree below a mask's leading bit, the
difference of their forcings is exactly a signed difference of two bits. -/
theorem last_bit (w : ℕ) (x y s : ℤ) (hs : 0 ≤ s) (hu : s < 2*2^w)
    (h : x ≡ y [ZMOD (2:ℤ)^w]) :
    let Q : ℤ := 2^w
    (Int.xor y s - y) - (Int.xor x s - x) =
      2*Q * (if Q ≤ s then (x/Q)%2 - (y/Q)%2 else 0) := by
  intro Q
  have hQ : 0 < Q := by dsimp [Q]; positivity
  obtain ⟨t,ht⟩ := Int.modEq_iff_dvd.mp h
  change y - x = Q*t at ht
  have he : y = x+Q*t := by linarith
  have hdiv : y/Q = x/Q+t := by simp [he,Int.add_mul_ediv_left,ne_of_gt hQ]
  have hh := upper_digits w x s t 0
  change Int.xor (x+Q*t) (s+Q*0) - Int.xor x s =
    Q*(Int.xor (x/Q+t) (s/Q+0) - Int.xor (x/Q) (s/Q)) at hh
  simp only [mul_zero,add_zero,← he,← hdiv] at hh
  by_cases hb : Q ≤ s
  · have h1 : s/Q = 1 := by
      apply (Int.ediv_eq_iff_of_pos hQ).2
      rw [one_mul]
      exact ⟨hb,by linarith [show s < 2*Q from hu]⟩
    rw [h1,xor_one,xor_one] at hh
    rw [if_pos hb]
    linear_combination hh - ht + Q * (hdiv)
  · have h0 := Int.ediv_eq_zero_of_lt hs (by omega : s < Q)
    rw [h0,xor_zero_right,xor_zero_right] at hh
    rw [if_neg hb,mul_zero]
    linear_combination hh - ht + Q * hdiv

/-- The error in the third convolution equals a signed count of bits, scaled
by eight times the block modulus. Only masks with the leading bit set contribute. -/
theorem balance (k : ℕ) :
    let P := 3*2^k
    let Q : ℤ := 2^(k+2)
    let g (i : ℕ) : ℤ := match i % 6 with
      | 1 | 2 => 1 | 4 | 5 => -1 | _ => 0
    let L (f : ℕ → ℤ) (r : ℕ) := g (r+2)*a P + g r*a (P+1) +
      ∑ j ∈ Finset.range r, g (r+5*(j+1)) *
        (Int.xor (f (j+1)) ((P+j+2:ℕ):ℤ) - f (j+1))
    let U := L (L a)
    let V := L U
    ∀ r < P, V r - a (P+r) = (2*Q) * ∑ j ∈ Finset.range r,
        g (r+5*(j+1)) * (if Q ≤ (P+j+2:ℕ) then
          (V (j+1)/Q)%2 - (U (j+1)/Q)%2 else 0) := by
  intro P Q g L U V r hr
  have rows := four_sweeps k
  change ∀ i < P, U i ≡ a (P+i) [ZMOD Q] ∧
    V i ≡ a (P+i) [ZMOD (2:ℤ)^(k+3)] ∧ L V i = a (P+i) at rows
  have hq : (2:ℤ)^(k+3) = 2*Q := by change 2^((k+2)+1) = 2*2^(k+2); ring
  let D (j : ℕ) := if Q ≤ (P+j+2:ℕ) then (V (j+1)/Q)%2 - (U (j+1)/Q)%2 else 0
  let E (f : ℕ → ℤ) (j : ℕ) := Int.xor (f (j+1)) ((P+j+2:ℕ):ℤ) - f (j+1)
  have diff (j : ℕ) (hj : j < r) : E U j - E V j = 2*Q * D j := by
    obtain ⟨hU,hV,_⟩ := rows (j+1) (by omega)
    rw [hq] at hV
    have h := hV.of_dvd (show Q ∣ 2*Q from dvd_mul_left _ _)
    apply last_bit (k+2) _ _ _ (by positivity) _ (h.trans hU.symm)
    have hbound : P+j+2 < 2*2^(k+2) := by
      dsimp only [P] at hr ⊢
      rw [pow_add]
      omega
    exact_mod_cast hbound
  let S := ∑ j ∈ Finset.range r, g (r+5*(j+1))*D j
  have heq : V r - L V r = (2*Q)*S := by
    change (_ + ∑ j ∈ Finset.range r, _ * E U j) -
      (_ + ∑ j ∈ Finset.range r, _ * E V j) = _ * ∑ j ∈ Finset.range r, _ * D j
    rw [add_sub_add_left_eq_sub,← Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_sub,diff j (Finset.mem_range.mp hj)]
    ring
  rwa [(rows r hr).2.2] at heq

/-- A zero at a translated initial root forces either an exceptional boundary
value or a zero immediately before the block. -/
theorem inherited (k : ℕ) (hk : 8 ≤ k) (r : ℕ)
    (hr : r ∈ ({0,6,11,23,36,42,48,54} : Finset ℕ))
    (hz : a (3*2^k+r) = 0) :
    let M : ℤ := 2^k
    let P := 3*2^k
    let A := a P / M
    let B := (a (P+1)-1) / M
    (A = 0 ∨ A = if B%4 = 1 then -12 else 4) ∨ a (P-1) = 0 := by
  intro M P A B
  have hM : 256 ≤ M := by
    exact (show (2:ℤ)^8 ≤ 2^k from pow_le_pow_right₀ (by decide) hk)
  have hMn : M ≠ 0 := by omega
  obtain ⟨s,hs⟩ := lifts k
  have sh (i : ℕ) : a (P+i) = a i + M*s i := by simpa [Nat.add_comm P] using hs i
  have ha : A = s 0 := by simp [A,show a P = M*s 0 by simpa [a_0] using sh 0,hMn]
  have hb : B = s 1 := by simp [B,sh 1,a_1,hMn]
  let Z : Finset ℕ := {0,6,11,23,36,42,48,54}
  have data : ∀ i : Fin 55, (-256 ≤ a i ∧ a i < 256) ∧ (i.val ∈ Z → a i = 0) := by
    decide
  have cut (i : ℕ) (hi : i < 55) : a i / M = a i / 256 := by
    obtain ⟨hl,hu⟩ : -256 ≤ a i ∧ a i < 256 := (data ⟨i,hi⟩).1
    by_cases h : 0 ≤ a i
    · rw [Int.ediv_eq_zero_of_lt h (by omega),Int.ediv_eq_zero_of_lt h (by omega)]
    · have hdiv (m : ℤ) (hm : 256 ≤ m) : a i / m = -1 := by
        exact Int.ediv_eq_neg_one_of_neg_of_le (by omega) (by omega)
      rw [hdiv M hM,hdiv 256 (by decide)]
  have recS (i : ℕ) (hi : i+2 ≤ 54) :
      s (i+2) = Int.xor (a (i+1)/256+s (i+1)) 3 - a (i+1)/256 - s i := by
    have hu := upper_digits k (a (i+1)) (i+2:ℤ) (s (i+1)) 3
    change Int.xor (a (i+1)+M*s (i+1)) ((i:ℤ)+2+M*3) - Int.xor (a (i+1)) (i+2:ℤ) =
      M * (Int.xor (a (i+1)/M+s (i+1)) (((i:ℤ)+2)/M+3) -
        Int.xor (a (i+1)/M) (((i:ℤ)+2)/M)) at hu
    have hdiv : ((i:ℤ)+2)/M = 0 := Int.ediv_eq_zero_of_lt (by positivity) (by omega)
    simp only [hdiv,zero_add,xor_zero_right,cut (i+1) (by omega)] at hu
    have hP : (P:ℤ) = M*3 := by dsimp [P,M]; ring
    have hfull := sh (i+2)
    rw [show P+(i+2) = (P+i)+2 by omega, a, show P+i+1=P+(i+1) by omega, sh (i+1),sh i] at hfull
    rw [a] at hfull
    push_cast at hfull
    rw [hP,show M*3+i+2 = (i:ℤ)+2+M*3 by ring] at hfull
    apply mul_left_cancel₀ hMn (b := s (i+2)) (c := _)
    linear_combination hu - hfull
  let T (c d : ℤ) (n : ℕ) := Nat.rec (motive := fun _ => ℤ × ℤ) (c,d)
    (fun i xy => (xy.2, Int.xor (a (i+1)/256+xy.2) 3 - a (i+1)/256 - xy.1)) n
  let c : Fin 4 := ⟨(A%4).toNat,by omega⟩
  let d : Fin 4 := ⟨(B%4).toNat,by omega⟩
  have hc : (c.val : ℤ) = A%4 := by dsimp [c]; omega
  have hd : (d.val : ℤ) = B%4 := by dsimp [d]; omega
  let u := A/4
  let v := B/4
  let w (i : ℕ) : ℤ := match i % 6 with
    | 0 => u | 1 => v | 2 => v-u | 3 => -u | 4 => -v | _ => u-v
  have hw (i : ℕ) : w (i+2) = w (i+1) - w i := by
    dsimp only [w]
    rw [Nat.add_mod i 2, Nat.add_mod i 1]
    have := Nat.mod_lt i (by decide : 0 < 6)
    interval_cases i % 6 <;> simp <;> ring
  let t (i : ℕ) := (T c.val d.val i).1
  have liftT (i : ℕ) : i ≤ 54 → s i = t i + 4*w i := by
    induction i using Nat.twoStepInduction with
    | zero =>
      intro _
      change s 0 = (c.val:ℤ) + 4*(A/4)
      omega
    | one =>
      intro _
      change s 1 = (d.val:ℤ) + 4*(B/4)
      omega
    | more i h0 h1 =>
      intro hi
      have tr : t (i+2) = Int.xor (a (i+1)/256+t (i+1)) 3 - a (i+1)/256 - t i := rfl
      rw [recS i hi,hw,tr,h0 (by omega),h1 (by omega),← add_assoc]
      have h := upper_digits 2 (a (i+1)/256+t (i+1)) 3 (w (i+1)) 0
      norm_num [xor_zero_right] at h
      linarith
  have table : ∀ c d : Fin 4, ∀ i : Fin 55, i.val ∈ Z →
      let z := (T c.val d.val i.val).1
      z%4 = 0 →
        (i.val%6 = 0 ∧ ((c.val:ℤ)-z = 0 ∨ (c.val:ℤ)-z = if d.val = 1 then -12 else 4)) ∨
        (i.val%6 = 5 ∧ z = 0 ∧ Int.xor c.val 3 = d.val) := by
    decide
  have hsmall : r < 55 := by simp at hr; omega
  have hzr := (data ⟨r,hsmall⟩).2 hr
  have hsr : s r = 0 := by
    have hh := sh r
    change a (P+r) = 0 at hz
    rw [hz,hzr,zero_add,eq_comm,mul_eq_zero] at hh
    exact hh.resolve_left hMn
  have ht := liftT r (by omega)
  have hit := table c d ⟨r,hsmall⟩ hr (show t r % 4 = 0 by omega)
  rcases hit with ⟨hmod,hh⟩ | ⟨hmod,hh⟩
  · left
    change r % 6 = 0 at hmod
    have he : w r = A/4 := by simp [w,hmod,u]
    have hA : A = (c.val:ℤ) - t r := by omega
    have hcond : (B%4 = 1) ↔ d.val = 1 := by omega
    rw [hA,if_congr hcond rfl rfl]
    exact hh
  · right
    change r % 6 = 5 at hmod
    have he : w r = A/4-B/4 := by simp [w,hmod,u,v]
    obtain ⟨ht0,hxor⟩ := hh
    change t r = 0 at ht0
    have hQ : A/4 = B/4 := by omega
    have h3 := upper_digits 2 c.val 3 (A/4) 0
    have hcd : (c.val:ℤ) / 4 = 0 := Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast c.isLt)
    norm_num [hcd,xor_zero_right,hxor] at h3
    have hax : (c.val:ℤ) + 4*(A/4) = A := by omega
    rw [hax] at h3
    have hBA : B = Int.xor A 3 := by omega
    have hh := upper_digits k 0 1 A 3
    have hm1 : (1:ℤ)/M = 0 := Int.ediv_eq_zero_of_lt (by decide) (by omega)
    change Int.xor (0+M*A) (1+M*3) - Int.xor 0 1 =
      M*(Int.xor (0/M+A) (1/M+3) - Int.xor (0/M) (1/M)) at hh
    simp only [hm1,Int.zero_ediv,zero_add] at hh
    have hh' : Int.xor (M*A) (1+M*3) - 1 = M*B := by
      rw [hBA]
      change Int.xor (M*A) (1+M*3) - 1 = M*(Int.xor A 3 - 0) at hh
      simpa using hh
    have hp : 0 < P := by dsimp [P]; positivity
    have hrec : a (P+1) = Int.xor (a P) ((P:ℤ)+1) - a (P-1) := by
      conv_lhs => rw [show P+1 = P-1+2 by omega, a]
      rw [show P-1+1 = P by omega]
      congr 2
      omega
    have hpz : (P:ℤ)+1 = 1+M*3 := by dsimp [P,M]; ring
    have hx : a P = M*A := by simpa [a_0,ha] using sh 0
    have hy : a (P+1) = 1+M*B := by simpa [a_1,hb] using sh 1
    rw [hx,hy,hpz] at hrec
    omega
private theorem batch {N L : ℕ} {x y u v : ℤ} (hx : a N = x) (hy : a (N+1) = y)
    (h : (List.range L).foldl (fun (s : ℤ × ℤ × Bool) j =>
        (s.2.1, Int.xor s.2.1 ((N+j+2 : ℕ) : ℤ) - s.1, s.2.2 && s.1 != 0))
      (x,y,true) = (u,v,true)) :
    a (N+L) = u ∧ a (N+L+1) = v ∧ ∀ n, N ≤ n → n < N+L → a n ≠ 0 := by
  let f := fun (s : ℤ × ℤ × Bool) (j : ℕ) =>
    (s.2.1, Int.xor s.2.1 ((N+j+2 : ℕ) : ℤ) - s.1, s.2.2 && s.1 != 0)
  let state (l : ℕ) := (List.range l).foldl f (x,y,true)
  have hs (l : ℕ) : (state l).1 = a (N+l) ∧ (state l).2.1 = a (N+l+1) ∧
      ((state l).2.2 = true → ∀ n, N ≤ n → n < N+l → a n ≠ 0) := by
    induction l with
    | zero => simp [state,hx,hy]; omega
    | succ l ih =>
      obtain ⟨ha,hb,hok⟩ := ih
      have hl : state (l+1) = f (state l) l := by simp [state, List.range_succ]
      rw [hl]
      simp only [f,ha,hb, Bool.and_eq_true, bne_iff_ne]
      refine ⟨rfl, ?_, ?_⟩
      · rw [show N+(l+1)+1 = (N+l)+2 by omega, a]
        push_cast
        rfl
      · rintro ⟨hflag, hnz⟩ n hN hn
        by_cases hh : n = N+l
        · simpa [hh] using hnz
        · exact hok hflag n hN (by omega)
  obtain ⟨ha,hb,hflag⟩ := hs L
  change state L = _ at h
  rw [h] at ha hb hflag
  exact ⟨ha.symm, hb.symm, hflag rfl⟩


private theorem extend {N L : ℕ} {x y u v : ℤ}
    (old : a N = x ∧ a (N+1) = y ∧ ∀ n, 55 ≤ n → n < N → a n ≠ 0)
    (h : (List.range L).foldl (fun (s : ℤ × ℤ × Bool) j =>
        (s.2.1, Int.xor s.2.1 ((N+j+2 : ℕ) : ℤ) - s.1, s.2.2 && s.1 != 0))
      (x,y,true) = (u,v,true)) :
    a (N+L) = u ∧ a (N+L+1) = v ∧ ∀ n, 55 ≤ n → n < N+L → a n ≠ 0 := by
  obtain ⟨hu,hv,hl⟩ := batch old.1 old.2.1 h
  refine ⟨hu,hv,fun n h₅₅ hn => ?_⟩
  by_cases hlt : n < N
  · exact old.2.2 n h₅₅ hlt
  · exact hl n (by omega) hn

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3200000 in
private theorem before_block : ∀ n, 55 ≤ n → n < 823 → a n ≠ 0 := by
  have b0 : a 55 = 73 ∧ a 56 = 113 ∧ ∀ n, 55 ≤ n → n < 55 → a n ≠ 0 :=
    ⟨by decide, by decide, by omega⟩
  have b1 := extend (N := 55) (L := 256) (u := -960) (v := 8088) b0 (by decide)
  have b2 := extend (N := 311) (L := 256) (u := -11713) (v := -3004) b1 (by decide)
  have b3 := extend (N := 567) (L := 256) (u := -8375) (v := -42383) b2 (by decide)
  exact b3.2.2

/-- The first normalized boundary coordinate avoids two explicitly specified integers. -/
def H1 : Prop :=
  ∀ k : ℕ, 8 ≤ k →
    let M : ℤ := 2^k
    let P := 3*2^k
    let A := a P / M
    let B := (a (P+1)-1) / M
    A ≠ 0 ∧ A ≠ (if B%4 = 1 then -12 else 4)

/-- For nonzero lower values surviving both divisibility filters, the predicted
quotient differs from the signed count obtained from one bit of two lower-block sums. -/
def H2 : Prop :=
  ∀ k : ℕ, 8 ≤ k →
    let P := 3*2^k
    let Q : ℤ := 2^(k+2)
    let g (i : ℕ) : ℤ := match i % 6 with
      | 1 | 2 => 1 | 4 | 5 => -1 | _ => 0
    let L (f : ℕ → ℤ) (r : ℕ) := g (r+2)*a P + g r*a (P+1) +
      ∑ j ∈ Finset.range r, g (r+5*(j+1)) *
        (Int.xor (f (j+1)) ((P+j+2:ℕ):ℤ) - f (j+1))
    let U := L (L a)
    let V := L U
    ∀ r < P, a r ≠ 0 → (2:ℤ)^k ∣ a r → 2*Q ∣ V r →
      V r / (2*Q) ≠ ∑ j ∈ Finset.range r, g (r+5*(j+1)) *
        (if Q ≤ (P+j+2:ℕ) then (V (j+1)/Q)%2 - (U (j+1)/Q)%2 else 0)

theorem main : H1 → H2 → type_of% @OeisA182510.conjecture1 := by
  intro hb hi
  let Z : Finset ℕ := {0,6,11,23,36,42,48,54}
  have hsmall : ∀ n : Fin 55, a n = 0 ↔ n.val ∈ Z := by decide
  have roots (n : ℕ) : a n = 0 → n ∈ Z := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hz
      by_cases hs : n < 55
      · exact (hsmall ⟨n,hs⟩).1 hz
      by_cases hfinite : n < 768
      · exact False.elim (before_block n (by omega) (by omega) hz)
      let k := Nat.log 2 (n/3)
      let P := 3*2^k
      have hk : 8 ≤ k := Nat.le_log_of_pow_le (by decide) (by norm_num; omega)
      have hlow : P ≤ n := by
        have h := Nat.pow_log_le_self 2 (show n/3 ≠ 0 by omega)
        change 2^k ≤ n/3 at h
        dsimp only [P]
        omega
      have hu : n < 2*P := by
        have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n/3)
        change n/3 < 2^(k+1) at h
        rw [pow_succ] at h
        dsimp only [P]
        omega
      let r := n-P
      have hr : r < P := by dsimp [r]; omega
      have heq : n = P+r := by dsimp [r]; omega
      have hz' : a (P+r) = 0 := heq ▸ hz
      exfalso
      by_cases hzr : a r = 0
      · have hh := inherited k hk r (ih r (by omega) hzr) hz'
        rcases hh with (h | h) | h
        · exact (hb k hk).1 h
        · exact (hb k hk).2 h
        · have hprev := ih (P-1) (by omega) h
          have hp : 768 ≤ P := by
            have hpow : 2^8 ≤ (2:ℕ)^k := Nat.pow_le_pow_right (by decide) hk
            dsimp [P]
            omega
          simp [Z] at hprev
          omega
      · obtain ⟨s,ht⟩ := lifts k
        have hd : (2:ℤ)^k ∣ a r := by
          refine ⟨-s r,?_⟩
          rw [Nat.add_comm P,ht] at hz'
          linear_combination hz'
        have hit := balance k r hr
        change a (3*2^k+r) = 0 at hz'
        rw [hz',sub_zero] at hit
        apply hi k hk r hr hzr hd ⟨_,hit⟩
        rw [hit]
        exact Int.mul_ediv_cancel_left _ (by positivity)
  have heq : {n : ℕ | a n = 0} = (Z : Set ℕ) := by
    ext n
    change a n = 0 ↔ n ∈ Z
    refine ⟨roots n,fun h => ?_⟩
    have hs : n < 55 := by simp [Z] at h; omega
    exact (hsmall ⟨n,hs⟩).2 h
  rw [heq,Set.ncard_coe_finset]
  decide

end OMA.R_OeisA182510_conjecture1_R2
