import OMAStatements.S_oeis_a071685

/-!
Harvey P. Dale's last-two-digit conjecture in OEIS A071685.
The proof works from the outer digits toward the middle. The carry
calculation is the reverse-multiple construction studied by A. L. Young
and N. J. A. Sloane, 2178 And All That (arXiv:1307.0453).
The finite tables certify the carries that can lead to a valid center.
-/

namespace A071685
open OMA.S_oeis_a071685

private def value (word : List ℕ) : ℤ := (Nat.ofDigits (10 : ℕ) word : ℕ)

private lemma value_sandwich (x : ℕ) (word : List ℕ) (y : ℕ) :
    value (x :: (word ++ [y])) = (x : ℤ) + 10 * value word + 10 ^ (word.length + 1) * y := by
  simp [value, Nat.ofDigits_cons, Nat.ofDigits_append, pow_succ]
  ring

private lemma value_bounds (word : List ℕ) (digits : ∀ d ∈ word, d < 10) :
    0 ≤ value word ∧ value word < (10 : ℤ) ^ word.length := by
  unfold value
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast Nat.ofDigits_lt_base_pow_length (by decide : 1 < 10) digits⟩

private def Carry (k left right : ℤ) (word : List ℕ) : Prop :=
  left + value word.reverse - k * value word = right * 10 ^ word.length

private def Bounded (x : ℤ) : Prop := -9 ≤ x ∧ x ≤ 0

private instance (x : ℤ) : Decidable (Bounded x) := by unfold Bounded; infer_instance

private def highDigit (k left x : ℤ) : ℤ := (k * x - left) % 10
private def leftStep (k left x : ℤ) : ℤ := (left + highDigit k left x - k * x) / 10
private def rightStep (k left right x : ℤ) : ℤ := 10 * right - x + k * highDigit k left x

private lemma carry_bound (k left right : ℤ) (word : List ℕ)
    (hk : 2 ≤ k ∧ k ≤ 9) (hl : Bounded left) (digits : ∀ d ∈ word, d < 10)
    (h : Carry k left right word) : Bounded right := by
  obtain ⟨hv0, hv⟩ := value_bounds word digits
  obtain ⟨hr0, hr⟩ := value_bounds word.reverse (by simpa using digits)
  rw [List.length_reverse] at hr
  have hp : (0 : ℤ) < 10^word.length := by positivity
  unfold Carry at h
  unfold Bounded at hl ⊢
  constructor
  · by_contra! hneg
    have hsmall := mul_le_mul_of_nonneg_right (show right ≤ -10 by omega) hp.le
    have hmul := mul_le_mul_of_nonneg_right hk.2 hv0
    linarith only [h, hsmall, hmul, hl.1, hr0, show value word ≤ 10^word.length-1 by omega, hp]
  · by_contra! hpos
    have hbig := mul_le_mul_of_nonneg_right (show 1 ≤ right by omega) hp.le
    have hmul : 0 ≤ k * value word := mul_nonneg (by omega) hv0
    linarith only [h,hbig,hmul,hl.2,hr]

private lemma peel (k left right : ℤ) (x y : ℕ) (word : List ℕ)
    (hk : 2 ≤ k ∧ k ≤ 9) (hl : Bounded left) (hx : x < 10) (hy : y < 10)
    (digits : ∀ d ∈ word, d < 10) (h : Carry k left right (x :: (word ++ [y]))) :
    (y : ℤ) = highDigit k left x ∧ Bounded (leftStep k left x) ∧
      Bounded (rightStep k left right x) ∧ Carry k (leftStep k left x) (rightStep k left right x) word := by
  unfold Carry at h
  have hlen : (x :: (word ++ [y])).length = word.length + 1 + 1 := by simp
  rw [hlen, pow_succ, show (x :: (word ++ [y])).reverse = y :: (word.reverse ++ [x]) by simp,
    value_sandwich, value_sandwich, List.length_reverse, pow_succ] at h
  have hdiv : left + y - k * x = 10 *
      ((10 * right - x + k * y) * 10 ^ word.length - (value word.reverse - k * value word)) := by
    linear_combination h
  have hdy : (y : ℤ) = highDigit k left x := by
    unfold highDigit
    omega
  have hnext : Carry k (leftStep k left x) (rightStep k left right x) word := by
    unfold Carry leftStep rightStep
    rw [← hdy, hdiv]
    omega
  have hleft : Bounded (leftStep k left x) := by
    unfold Bounded leftStep at *
    rw [← hdy]
    have hmul := mul_le_mul_of_nonneg_right hk.2 (Int.natCast_nonneg x)
    have hmul0 : 0 ≤ k * x := mul_nonneg (by omega) (Int.natCast_nonneg _)
    omega
  exact ⟨hdy,hleft,carry_bound k _ _ word hk hleft digits hnext,hnext⟩

private def coord (x : Fin 10) : ℤ := (x.val : ℤ)-9
private def index (x : ℤ) (h : Bounded x) : Fin 10 := ⟨(x+9).toNat, by unfold Bounded at h; omega⟩
private def factor (x : Fin 8) : ℤ := (x.val : ℤ)+2
private def factorIndex (x : ℤ) (h : 2 ≤ x ∧ x ≤ 9) : Fin 8 := ⟨(x-2).toNat, by omega⟩

@[simp] private lemma coord_index (x : ℤ) (h : Bounded x) : coord (index x h) = x := by
  unfold coord index Bounded at *
  simp
  omega

@[simp] private lemma factor_at (x : ℤ) (h : 2 ≤ x ∧ x ≤ 9) : factor (factorIndex x h) = x := by
  unfold factor factorIndex
  simp
  omega

/-- Row bitsets of carry pairs from which one can reach the center of the word. -/
private def carryTable : List (List ℕ) := [
  [769, 770, 772, 776, 784, 288, 320, 896, 256, 512],
  [769, 898, 772, 904, 912, 928, 448, 896, 896, 896],
  [577, 130, 260, 584, 144, 288, 576, 128, 256, 576],
  [129, 418, 260, 840, 528, 160, 64, 448, 256, 640],
  [865, 850, 116, 952, 1008, 864, 752, 976, 432, 1008],
  [577, 146, 292, 584, 144, 288, 584, 144, 288, 584],
  [1001, 982, 420, 712, 372, 680, 340, 744, 308, 600],
  [513, 1022, 782, 750, 722, 682, 602, 954, 902, 1022]]

private def productive (k l r : ℤ) : Bool :=
  let rows := (carryTable[(k-2).toNat]?).getD []
  ((rows[(l+9).toNat]?).getD 0).testBit (r+9).toNat

set_option maxRecDepth 100000 in
private theorem empty_check : ∀ k : Fin 8, ∀ l : Fin 10,
    productive (factor k) (coord l) (coord l) = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem single_check : ∀ k : Fin 8, ∀ l r d : Fin 10,
    coord l + (1-factor k)*d.val = 10*coord r → productive (factor k) (coord l) (coord r) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem step_check : ∀ k : Fin 8, ∀ l r x : Fin 10,
    Bounded (leftStep (factor k) (coord l) x.val) → Bounded (rightStep (factor k) (coord l) (coord r) x.val) →
    productive (factor k) (leftStep (factor k) (coord l) x.val)
      (rightStep (factor k) (coord l) (coord r) x.val) = true →
    productive (factor k) (coord l) (coord r) = true := by decide +kernel

private theorem can_finish (word : List ℕ) (digits : ∀ d ∈ word, d < 10)
    (k l r : ℤ) (hk : 2 ≤ k ∧ k ≤ 9) (hl : Bounded l) (hr : Bounded r)
    (h : Carry k l r word) : productive k l r = true := by
  induction word using List.bidirectionalRec generalizing l r with
  | nil =>
      have he : l = r := by simpa [Carry,value] using h
      subst r
      simpa using empty_check (factorIndex k hk) (index l hl)
  | singleton d =>
      have he : l + (1-k)*(d:ℤ) = 10*r := by
        simp [Carry,value] at h
        linear_combination h
      have test := single_check (factorIndex k hk) (index l hl) (index r hr) ⟨d,digits d (by simp)⟩
      simp only [factor_at,coord_index] at test
      exact test he
  | cons_append x word y ih =>
      have hx : x < 10 := digits x (by simp)
      have hy : y < 10 := digits y (by simp)
      have inner : ∀ d ∈ word, d < 10 := fun d hd => digits d (by simp [hd])
      obtain ⟨_, hl', hr', h'⟩ := peel k l r x y word hk hl hx hy inner h
      have test := step_check (factorIndex k hk) (index l hl) (index r hr) ⟨x,hx⟩
      simp only [factor_at,coord_index] at test
      exact test hl' hr' (ih inner _ _ hl' hr' h')

private theorem root_check : ∀ k : Fin 8, ∀ x : Fin 10,
    0 < x.val → 0 < highDigit (factor k) 0 x.val →
    Bounded (leftStep (factor k) 0 x.val) → Bounded (rightStep (factor k) 0 0 x.val) →
    productive (factor k) (leftStep (factor k) 0 x.val) (rightStep (factor k) 0 0 x.val) = true →
    leftStep (factor k) 0 x.val < 0 ∧ rightStep (factor k) 0 0 x.val = 0 := by decide +kernel

private def endings : Finset ℕ := {1,12,78,89}

set_option maxRecDepth 100000 in
private theorem two_check : ∀ i : Fin 8, ∀ x u : Fin 10,
    let k := factor i
    let l := leftStep k 0 x.val
    let r := rightStep k 0 0 x.val
    0 < x.val → 0 < highDigit k 0 x.val → Bounded l → Bounded r →
    productive k l r = true → Bounded (leftStep k l u.val) → Bounded (rightStep k l r u.val) →
    productive k (leftStep k l u.val) (rightStep k l r u.val) = true →
    x.val+10*u.val ∈ endings ∧ (highDigit k 0 x.val).toNat+10*(highDigit k l u.val).toNat ∈ endings := by
  decide +kernel

private lemma mod_two (x y : ℕ) (tail : List ℕ) (hx : x < 10) (hy : y < 10) :
    Nat.ofDigits 10 (x :: y :: tail) % 100 = x+10*y := by
  simp only [Nat.ofDigits_cons]
  omega

private def EndsNonzero (word : List ℕ) : Prop :=
  ∃ x y : ℕ, word.head? = some x ∧ 0 < x ∧ word.getLast? = some y ∧ 0 < y

private lemma endings_of_word (word : List ℕ) (good : ∀ d ∈ word, d < 10)
    (ends : EndsNonzero word) (k : ℤ) (hk : 2 ≤ k ∧ k ≤ 9) (carry : Carry k 0 0 word) :
    Nat.ofDigits 10 word % 100 ∈ endings ∧ Nat.ofDigits 10 word.reverse % 100 ∈ endings := by
  obtain ⟨a,b,ha,hapos,hb,hbpos⟩ := ends
  cases word using List.bidirectionalRec with
  | nil => simp at ha
  | singleton d =>
      have hdp : 0 < d := by simpa using (Option.some.inj ha ▸ hapos)
      simp [Carry,value] at carry
      have hmul := mul_le_mul_of_nonneg_right hk.1 (Int.natCast_nonneg d)
      omega
  | cons_append x mid y =>
      have hx0 : 0 < x := by
        have hd : x = a := by simpa using ha
        omega
      have hy0 : 0 < y := by
        have hd : y = b := by simpa [List.getLast?_cons, List.getLast?_concat] using hb
        omega
      have hx : x < 10 := good x (by simp)
      have hy : y < 10 := good y (by simp)
      have hm : ∀ d ∈ mid, d < 10 := fun d hd => good d (by simp [hd])
      obtain ⟨dy, hl, hr, middle⟩ := peel k 0 0 x y mid hk (by decide) hx hy hm carry
      have active := can_finish mid hm k _ _ hk hl hr middle
      have root := root_check (factorIndex k hk) ⟨x,hx⟩
      simp only [factor_at] at root
      obtain ⟨leftNeg, rightZero⟩ := root hx0 (by omega) hl hr active
      cases mid using List.bidirectionalRec with
      | nil => simp [Carry,value,rightZero] at middle; omega
      | singleton d =>
          simp [Carry,value,rightZero] at middle
          have hmul := mul_le_mul_of_nonneg_right hk.1 (Int.natCast_nonneg d)
          omega
      | cons_append u core v =>
          have hu : u < 10 := hm u (by simp)
          have hv : v < 10 := hm v (by simp)
          have hc : ∀ d ∈ core, d < 10 := fun d hd => hm d (by simp [hd])
          obtain ⟨dv, hl', hr', final⟩ := peel k _ _ u v core hk hl hu hv hc middle
          have alive := can_finish core hc k _ _ hk hl' hr' final
          have verified := two_check (factorIndex k hk) ⟨x,hx⟩ ⟨u,hu⟩
          simp only [factor_at] at verified
          obtain ⟨small,large⟩ := verified hx0 (by omega) hl hr active hl' hr' alive
          have hys : (highDigit k 0 x).toNat = y := by rw [← dy]; simp
          have hvs : (highDigit k (leftStep k 0 x) u).toNat = v := by rw [← dv]; simp
          constructor
          · change Nat.ofDigits 10 (x :: u :: ((core ++ [v]) ++ [y])) % 100 ∈ endings
            rw [mod_two x u _ hx hu]
            exact small
          · rw [show (x :: ((u :: (core ++ [v])) ++ [y])).reverse =
                  y :: v :: (core.reverse ++ [u,x]) by simp [List.reverse_append, List.append_assoc],
                mod_two y v _ hy hv]
            simpa only [hys,hvs] using large

private lemma length_bound (w : List ℕ) (h : w.getLast? ≠ some 0) (ne : w ≠ []) :
    (10:ℕ)^w.length ≤ 10 * Nat.ofDigits 10 w := by
  apply Nat.pow_length_le_mul_ofDigits ne
  intro bad
  exact h (by rw [List.getLast?_eq_some_getLast ne,bad])

private lemma word_multiple (w : List ℕ) (good : ∀ d ∈ w, d < 10) (ends : EndsNonzero w)
    (k : ℕ) (nontrivial : k ≠ 1)
    (multiple : Nat.ofDigits 10 w.reverse = k * Nat.ofDigits 10 w) :
    Nat.ofDigits 10 w % 100 ∈ endings ∧ Nat.ofDigits 10 w.reverse % 100 ∈ endings := by
  obtain ⟨x,y,hx,hxp,hy,hyp⟩ := ends
  have hw : w ≠ [] := by intro eq; simp [eq] at hx
  have hwrev : w.reverse ≠ [] := by simpa using hw
  have last : w.getLast? ≠ some 0 := by rw [hy]; simp [hyp.ne']
  have revlast : w.reverse.getLast? ≠ some 0 := by rw [List.getLast?_reverse,hx]; simp [hxp.ne']
  have low := length_bound w last hw
  have lowRev := length_bound w.reverse revlast hwrev
  rw [List.length_reverse] at lowRev
  have highRev := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 10) (show ∀ d ∈ w.reverse, d < 10 by simpa using good)
  rw [List.length_reverse] at highRev
  have powpos : 0 < (10:ℕ)^w.length := by positivity
  have hpos : k ≠ 0 := by intro eq; rw [eq,zero_mul] at multiple; omega
  have hkLo : 2 ≤ k := by omega
  have hkHi : k ≤ 9 := by
    by_contra! h
    have hp := Nat.mul_le_mul_right (Nat.ofDigits 10 w) (show 10 ≤ k by omega)
    omega
  have eq : value w.reverse = (k:ℤ) * value w := by
    unfold value
    exact_mod_cast multiple
  apply endings_of_word w good ⟨x,y,hx,hxp,hy,hyp⟩ (k:ℤ) (by omega)
  simp [Carry,eq]

end A071685

open A071685 OMA.S_oeis_a071685 in
theorem OMA.solution : type_of% @OMA.S_oeis_a071685.main := by
  intro n hn
  obtain ⟨pos, neq, nondiv, orient⟩ := hn
  let w := Nat.digits 10 n
  have good : ∀ d ∈ w, d < 10 := fun d hd => Nat.digits_lt_base (by decide) hd
  have head : w.head? = some (n%10) := by
    unfold w
    rw [Nat.digits_def' (by decide : 1<10) pos]
    rfl
  have hhead : 0 < n%10 := by
    exact Nat.pos_of_ne_zero (fun h => nondiv (Nat.dvd_iff_mod_eq_zero.mpr h))
  have ne : w ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr pos.ne'
  have last : w.getLast? = some (w.getLast ne) := List.getLast?_eq_some_getLast ne
  have hlast : 0 < w.getLast ne := Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 10 pos.ne')
  have val : Nat.ofDigits 10 w = n := Nat.ofDigits_digits 10 n
  have revval : Nat.ofDigits 10 w.reverse = R n := rfl
  rcases orient with ⟨k,hk⟩ | ⟨k,hk⟩
  · have nontrivial : k ≠ 1 := fun h => neq (by simpa [h] using hk)
    have mult : Nat.ofDigits 10 w.reverse = k*Nat.ofDigits 10 w := by simpa [val,revval,mul_comm] using hk
    simpa [val,endings] using (word_multiple w good ⟨_,_,head,hhead,last,hlast⟩ k nontrivial mult).1
  · have nontrivial : k ≠ 1 := fun h => neq (by simpa [h] using hk.symm)
    have mult : Nat.ofDigits 10 w.reverse.reverse = k*Nat.ofDigits 10 w.reverse := by
      simpa [val,revval,mul_comm] using hk
    have ends : EndsNonzero w.reverse := ⟨_,_,by simpa using last,hlast,by simpa using head,hhead⟩
    have h := (word_multiple w.reverse (by simpa using good) ends k nontrivial mult).2
    simpa [val,endings] using h
