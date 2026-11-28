import OMAStatements.S_oeis_a026368

/-! Positions of the zeros of the substitution 0 -> 11, 1 -> 110. -/
-- Credit: @STARDUSTLC666

namespace MorphicZeros

open OMA.S_oeis_a026368

private noncomputable def slope : ℝ := 2 + Real.sqrt 3
private noncomputable def c : ℝ := Real.sqrt 3 - 1

private lemma contraction : 0 ≤ c ∧ c ≤ 3/4 := by
  have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have p := Real.sqrt_nonneg (3:ℝ)
  unfold c
  constructor <;> nlinarith

private noncomputable def delta (w : List Bool) : ℝ :=
  slope * (w.count false : ℝ) - w.length

private lemma delta_append (u v : List Bool) : delta (u++v) = delta u + delta v := by
  simp [delta,List.count_append]
  ring

private lemma step_append (u v : List Bool) :
    morphStep (u++v) = morphStep u ++ morphStep v := by simp [morphStep]

private lemma step_delta (w : List Bool) : delta (morphStep w) = -c * delta w := by
  induction w with
  | nil => simp [morphStep,delta]
  | cons b w ih =>
    change delta (morphStep ([b] ++ w)) = -c * delta ([b] ++ w)
    rw [step_append, delta_append, delta_append, ih]
    have sq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    cases b <;> norm_num [morphStep,delta,c,slope] <;> nlinarith

-- Full images and the two possible incomplete initial segments of a letter image.
private def Good (w : List Bool) : Prop :=
  -(14/3) ≤ delta w ∧ delta w ≤ 7/2 ∧
  (w.getLast? = some true → delta w ≤ 5/2) ∧
  (w.getLast? = some false → -(15/8) ≤ delta w)

private lemma empty_good : Good [] := by norm_num [Good,delta]

private lemma image_bounds {w : List Bool} (h : Good w) :
    -(21/8) ≤ delta (morphStep w) ∧ delta (morphStep w) ≤ 7/2 := by
  rw [step_delta]
  obtain ⟨lo,hi,_⟩ := h
  obtain ⟨nonneg,small⟩ := contraction
  constructor
  · nlinarith [mul_nonneg nonneg (sub_nonneg.mpr hi)]
  · nlinarith [mul_nonneg nonneg (sub_nonneg.mpr lo)]

private lemma ones_good {w : List Bool} (h : Good w) :
    Good (morphStep w ++ [true]) ∧ Good (morphStep w ++ [true,true]) := by
  obtain ⟨lo,hi⟩ := image_bounds h
  have one : delta [true] = -1 := by norm_num [delta]
  have two : delta [true,true] = -2 := by norm_num [delta]
  constructor <;> simp [Good,delta_append,one,two] <;> (repeat' apply And.intro) <;> linarith

private lemma zero_good {v : List Bool} (h : Good (v ++ [true])) :
    Good (morphStep (v ++ [true])) := by
  have last : delta (v ++ [true]) ≤ 5/2 := h.2.2.1 (by simp)
  obtain ⟨lo,hi⟩ := image_bounds h
  have strictLo : -(15/8) ≤ delta (morphStep (v ++ [true])) := by
    rw [step_delta]
    obtain ⟨nonneg,small⟩ := contraction
    nlinarith [mul_nonneg nonneg (sub_nonneg.mpr last)]
  have ends : (morphStep (v ++ [true])).getLast? = some false := by
    rw [step_append]
    simp [morphStep]
  exact ⟨by linarith,hi,by simp [ends],fun _ => strictLo⟩

-- Check all prefixes by scanning the unprocessed suffix from left to right.
private def Scan (v : List Bool) : List Bool → Prop
  | [] => Good v
  | b :: w => Good v ∧ Scan (v ++ [b]) w

private lemma scan_start {v w : List Bool} (h : Scan v w) : Good v := by
  cases w with
  | nil => exact h
  | cons b w => exact h.1

private lemma scan_image (v w : List Bool) (h : Scan v w) (start : Good (morphStep v)) :
    Scan (morphStep v) (morphStep w) := by
  induction w generalizing v with
  | nil => exact start
  | cons b w ih =>
    obtain ⟨hv,tail⟩ := h
    obtain ⟨one,two⟩ := ones_good hv
    cases b with
    | false =>
      have full : morphStep (v++[false]) = morphStep v ++ [true,true] := by
        rw [step_append]; rfl
      have next := ih (v++[false]) tail (full ▸ two)
      change Good _ ∧ Good _ ∧ Scan _ (morphStep w)
      exact ⟨start,one,by simpa [full,List.append_assoc] using next⟩
    | true =>
      have full : morphStep (v++[true]) = morphStep v ++ [true,true,false] := by
        rw [step_append]; rfl
      have next := ih (v++[true]) tail (zero_good (scan_start tail))
      change Good _ ∧ Good _ ∧ Good _ ∧ Scan _ (morphStep w)
      exact ⟨start,one,by simpa [List.append_assoc] using two,
        by simpa [full,List.append_assoc] using next⟩

private lemma scan_take (v w : List Bool) (h : Scan v w) (k : ℕ) :
    Good (v ++ w.take k) := by
  induction w generalizing v k with
  | nil => simpa [Scan] using h
  | cons b w ih =>
    cases k with
    | zero => simpa using h.1
    | succ k => simpa [List.append_assoc] using ih (v++[b]) h.2 k

private def stage (t : ℕ) := morphStep^[t] [true]

private lemma stage_succ (t : ℕ) : stage (t+1) = morphStep (stage t) :=
  Function.iterate_succ_apply' _ _ _

private lemma stage_scan (t : ℕ) : Scan [] (stage t) := by
  induction t with
  | zero =>
    change Good [] ∧ Good [true]
    exact ⟨empty_good,by norm_num [Good,delta]⟩
  | succ t ih => exact stage_succ t ▸ scan_image [] (stage t) ih empty_good

private lemma stage_length (t : ℕ) : t+1 ≤ (stage t).length := by
  have growth (w : List Bool) : 2*w.length ≤ (morphStep w).length := by
    induction w with
    | nil => simp
    | cons b w ih =>
      cases b <;> simp [morphStep] at ih ⊢ <;> omega
  induction t with
  | zero => decide
  | succ t ih => rw [stage_succ]; have := growth (stage t); omega

private lemma stage_prefix {i j : ℕ} (h : i ≤ j) : (stage i).IsPrefix (stage j) := by
  have one (n : ℕ) : (stage n).IsPrefix (stage (n+1)) := by
    induction n with
    | zero => exact ⟨[true,false],rfl⟩
    | succ n ih =>
      obtain ⟨tail,e⟩ := ih
      refine ⟨morphStep tail,?_⟩
      calc
        stage (n+1) ++ morphStep tail = morphStep (stage n) ++ morphStep tail := by rw [stage_succ n]
        _ = morphStep (stage n ++ tail) := (step_append _ _).symm
        _ = stage (n+1+1) := by rw [e, stage_succ (n+1)]
  induction j, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ j _ ih => exact ih.trans (one j)

private def initial (k : ℕ) := (List.range k).map fixedPoint

private lemma initial_succ (k : ℕ) : initial (k+1) = initial k ++ [fixedPoint k] := by
  simp [initial,List.range_succ]

private lemma initial_good (k : ℕ) : Good (initial k) := by
  have agree : initial k = (stage k).take k := by
    apply List.ext_getElem
    · simp [initial, Nat.min_eq_left (by have := stage_length k; omega : k ≤ (stage k).length)]
    · intro i left right
      have ik : i < k := by simpa [initial] using left
      have inside : i < (stage (i+1)).length := by have := stage_length (i+1); omega
      have extended := stage_prefix (show i+1 ≤ k by omega)
      have letter : fixedPoint i = (stage k)[i]'(inside.trans_le extended.length_le) := by
        change (stage (i+1)).getD i true = _
        rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside]
        exact extended.getElem inside
      simpa [initial] using letter
  rw [agree]
  simpa using scan_take [] (stage k) (stage_scan k) k

private abbrev zeroAt (i : ℕ) := fixedPoint i = false

private lemma count_initial (k : ℕ) : (initial k).count false = Nat.count zeroAt k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases e : fixedPoint k <;> simp [initial_succ,List.count_append,Nat.count_succ,ih,zeroAt,e]

private lemma infinitely_many : (Set.ofPred zeroAt).Infinite := by
  classical
  intro finite
  let m := finite.toFinset.card
  let k := 4*m+6
  have lo := (initial_good k).1
  rw [delta,count_initial] at lo
  have length : (initial k).length = k := by simp [initial]
  rw [length] at lo
  have bound : (Nat.count zeroAt k : ℝ) ≤ m := by exact_mod_cast Nat.count_le_card finite k
  have coeff : slope ≤ 4 := by
    have := contraction.2
    unfold c at this
    unfold slope
    linarith
  have product := mul_nonneg (sub_nonneg.mpr coeff) (Nat.cast_nonneg (α := ℝ) (Nat.count zeroAt k))
  dsimp [k] at lo
  push_cast at lo
  linarith

theorem position_bounds (n : ℕ) (hn : 1 ≤ n) :
    -(15/8) ≤ (n : ℝ)*(2+Real.sqrt 3) - a n ∧
    (n : ℝ)*(2+Real.sqrt 3) - a n ≤ 7/2 := by
  let i := Nat.nth zeroAt (n-1)
  have marked : fixedPoint i = false := Nat.nth_mem_of_infinite infinitely_many _
  have rank : Nat.count zeroAt (i+1) = n := by
    rw [Nat.count_succ,if_pos marked]
    have h := Nat.count_nth_of_infinite infinitely_many (n-1)
    dsimp [i]
    omega
  have last : (initial (i+1)).getLast? = some false := by simp [initial_succ,marked]
  have good := initial_good (i+1)
  have result := And.intro (good.2.2.2 last) good.2.1
  rw [delta,count_initial,rank] at result
  have length : (initial (i+1)).length = a n := by simp [initial,a,i]
  rwa [length, slope, mul_comm (2 + Real.sqrt 3)] at result

end MorphicZeros

theorem OMA.solution : type_of% @OMA.S_oeis_a026368.main := by
  intro n hn
  obtain ⟨lo,hi⟩ := MorphicZeros.position_bounds n hn
  constructor <;> linarith
