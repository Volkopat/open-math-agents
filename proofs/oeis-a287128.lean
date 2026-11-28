import OMAStatements.S_oeis_a287128
import Mathlib

open OMA.S_oeis_a287128

private inductive Block where
  | zeroZero
  | zeroOne
  | one
  deriving DecidableEq

private def letters : Block → List Bool
  | .zeroZero => [false,false]
  | .zeroOne => [false,true]
  | .one => [true]

private def emit : Block → List Bool
  | .zeroZero => [false,false,true]
  | .zeroOne => [false,true,true,false]
  | .one => [true,true,false]

private def active : Block → Bool
  | .zeroZero => false
  | _ => true

private def pending (b : Bool) : List Bool := if b then [false] else []

private def encode (bs : List Block) : List Bool := bs.flatMap letters

private theorem rewrite_encoded (bs : List Block) (q : Bool) :
    rewrite (encode bs ++ pending q) = bs.flatMap emit ++ pending q := by
  induction bs with
  | nil => cases q <;> rfl
  | cons b bs ih =>
    cases b <;>
      simp only [encode,List.flatMap_cons,letters,emit,List.cons_append,List.nil_append,rewrite] at ih ⊢ <;>
      rw [ih]

/-- A pending zero is read just before the next emitted block. -/
private def moveBlock : Bool → Block → List Block
  | false, .zeroZero => [.zeroZero,.one]
  | true, .zeroZero => [.zeroZero,.zeroOne]
  | false, .zeroOne => [.zeroOne,.one]
  | true, .zeroOne => [.zeroZero,.one,.one]
  | false, .one => [.one,.one]
  | true, .one => [.zeroOne,.one]

private def lastActive (p : Bool) : List Block → Bool
  | [] => p
  | b::bs => lastActive (active b) bs

private def moved (p : Bool) : List Block → List Block
  | [] => []
  | b::bs => moveBlock p b ++ moved (active b) bs

private theorem move_local (p : Bool) (b : Block) :
    pending p ++ emit b = encode (moveBlock p b) ++ pending (active b) := by
  cases p <;> cases b <;> rfl

private theorem moving (p : Bool) (bs : List Block) :
    pending p ++ bs.flatMap emit = encode (moved p bs) ++ pending (lastActive p bs) := by
  induction bs generalizing p with
  | nil => simp [moved,encode,lastActive]
  | cons b bs ih =>
    rw [List.flatMap_cons, ← List.append_assoc, move_local, List.append_assoc, ih]
    simp [moved,encode,List.flatMap_append,List.append_assoc,lastActive]

private theorem last_append (p : Bool) (xs ys : List Block) :
    lastActive p (xs++ys) = lastActive (lastActive p xs) ys := by
  induction xs generalizing p with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append,lastActive,ih]

private theorem move_last (q p : Bool) (b : Block) :
    lastActive q (moveBlock p b) = true := by cases p <;> cases b <;> rfl

private theorem moved_last (p : Bool) (bs : List Block) :
    lastActive true (moved p bs) = true := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih => rw [moved,last_append,move_last,ih]

private def spill (q : Bool) : List Block := if q then [.zeroZero] else []

private def rest : ℕ → List Block
  | 0 => []
  | n+1 => .one :: (moved false (rest n) ++ spill (decide (n%3 = 2)))

private theorem mod_cycle (n : ℕ) : ((n+1)%3 = 0) ↔ n%3 = 2 := by omega

private theorem rest_last (n : ℕ) : lastActive false (rest n) = decide (n%3 ≠ 0) := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [rest,lastActive,last_append]
    change lastActive (lastActive true (moved false (rest n))) (spill (decide (n%3=2))) = _
    rw [moved_last]
    by_cases h : n%3=2
    · have ht : (n+1)%3=0 := (mod_cycle n).mpr h
      simp [h,ht,spill,lastActive,active]
    · have ht : (n+1)%3≠0 := fun h' => h ((mod_cycle n).mp h')
      simp [h,ht,spill,lastActive]

private theorem pending_cycle (n : ℕ) :
    pending (decide (n%3 ≠ 0)) ++ pending (decide (n%3 = 2)) =
      encode (spill (decide (n%3 = 2))) ++ pending (decide ((n+1)%3 = 2)) := by
  have hh : n%3 = 0 ∨ n%3 = 1 ∨ n%3 = 2 := by omega
  rcases hh with h | h | h
  · have ht : (n+1)%3≠2 := by omega
    simp [pending,spill,encode,h,ht]
  · have ht : (n+1)%3=2 := by omega
    simp [pending,spill,encode,h,ht]
  · have ht : (n+1)%3≠2 := by omega
    simp [pending,spill,encode,letters,h,ht]

private theorem word_rest (n : ℕ) :
    word n = encode (.zeroZero::rest n) ++ pending (decide (n%3 = 2)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [word,ih,rewrite_encoded]
    change [false,false,true] ++ (pending false ++ (rest n).flatMap emit) ++
        pending (decide (n%3=2)) = _
    rw [moving,rest_last]
    simp only [List.append_assoc]
    rw [pending_cycle,rest]
    simp [encode,letters,List.flatMap_append,List.append_assoc]

private def tag (p : Bool) : List Block → List (Bool × Block)
  | [] => []
  | b::bs => (p,b) :: tag (active b) bs

private theorem tag_append (p : Bool) (xs ys : List Block) :
    tag p (xs++ys) = tag p xs ++ tag (lastActive p xs) ys := by
  induction xs generalizing p with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append,tag,lastActive,ih]

private def expandTag (t : Bool × Block) : List (Bool × Block) :=
  tag true (moveBlock t.1 t.2)

private theorem tag_moved (p : Bool) (bs : List Block) :
    tag true (moved p bs) = (tag p bs).flatMap expandTag := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih => rw [moved,tag_append,move_last,ih,tag,List.flatMap_cons,expandTag]

private theorem rest_tags (n : ℕ) :
    tag false (rest (n+1)) = (false,Block.one) ::
      ((tag false (rest n)).flatMap expandTag ++
        if n%3=2 then [(true,Block.zeroZero)] else []) := by
  rw [rest,tag]
  change (false,Block.one) :: tag true (moved false (rest n) ++ spill (decide (n%3=2))) = _
  rw [tag_append,moved_last,tag_moved]
  by_cases h : n%3=2 <;> simp [h,spill,tag]

private def tally (target : Bool × Block) : List (Bool × Block) → ℤ
  | [] => 0
  | t::ts => (if t=target then 1 else 0) + tally target ts

private theorem tally_append (t : Bool × Block) (xs ys : List (Bool × Block)) :
    tally t (xs++ys) = tally t xs+tally t ys := by
  induction xs with
  | nil => simp [tally]
  | cons x xs ih => simp [tally,ih,add_assoc]

private def tU (ts : List (Bool × Block)) : ℤ := tally (false,.zeroZero) ts
private def U (n : ℕ) : ℤ := tU (tag false (rest n))
private def tA (ts : List (Bool × Block)) : ℤ := tally (true,.zeroZero) ts
private def A (n : ℕ) : ℤ := tA (tag false (rest n))
private def tB (ts : List (Bool × Block)) : ℤ := tally (false,.zeroOne) ts
private def B (n : ℕ) : ℤ := tB (tag false (rest n))
private def tC (ts : List (Bool × Block)) : ℤ := tally (true,.zeroOne) ts
private def C (n : ℕ) : ℤ := tC (tag false (rest n))
private def tD (ts : List (Bool × Block)) : ℤ := tally (false,.one) ts
private def D (n : ℕ) : ℤ := tD (tag false (rest n))
private def tE (ts : List (Bool × Block)) : ℤ := tally (true,.one) ts
private def E (n : ℕ) : ℤ := tE (tag false (rest n))

private def Q (n : ℕ) : ℤ := if n%3=2 then 1 else 0
private def P (n : ℕ) : ℤ := if n%3=0 then 0 else 1

private theorem transformed_counts (ts : List (Bool × Block)) :
    tU (ts.flatMap expandTag) = 0 ∧
    tA (ts.flatMap expandTag) = tU ts+tA ts+tC ts ∧
    tB (ts.flatMap expandTag) = tA ts ∧
    tC (ts.flatMap expandTag) = tB ts+tE ts ∧
    tD (ts.flatMap expandTag) = tU ts+tC ts ∧
    tE (ts.flatMap expandTag) = tB ts+tC ts+2*tD ts+tE ts := by
  induction ts with
  | nil => decide +kernel
  | cons t ts ih =>
    rcases t with ⟨p,b⟩
    simp only [tU,tA,tB,tC,tD,tE] at ih
    cases p <;> cases b <;>
      simp [tU,tA,tB,tC,tD,tE,expandTag,moveBlock,tag,active,tally] <;> omega

private theorem raw_counts (n : ℕ) :
    U (n+1)=0 ∧ A (n+1)=U n+A n+C n+Q n ∧
    B (n+1)=A n ∧ C (n+1)=B n+E n ∧
    D (n+1)=1+U n+C n ∧ E (n+1)=B n+C n+2*D n+E n := by
  have h := transformed_counts (tag false (rest n))
  unfold U A B C D E Q
  rw [rest_tags]
  simp only [tU,tA,tB,tC,tD,tE] at h ⊢
  by_cases q : n%3=2 <;> simp [q,tally,tally_append] <;> omega

private theorem u_zero (n : ℕ) : U n=0 := by
  cases n with
  | zero => rfl
  | succ n => exact (raw_counts n).1

private theorem counts (n : ℕ) :
    A (n+1)=A n+C n+Q n ∧ B (n+1)=A n ∧ C (n+1)=B n+E n ∧
    D (n+1)=1+C n ∧ E (n+1)=B n+C n+2*D n+E n := by
  have h := (raw_counts n).2
  simpa [u_zero] using h

private theorem invariant (n : ℕ) : A n-B n-D n = -P n := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := counts n
    unfold Q P at *
    by_cases q : n%3=2
    · have hp := (mod_cycle n).mpr q
      simp [q,hp] at *
      omega
    · have hp : (n+1)%3≠0 := fun he => q ((mod_cycle n).mp he)
      simp [q,hp] at *
      omega

private theorem enc_length (p : Bool) (bs : List Block) :
    ((encode bs).length : ℤ) =
      2*(tU (tag p bs)+tA (tag p bs)+tB (tag p bs)+tC (tag p bs))+
        tD (tag p bs)+tE (tag p bs) := by
  induction bs generalizing p with
  | nil => cases p <;> decide +kernel
  | cons b bs ih =>
    have hsplit : (encode (b::bs)).length = (letters b).length + (encode bs).length := by
      change (letters b ++ encode bs).length = _
      rw [List.length_append]
    rw [hsplit,Nat.cast_add,ih (active b)]
    cases p <;> cases b <;>
      simp [letters,tU,tA,tB,tC,tD,tE,tag,active,tally] <;> omega

private theorem word_length (n : ℕ) :
    ((word n).length : ℤ) = 2+2*(A n+B n+C n)+D n+E n+Q n := by
  rw [word_rest,List.length_append,Nat.cast_add,enc_length false]
  have hU := u_zero n
  unfold U tU at hU
  unfold A B C D E Q
  by_cases q : n%3=2 <;>
    simp [pending,q,tU,tA,tB,tC,tD,tE,tag,active,tally] <;> omega

private theorem length_recurrence (n : ℕ) :
    ((word (n+5)).length : ℤ) =
      3*((word (n+4)).length : ℤ) - 2*((word (n+3)).length : ℤ) +
      2*((word (n+2)).length : ℤ) - 4*((word (n+1)).length : ℤ) + 2*((word n).length : ℤ) := by
  have h0 := counts n
  have h1 := counts (n+1)
  have h2 := counts (n+2)
  have h3 := counts (n+3)
  have h4 := counts (n+4)
  simp only [Nat.add_assoc, show (1:ℕ)+1=2 by decide, show (2:ℕ)+1=3 by decide,
    show (3:ℕ)+1=4 by decide, show (4:ℕ)+1=5 by decide] at h1 h2 h3 h4
  have hi := invariant n
  simp only [word_length]
  have hmod : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
  rcases hmod with h | h | h
  · have q1 : (n+1)%3 = 1 := by omega
    have q2 : (n+2)%3 = 2 := by omega
    have q3 : (n+3)%3 = 0 := by omega
    have q4 : (n+4)%3 = 1 := by omega
    have q5 : (n+5)%3 = 2 := by omega
    simp [Q,P,h,q1,q2,q3,q4,q5] at *
    linarith only [hi,h0.1,h0.2.1,h0.2.2.1,h0.2.2.2.1,h0.2.2.2.2,h1.1,h1.2.1,h1.2.2.1,h1.2.2.2.1,h1.2.2.2.2,h2.1,h2.2.1,h2.2.2.1,h2.2.2.2.1,h2.2.2.2.2,h3.1,h3.2.1,h3.2.2.1,h3.2.2.2.1,h3.2.2.2.2,h4.1,h4.2.1,h4.2.2.1,h4.2.2.2.1,h4.2.2.2.2]
  · have q1 : (n+1)%3 = 2 := by omega
    have q2 : (n+2)%3 = 0 := by omega
    have q3 : (n+3)%3 = 1 := by omega
    have q4 : (n+4)%3 = 2 := by omega
    have q5 : (n+5)%3 = 0 := by omega
    simp [Q,P,h,q1,q2,q3,q4,q5] at *
    linarith only [hi,h0.1,h0.2.1,h0.2.2.1,h0.2.2.2.1,h0.2.2.2.2,h1.1,h1.2.1,h1.2.2.1,h1.2.2.2.1,h1.2.2.2.2,h2.1,h2.2.1,h2.2.2.1,h2.2.2.2.1,h2.2.2.2.2,h3.1,h3.2.1,h3.2.2.1,h3.2.2.2.1,h3.2.2.2.2,h4.1,h4.2.1,h4.2.2.1,h4.2.2.2.1,h4.2.2.2.2]
  · have q1 : (n+1)%3 = 0 := by omega
    have q2 : (n+2)%3 = 1 := by omega
    have q3 : (n+3)%3 = 2 := by omega
    have q4 : (n+4)%3 = 0 := by omega
    have q5 : (n+5)%3 = 1 := by omega
    simp [Q,P,h,q1,q2,q3,q4,q5] at *
    linarith only [hi,h0.1,h0.2.1,h0.2.2.1,h0.2.2.2.1,h0.2.2.2.2,h1.1,h1.2.1,h1.2.2.1,h1.2.2.2.1,h1.2.2.2.2,h2.1,h2.2.1,h2.2.2.1,h2.2.2.2.1,h2.2.2.2.2,h3.1,h3.2.1,h3.2.2.1,h3.2.2.2.1,h3.2.2.2.2,h4.1,h4.2.1,h4.2.2.1,h4.2.2.2.1,h4.2.2.2.2]

theorem OMA.solution : type_of% @OMA.S_oeis_a287128.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n<5
    · interval_cases n <;> decide +kernel
    · obtain ⟨j,rfl⟩ : ∃ j, n=j+5 := ⟨n-5,by omega⟩
      rw [length_recurrence,ih (j+4) (by omega),ih (j+3) (by omega),ih (j+2) (by omega),
        ih (j+1) (by omega),ih j (by omega),reference]