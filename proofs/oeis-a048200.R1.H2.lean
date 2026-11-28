import OMAReductions.R_oeis_a048200_R1

/-!
The explicit reversal word is Algorithm LE1 of Sai Satwik Kuppili and
Bhadrachalam Chitturi, Exact upper bound for sorting Rn with LE, Theorem 2,
doi:10.1142/S1793830920500330. The list invariants below use arbitrary labels,
so the same word takes the ascending range to its reverse.
-/

namespace OMA.ReversalUpper
open OMA.S_oeis_a048200

private theorem run_append (p q : List Bool) (xs : List ℕ) :
    run (p ++ q) xs = run q (run p xs) := by simp [run, List.foldl_append]

private def turn (k : ℕ) : List Bool := List.replicate k true

private def carry : ℕ → List Bool
  | 0 => []
  | k + 1 => false :: true :: carry k

private theorem turn_length (k : ℕ) : (turn k).length = k := by simp [turn]

private theorem carry_length (k : ℕ) : (carry k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [carry, List.length_cons, ih]; omega

private theorem turn_front (xs ys : List ℕ) :
    run (turn xs.length) (xs ++ ys) = ys ++ xs := by
  induction xs generalizing ys with
  | nil => simp [turn, run]
  | cons x xs ih =>
    change run ([true] ++ turn xs.length) (x :: (xs ++ ys)) = ys ++ (x :: xs)
    rw [run_append]
    have h : run [true] (x :: (xs ++ ys)) = xs ++ (ys ++ [x]) := by
      simp [run, step, List.append_assoc]
    rw [h, ih]
    simp [List.append_assoc]

private theorem carry_front (x : ℕ) (xs ys : List ℕ) :
    run (carry xs.length) (x :: (xs ++ ys)) = x :: (ys ++ xs) := by
  induction xs generalizing ys with
  | nil => simp [carry, run]
  | cons y xs ih =>
    change run ([false, true] ++ carry xs.length) (x :: y :: (xs ++ ys)) =
      x :: (ys ++ y :: xs)
    rw [run_append]
    have h : run [false, true] (x :: y :: (xs ++ ys)) = x :: (xs ++ (ys ++ [y])) := by
      simp [run, step, exch, List.append_assoc]
    rw [h, ih]
    simp [List.append_assoc]

private theorem cycle_step (x y : ℕ) (u s v b t : List ℕ) :
    run (carry u.length ++ turn (s.length + 1) ++ carry (v ++ b).length ++ turn (t.length + 1))
      (x :: (u ++ (s ++ y :: (v ++ (b ++ t))))) = u ++ x :: (s ++ (v ++ (b ++ y :: t))) := by
  simp only [run_append]
  rw [carry_front]
  have turn₁ := turn_front (x :: s) ((y :: (v ++ (b ++ t))) ++ u)
  simp only [List.length_cons, List.cons_append, List.append_assoc] at turn₁ ⊢
  rw [turn₁]
  have carry₂ := carry_front y (v ++ b) (t ++ (u ++ x :: s))
  simp only [List.append_assoc] at carry₂
  rw [carry₂]
  simpa only [List.length_cons, List.cons_append, List.append_assoc] using
    turn_front (y :: t) ((u ++ x :: s) ++ (v ++ b))

private theorem even_end (x z y w : ℕ) (s t : List ℕ) :
    run (carry 1 ++ turn (s.length + 1) ++ [false]) (x :: z :: (s ++ y :: w :: t)) =
      w :: y :: (t ++ z :: x :: s) := by
  simp only [run_append]
  have h := carry_front x [z] (s ++ y :: w :: t)
  simp only [List.length_cons, List.length_nil, List.singleton_append] at h
  rw [h]
  have hturn := turn_front (x :: s) ((y :: w :: t) ++ [z])
  simp only [List.length_cons, List.cons_append, List.append_assoc] at hturn ⊢
  rw [hturn]
  simp [run, step, exch, List.append_assoc]

private theorem even_word (k m : ℕ) (u s v t : List ℕ)
    (hu : u.length = k + 2) (hv : v.length = k + 2)
    (hs : u.length + s.length = m) (ht : v.length + t.length = m) :
    ∃ w : List Bool, w.length = (2*k+1)*m+(k+2)*(k+1) ∧
      run w (u ++ s ++ v ++ t) = v.reverse ++ t ++ u.reverse ++ s := by
  induction k generalizing u s v t with
  | zero =>
    obtain ⟨x,z,rfl⟩ := List.length_eq_two.mp hu
    obtain ⟨y,w,rfl⟩ := List.length_eq_two.mp hv
    refine ⟨carry 1 ++ turn (s.length+1) ++ [false], ?_, ?_⟩
    · simp only [List.length_append, carry_length, turn_length, List.length_cons,
        List.length_nil] at hs ⊢
      omega
    · simpa [List.append_assoc] using even_end x z y w s t
  | succ k ih =>
    cases u with
    | nil => simp at hu
    | cons x u =>
      cases v with
      | nil => simp at hv
      | cons y v =>
        simp only [List.length_cons] at hu hv hs ht
        obtain ⟨w,hw,hw_run⟩ := ih u (x::s) v (y::t) (by omega) (by omega)
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hs)
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ht)
        let stage := carry u.length ++ turn (s.length+1) ++ carry v.length ++ turn (t.length+1)
        refine ⟨stage ++ w, ?_, ?_⟩
        · have hstage : stage.length = 2*m+2*(k+2) := by
            simp only [stage,List.length_append,carry_length,turn_length]
            omega
          rw [List.length_append,hstage,hw]
          ring
        · rw [run_append]
          have hstep := cycle_step x y u s v [] t
          simp only [List.append_nil,List.nil_append] at hstep
          have heq : run stage (x :: u ++ s ++ y :: v ++ t) = u ++ (x::s) ++ v ++ (y::t) := by
            simpa [stage,List.append_assoc] using hstep
          rw [heq]
          simpa [List.append_assoc] using hw_run

private theorem odd_end (x z y p q : ℕ) (s t : List ℕ) :
    run (carry 1 ++ turn (s.length + 1) ++ carry 2) (x :: z :: (s ++ y :: p :: q :: t)) =
      y :: (t ++ z :: x :: (s ++ [p,q])) := by
  simp only [run_append]
  have h := carry_front x [z] (s ++ y :: p :: q :: t)
  simp only [List.length_cons, List.length_nil, List.singleton_append] at h
  rw [h]
  have hturn := turn_front (x :: s) ((y :: p :: q :: t) ++ [z])
  simp only [List.length_cons, List.cons_append, List.append_assoc] at hturn ⊢
  rw [hturn]
  simpa [List.append_assoc] using carry_front y [p,q] (t ++ z :: x :: s)

private theorem odd_word (k m : ℕ) (p q : ℕ) (u s v t : List ℕ)
    (hu : u.length = k + 2) (hv : v.length = k + 1)
    (hs : u.length + s.length = m) (ht : v.length + t.length + 1 = m) :
    ∃ w : List Bool, w.length = (2*k+1)*m+(k+2)*(k+1)+2*k+3 ∧
      run w (u ++ s ++ v ++ p :: q :: t) = v.reverse ++ t ++ u.reverse ++ s ++ [p,q] := by
  induction k generalizing u s v t with
  | zero =>
    obtain ⟨x,z,rfl⟩ := List.length_eq_two.mp hu
    obtain ⟨y,rfl⟩ := List.length_eq_one_iff.mp hv
    refine ⟨carry 1 ++ turn (s.length+1) ++ carry 2, ?_, ?_⟩
    · simp only [List.length_append, carry_length, turn_length, List.length_cons,
        List.length_nil] at hs ⊢
      omega
    · simpa [List.append_assoc] using odd_end x z y p q s t
  | succ k ih =>
    cases u with
    | nil => simp at hu
    | cons x u =>
      cases v with
      | nil => simp at hv
      | cons y v =>
        simp only [List.length_cons] at hu hv hs ht
        obtain ⟨w,hw,hw_run⟩ := ih u (x::s) v (y::t) (by omega) (by omega)
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hs)
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ht)
        let stage := carry u.length ++ turn (s.length+1) ++ carry (v ++ [p,q]).length ++ turn (t.length+1)
        refine ⟨stage ++ w, ?_, ?_⟩
        · have hstage : stage.length = 2*m+2*(k+2)+2 := by
            simp only [stage,List.length_append,carry_length,turn_length,List.length_cons,List.length_nil]
            omega
          rw [List.length_append,hstage,hw]
          ring
        · rw [run_append]
          have heq : run stage (x :: u ++ s ++ y :: v ++ p :: q :: t) = u ++ (x::s) ++ v ++ p :: q :: y :: t := by
            simpa [stage,List.append_assoc] using cycle_step x y u s v [p,q] t
          rw [heq]
          simpa [List.append_assoc] using hw_run

private theorem reversal_even (n m : ℕ) (hn : n = 2*m) (hm : 2 ≤ m) :
    4 * a n + 8*n ≤ 3*n^2 := by
  let l := (List.range n).reverse
  let A := l.take m
  let B := l.drop m
  have hA : A.length = m := by simp [A,l] <;> omega
  have hB : B.length = m := by simp [B,l] <;> omega
  have hAB : A ++ B = l := List.take_append_drop m l
  let k := m-2
  have hk : k+2=m := by dsimp [k]; omega
  obtain ⟨w,hw,hr⟩ := even_word k m B.reverse [] A.reverse []
    (by simpa [hB] using hk.symm) (by simpa [hA] using hk.symm) (by simp [hB]) (by simp [hA])
  have run_w : run w (List.range n) = (List.range n).reverse := by
    have hrev : B.reverse ++ A.reverse = List.range n := by
      rw [← List.reverse_append, hAB]
      simp [l]
    simpa [hrev,hAB,l] using hr
  have amin : a n ≤ w.length := Nat.sInf_le ⟨w,rfl,run_w⟩
  have bound : 4 * w.length + 8*n = 3*n^2 := by
    rw [hw,hn,← hk]
    ring
  omega

private theorem reversal_odd (n m : ℕ) (hn : n = 2*m+1) (hm : 2 ≤ m) :
    4 * a n + 10*n ≤ 3*n^2+15 := by
  let l := (List.range n).reverse
  let A := l.take (m-1)
  let B := (l.drop (m-1)).take m
  let C := (l.drop (m-1)).drop m
  have hA : A.length = m-1 := by simp [A,l] <;> omega
  have hB : B.length = m := by simp [B,l] <;> omega
  have hC : C.length = 2 := by simp [C,l] <;> omega
  have hABC : A ++ B ++ C = l := by rw [List.append_assoc]; simp only [A,B,C,List.take_append_drop]
  obtain ⟨p,q,hpq⟩ := List.length_eq_two.mp hC
  let k := m-2
  have hk : k+2=m := by dsimp [k]; omega
  obtain ⟨w,hw,hr⟩ := odd_word k m p q B.reverse [] A.reverse []
    (by simpa [hB] using hk.symm) (by simp [hA]; omega) (by simp [hB]) (by simp [hA]; omega)
  have hrev : List.range n = q :: p :: (B.reverse ++ A.reverse) := by
    have h := congrArg List.reverse hABC
    simpa [List.reverse_append,hpq,l,List.append_assoc] using h.symm
  let z := [false,true,true] ++ w
  have run_z : run z (List.range n) = (List.range n).reverse := by
    calc
      run z (List.range n) = run w (run [false,true,true] (q :: p :: (B.reverse ++ A.reverse))) := by
        rw [hrev, show z = [false,true,true] ++ w by rfl, run_append]
      _ = run w (B.reverse ++ A.reverse ++ [p,q]) := by simp [run,step,exch,List.append_assoc]
      _ = A ++ B ++ [p,q] := by simpa [List.append_assoc] using hr
      _ = (List.range n).reverse := by rw [← hpq, hABC]
  have amin : a n ≤ z.length := Nat.sInf_le ⟨z,rfl,run_z⟩
  have bound : 4 * z.length + 10*n = 3*n^2+15 := by
    simp only [z,List.length_append,List.length_cons,List.length_nil,hw,hn]
    rw [← hk]
    ring
  omega

end OMA.ReversalUpper

theorem OMA.solution : OMA.R_oeis_a048200_R1.H2 := by
  intro n hn
  constructor
  · rintro ⟨m,hm⟩
    exact OMA.ReversalUpper.reversal_even n m (by omega) (by omega)
  · rintro ⟨m,hm⟩
    exact OMA.ReversalUpper.reversal_odd n m (by omega) (by omega)
