import FormalConjectures.Wikipedia.BusyBeaver
import Mathlib.Tactic

/-!
# Reduction of BB(5) = 47,176,870

This file proves:
1. The exact lower bound `47176870 ≤ BB 5` via a formal accelerated macro-step simulation
   of the Marxen–Buntrock 5-state Busy Beaver champion (`1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA`),
   establishing that it halts at step 47,176,870 without `native_decide` or brute-force unfolding.
2. Canonicalization of any 5-state `Candidate 5` to an indexed `Machine (Fin 2) (Fin 5)` with
   initial transition `M 0 0 = some (some 1, Stmt.write a Dir.right)` (`a ∈ {0, 1}`) via
   state-renaming and left-right mirror symmetry (ruling out halting and self-looping starts).
3. Reduction of `BusyBeaver.BB_5` to the two Tree Normal Form (TNF) upper-bound branches
   `H1` (`a = 0`) and `H2` (`a = 1`).
-/

namespace OMA.R_BusyBeaver_BB_5_R1

open Turing Turing.BusyBeaver BusyBeaver

/- ## General multiStep and ListBlank helpers -/

private lemma multiStep_add {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (s : Cfg Γ Λ) (m n : ℕ) :
    M.multiStep s (m + n) = (M.multiStep s m).bind (fun t => M.multiStep t n) := by
  induction n with
  | zero =>
    cases M.multiStep s m <;> rfl
  | succ n ih =>
    rw [← Nat.add_assoc, Machine.multiStep_succ, ih]
    cases M.multiStep s m with
    | none => rfl
    | some t =>
      simp only [Option.bind_some, Machine.multiStep_succ]

private lemma multiStep_trans {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {M : Machine Γ Λ} {s t u : Cfg Γ Λ} {m n : ℕ}
    (h1 : M.multiStep s m = some t) (h2 : M.multiStep t n = some u) :
    M.multiStep s (m + n) = some u := by
  rw [multiStep_add, h1, Option.bind_some, h2]

private lemma append_replicate_succ_right {Γ : Type*} [Inhabited Γ] (a : ℕ) (x : Γ) (L : ListBlank Γ) :
    ListBlank.append (List.replicate a x) (L.cons x) = ListBlank.append (List.replicate (a + 1) x) L := by
  induction a with
  | zero => rfl
  | succ a ih =>
    simp only [List.replicate_succ, ListBlank.append, ih]

private lemma append_replicate_add {Γ : Type*} [Inhabited Γ] (a b : ℕ) (x : Γ) (L : ListBlank Γ) :
    ListBlank.append (List.replicate (a + b) x) L =
      ListBlank.append (List.replicate a x) (ListBlank.append (List.replicate b x) L) := by
  rw [List.replicate_add, ListBlank.append_assoc]

private lemma head_default_fin2 : (default : ListBlank (Fin 2)).head = (0 : Fin 2) := rfl

private lemma tail_default_fin2 : (default : ListBlank (Fin 2)).tail = (default : ListBlank (Fin 2)) := rfl

/- ## Lower bound: Marxen–Buntrock 5-state champion halts at 47,176,870 -/

private lemma sweep_B_right (M : Machine (Fin 2) (Fin 5))
    (h11 : M 1 1 = some (some 1, Stmt.write 1 Dir.right)) :
    ∀ a : ℕ, ∀ L R : ListBlank (Fin 2),
      M.multiStep ⟨some 1, Tape.mk' L (ListBlank.append (List.replicate a 1) R)⟩ a =
        some ⟨some 1, Tape.mk' (ListBlank.append (List.replicate a 1) L) R⟩ := by
  intro a
  induction a with
  | zero =>
    intro L R
    rfl
  | succ a ih =>
    intro L R
    have hstep : M.multiStep ⟨some 1, Tape.mk' L (ListBlank.append (List.replicate (a + 1) 1) R)⟩ 1 =
        some ⟨some 1, Tape.mk' (L.cons 1) (ListBlank.append (List.replicate a 1) R)⟩ := by
      simp only [Machine.multiStep_one, Machine.step, List.replicate_succ, ListBlank.append,
        Tape.mk', ListBlank.head_cons, ListBlank.tail_cons, h11, Option.map_some, Tape.write,
        Tape.move]
    have hrest := ih (L.cons 1) R
    rw [append_replicate_succ_right] at hrest
    have htot := multiStep_trans hstep hrest
    rwa [Nat.add_comm 1 a] at htot

private lemma sweep_D_left (M : Machine (Fin 2) (Fin 5))
    (h31 : M 3 1 = some (some 3, Stmt.write 1 Dir.left)) :
    ∀ a : ℕ, ∀ L R : ListBlank (Fin 2),
      M.multiStep ⟨some 3, ⟨(ListBlank.append (List.replicate a 1) L).head,
          (ListBlank.append (List.replicate a 1) L).tail, R⟩⟩ a =
        some ⟨some 3, ⟨L.head, L.tail, ListBlank.append (List.replicate a 1) R⟩⟩ := by
  intro a
  induction a with
  | zero =>
    intro L R
    rfl
  | succ a ih =>
    intro L R
    have hstep : M.multiStep ⟨some 3, ⟨(ListBlank.append (List.replicate (a + 1) 1) L).head,
          (ListBlank.append (List.replicate (a + 1) 1) L).tail, R⟩⟩ 1 =
        some ⟨some 3, ⟨(ListBlank.append (List.replicate a 1) L).head,
          (ListBlank.append (List.replicate a 1) L).tail, R.cons 1⟩⟩ := by
      simp only [Machine.multiStep_one, Machine.step, List.replicate_succ, ListBlank.append,
        ListBlank.head_cons, ListBlank.tail_cons, h31, Option.map_some, Tape.write, Tape.move]
    have hrest := ih L (R.cons 1)
    rw [append_replicate_succ_right] at hrest
    have htot := multiStep_trans hstep hrest
    rwa [Nat.add_comm 1 a] at htot

private lemma sweep_ACE_left (M : Machine (Fin 2) (Fin 5))
    (h01 : M 0 1 = some (some 2, Stmt.write 1 Dir.left))
    (h21 : M 2 1 = some (some 4, Stmt.write 0 Dir.left))
    (h41 : M 4 1 = some (some 0, Stmt.write 0 Dir.left)) :
    ∀ k : ℕ, ∀ L R : ListBlank (Fin 2),
      M.multiStep ⟨some 0, ⟨(ListBlank.append (List.replicate (3 * k) 1) L).head,
          (ListBlank.append (List.replicate (3 * k) 1) L).tail, R⟩⟩ (3 * k) =
        some ⟨some 0, ⟨L.head, L.tail,
          ListBlank.append (List.flatten (List.replicate k [(0 : Fin 2), 0, 1])) R⟩⟩ := by
  intro k
  induction k with
  | zero =>
    intro L R
    rfl
  | succ k ih =>
    intro L R
    have h3 : 3 * (k + 1) = 3 + 3 * k := by ring
    rw [h3, append_replicate_add]
    have hstep3 : M.multiStep
        ⟨some 0, ⟨(ListBlank.append (List.replicate 3 1) (ListBlank.append (List.replicate (3 * k) 1) L)).head,
          (ListBlank.append (List.replicate 3 1) (ListBlank.append (List.replicate (3 * k) 1) L)).tail, R⟩⟩ 3 =
        some ⟨some 0, ⟨(ListBlank.append (List.replicate (3 * k) 1) L).head,
          (ListBlank.append (List.replicate (3 * k) 1) L).tail, ListBlank.append [(0 : Fin 2), 0, 1] R⟩⟩ := by
      simp only [Machine.multiStep_succ, Machine.multiStep_zero, Option.bind_some, Machine.step,
        List.replicate_succ, List.replicate_zero, ListBlank.append, ListBlank.head_cons,
        ListBlank.tail_cons, h01, h21, h41, Option.map_some, Tape.write, Tape.move]
    have hrest := ih L (ListBlank.append [(0 : Fin 2), 0, 1] R)
    have hflat : ListBlank.append (List.flatten (List.replicate k [(0 : Fin 2), 0, 1]))
          (ListBlank.append [(0 : Fin 2), 0, 1] R) =
        ListBlank.append (List.flatten (List.replicate (k + 1) [(0 : Fin 2), 0, 1])) R := by
      rw [← ListBlank.append_assoc]
      congr 1
      have hrep : List.replicate (k + 1) [(0 : Fin 2), 0, 1] =
          List.replicate k [(0 : Fin 2), 0, 1] ++ [[(0 : Fin 2), 0, 1]] := by
        rw [List.replicate_add]
        rfl
      rw [hrep, List.flatten_append]
      simp
    rw [hflat] at hrest
    exact multiStep_trans hstep3 hrest

private lemma expand_one_round (M : Machine (Fin 2) (Fin 5))
    (h00 : M 0 0 = some (some 1, Stmt.write 1 Dir.right))
    (h10 : M 1 0 = some (some 2, Stmt.write 1 Dir.right))
    (h11 : M 1 1 = some (some 1, Stmt.write 1 Dir.right))
    (h20 : M 2 0 = some (some 3, Stmt.write 1 Dir.right))
    (h30 : M 3 0 = some (some 0, Stmt.write 1 Dir.left))
    (h31 : M 3 1 = some (some 3, Stmt.write 1 Dir.left))
    (a : ℕ) (R : ListBlank (Fin 2)) :
    M.multiStep ⟨some 0, ⟨0, default, ListBlank.append (List.replicate a 1) (ListBlank.append [0, 0, 1] R)⟩⟩ (2 * a + 8) =
      some ⟨some 0, ⟨0, default, ListBlank.append (List.replicate (a + 5) 1) R⟩⟩ := by
  have hs1 : M.multiStep
      ⟨some 0, ⟨0, default, ListBlank.append (List.replicate a 1) (ListBlank.append [0, 0, 1] R)⟩⟩ 1 =
      some ⟨some 1, Tape.mk' (ListBlank.append (List.replicate 1 1) default)
        (ListBlank.append (List.replicate a 1) (ListBlank.append [0, 0, 1] R))⟩ := by
    simp only [Machine.multiStep_one, Machine.step, h00, Option.map_some, Tape.write, Tape.move,
      Tape.mk', List.replicate_one, ListBlank.append]
  have hs2 := sweep_B_right M h11 a (ListBlank.append (List.replicate 1 1) default) (ListBlank.append [0, 0, 1] R)
  rw [← append_replicate_add] at hs2
  have hs3 : M.multiStep
      ⟨some 1, Tape.mk' (ListBlank.append (List.replicate (a + 1) 1) default) (ListBlank.append [0, 0, 1] R)⟩ 2 =
      some ⟨some 3, ⟨(ListBlank.append (List.replicate (a + 4) 1) default).head,
        (ListBlank.append (List.replicate (a + 4) 1) default).tail, R⟩⟩ := by
    have h4 : ListBlank.append (List.replicate (a + 4) (1 : Fin 2)) default =
        ((((ListBlank.append (List.replicate (a + 1) (1 : Fin 2)) default).cons 1).cons 1).cons 1) := by
      rw [show a + 4 = 3 + (a + 1) by omega, append_replicate_add]
      rfl
    rw [h4]
    simp only [Machine.multiStep_succ, Machine.multiStep_zero, Option.bind_some, Machine.step,
      Tape.mk', ListBlank.append, ListBlank.head_cons, ListBlank.tail_cons, h10, h20,
      Option.map_some, Tape.write, Tape.move]
  have hs4 := sweep_D_left M h31 (a + 4) default R
  have hs5 : M.multiStep
      ⟨some 3, ⟨(default : ListBlank (Fin 2)).head, (default : ListBlank (Fin 2)).tail,
        ListBlank.append (List.replicate (a + 4) 1) R⟩⟩ 1 =
      some ⟨some 0, ⟨0, default, ListBlank.append (List.replicate (a + 5) 1) R⟩⟩ := by
    rw [head_default_fin2, tail_default_fin2]
    simp only [Machine.multiStep_one, Machine.step, h30, Option.map_some, Tape.write, Tape.move,
      head_default_fin2, tail_default_fin2]
    congr 2
  have h12 := multiStep_trans hs1 hs2
  have h123 := multiStep_trans h12 hs3
  have h1234 := multiStep_trans h123 hs4
  have h12345 := multiStep_trans h1234 hs5
  rwa [show 1 + a + 2 + (a + 4) + 1 = 2 * a + 8 by omega] at h12345

private lemma expand_rounds (M : Machine (Fin 2) (Fin 5))
    (h00 : M 0 0 = some (some 1, Stmt.write 1 Dir.right))
    (h10 : M 1 0 = some (some 2, Stmt.write 1 Dir.right))
    (h11 : M 1 1 = some (some 1, Stmt.write 1 Dir.right))
    (h20 : M 2 0 = some (some 3, Stmt.write 1 Dir.right))
    (h30 : M 3 0 = some (some 0, Stmt.write 1 Dir.left))
    (h31 : M 3 1 = some (some 3, Stmt.write 1 Dir.left)) :
    ∀ m a : ℕ, ∀ R : ListBlank (Fin 2),
      M.multiStep ⟨some 0, ⟨0, default,
          ListBlank.append (List.replicate a 1)
            (ListBlank.append (List.flatten (List.replicate m [(0 : Fin 2), 0, 1])) R)⟩⟩
        (5 * m * m + (2 * a + 3) * m) =
        some ⟨some 0, ⟨0, default, ListBlank.append (List.replicate (a + 5 * m) 1) R⟩⟩ := by
  intro m
  induction m with
  | zero =>
    intro a R
    simp
  | succ m ih =>
    intro a R
    have hflat : ListBlank.append (List.flatten (List.replicate (m + 1) [(0 : Fin 2), 0, 1])) R =
        ListBlank.append [(0 : Fin 2), 0, 1]
          (ListBlank.append (List.flatten (List.replicate m [(0 : Fin 2), 0, 1])) R) := by
      rw [List.replicate_succ, List.flatten_cons, ListBlank.append_assoc]
    rw [hflat]
    have h1 := expand_one_round M h00 h10 h11 h20 h30 h31 a
      (ListBlank.append (List.flatten (List.replicate m [(0 : Fin 2), 0, 1])) R)
    have h2 := ih (a + 5) R
    have htot := multiStep_trans h1 h2
    have hsteps : 2 * a + 8 + (5 * m * m + (2 * (a + 5) + 3) * m) =
        5 * (m + 1) * (m + 1) + (2 * a + 3) * (m + 1) := by ring
    have halen : a + 5 + 5 * m = a + 5 * (m + 1) := by ring
    rwa [hsteps, halen] at htot

private lemma phase_to_A (M : Machine (Fin 2) (Fin 5))
    (h00 : M 0 0 = some (some 1, Stmt.write 1 Dir.right))
    (h10 : M 1 0 = some (some 2, Stmt.write 1 Dir.right))
    (h11 : M 1 1 = some (some 1, Stmt.write 1 Dir.right))
    (h20 : M 2 0 = some (some 3, Stmt.write 1 Dir.right))
    (h30 : M 3 0 = some (some 0, Stmt.write 1 Dir.left))
    (n : ℕ) :
    M.multiStep ⟨some 0, ⟨0, default, ListBlank.append (List.replicate n 1) default⟩⟩ (n + 4) =
      some ⟨some 0, ⟨(ListBlank.append (List.replicate (n + 3) 1) default).head,
        (ListBlank.append (List.replicate (n + 3) 1) default).tail,
        ListBlank.append (List.replicate 1 1) default⟩⟩ := by
  have hs1 : M.multiStep ⟨some 0, ⟨0, default, ListBlank.append (List.replicate n 1) default⟩⟩ 1 =
      some ⟨some 1, Tape.mk' (ListBlank.append (List.replicate 1 1) default)
        (ListBlank.append (List.replicate n 1) default)⟩ := by
    simp only [Machine.multiStep_one, Machine.step, h00, Option.map_some, Tape.write, Tape.move,
      Tape.mk', List.replicate_one, ListBlank.append]
  have hs2 := sweep_B_right M h11 n (ListBlank.append (List.replicate 1 1) default) default
  rw [← append_replicate_add] at hs2
  have hs3 : M.multiStep ⟨some 1, Tape.mk' (ListBlank.append (List.replicate (n + 1) 1) default) default⟩ 3 =
      some ⟨some 0, ⟨(ListBlank.append (List.replicate (n + 3) 1) default).head,
        (ListBlank.append (List.replicate (n + 3) 1) default).tail,
        ListBlank.append (List.replicate 1 1) default⟩⟩ := by
    have h3 : ListBlank.append (List.replicate (n + 3) (1 : Fin 2)) default =
        (((ListBlank.append (List.replicate (n + 1) (1 : Fin 2)) default).cons 1).cons 1) := by
      rw [show n + 3 = 2 + (n + 1) by omega, append_replicate_add]
      rfl
    rw [h3]
    simp only [Machine.multiStep_succ, Machine.multiStep_zero, Option.bind_some, Machine.step,
      Tape.mk', head_default_fin2, tail_default_fin2, ListBlank.head_cons, ListBlank.tail_cons,
      List.replicate_one, ListBlank.append, h10, h20, h30, Option.map_some, Tape.write, Tape.move]
  have h123 := multiStep_trans (multiStep_trans hs1 hs2) hs3
  rwa [show 1 + n + 3 = n + 4 by omega] at h123

private lemma collatz_3k (M : Machine (Fin 2) (Fin 5))
    (h00 : M 0 0 = some (some 1, Stmt.write 1 Dir.right))
    (h01 : M 0 1 = some (some 2, Stmt.write 1 Dir.left))
    (h10 : M 1 0 = some (some 2, Stmt.write 1 Dir.right))
    (h11 : M 1 1 = some (some 1, Stmt.write 1 Dir.right))
    (h20 : M 2 0 = some (some 3, Stmt.write 1 Dir.right))
    (h21 : M 2 1 = some (some 4, Stmt.write 0 Dir.left))
    (h30 : M 3 0 = some (some 0, Stmt.write 1 Dir.left))
    (h31 : M 3 1 = some (some 3, Stmt.write 1 Dir.left))
    (h41 : M 4 1 = some (some 0, Stmt.write 0 Dir.left))
    (k : ℕ) :
    M.multiStep ⟨some 0, ⟨0, default, ListBlank.append (List.replicate (3 * k) 1) default⟩⟩
      (5 * k * k + 19 * k + 15) =
      some ⟨some 0, ⟨0, default, ListBlank.append (List.replicate (5 * k + 6) 1) default⟩⟩ := by
  have h1 := phase_to_A M h00 h10 h11 h20 h30 (3 * k)
  rw [show 3 * k + 3 = 3 * (k + 1) by omega] at h1
  have h2 := sweep_ACE_left M h01 h21 h41 (k + 1) default (ListBlank.append (List.replicate 1 1) default)
  rw [head_default_fin2, tail_default_fin2] at h2
  have h3 := expand_rounds M h00 h10 h11 h20 h30 h31 (k + 1) 0 (ListBlank.append (List.replicate 1 1) default)
  simp only [List.replicate_zero, ListBlank.append, zero_add] at h3
  rw [← append_replicate_add] at h3
  have htot := multiStep_trans (multiStep_trans h1 h2) h3
  have hsteps : 3 * k + 4 + 3 * (k + 1) + (5 * (k + 1) * (k + 1) + (2 * 0 + 3) * (k + 1)) =
      5 * k * k + 19 * k + 15 := by ring
  have hlen : 5 * (k + 1) + 1 = 5 * k + 6 := by ring
  rwa [hsteps, hlen] at htot

private lemma collatz_3k_1 (M : Machine (Fin 2) (Fin 5))
    (h00 : M 0 0 = some (some 1, Stmt.write 1 Dir.right))
    (h01 : M 0 1 = some (some 2, Stmt.write 1 Dir.left))
    (h10 : M 1 0 = some (some 2, Stmt.write 1 Dir.right))
    (h11 : M 1 1 = some (some 1, Stmt.write 1 Dir.right))
    (h20 : M 2 0 = some (some 3, Stmt.write 1 Dir.right))
    (h21 : M 2 1 = some (some 4, Stmt.write 0 Dir.left))
    (h30 : M 3 0 = some (some 0, Stmt.write 1 Dir.left))
    (h31 : M 3 1 = some (some 3, Stmt.write 1 Dir.left))
    (h41 : M 4 1 = some (some 0, Stmt.write 0 Dir.left))
    (k : ℕ) :
    M.multiStep ⟨some 0, ⟨0, default, ListBlank.append (List.replicate (3 * k + 1) 1) default⟩⟩
      (5 * k * k + 25 * k + 27) =
      some ⟨some 0, ⟨0, default, ListBlank.append (List.replicate (5 * k + 9) 1) default⟩⟩ := by
  have h1 := phase_to_A M h00 h10 h11 h20 h30 (3 * k + 1)
  rw [show 3 * k + 1 + 3 = 3 * (k + 1) + 1 by omega] at h1
  have h2 := sweep_ACE_left M h01 h21 h41 (k + 1)
    (ListBlank.append (List.replicate 1 1) default)
    (ListBlank.append (List.replicate 1 1) default)
  rw [← append_replicate_add] at h2
  set tailR := ListBlank.append (List.flatten (List.replicate (k + 1) [(0 : Fin 2), 0, 1]))
    (ListBlank.append (List.replicate 1 1) default)
  have hmid : M.multiStep
      ⟨some 0, ⟨(ListBlank.append (List.replicate 1 (1 : Fin 2)) default).head,
        (ListBlank.append (List.replicate 1 (1 : Fin 2)) default).tail, tailR⟩⟩ 5 =
      some ⟨some 0, ⟨0, default, ListBlank.append (List.replicate 3 1) tailR⟩⟩ := by
    simp only [Machine.multiStep_succ, Machine.multiStep_zero, Option.bind_some, Machine.step,
      List.replicate_succ, List.replicate_zero, ListBlank.append, ListBlank.head_cons,
      ListBlank.tail_cons, head_default_fin2, tail_default_fin2,
      h01, h20, h31, h30, Option.map_some, Tape.write, Tape.move]
  have h3 := expand_rounds M h00 h10 h11 h20 h30 h31 (k + 1) 3
    (ListBlank.append (List.replicate 1 1) default)
  rw [← append_replicate_add] at h3
  have htot := multiStep_trans (multiStep_trans (multiStep_trans h1 h2) hmid) h3
  have hsteps : 3 * k + 1 + 4 + 3 * (k + 1) + 5 +
      (5 * (k + 1) * (k + 1) + (2 * 3 + 3) * (k + 1)) = 5 * k * k + 25 * k + 27 := by ring
  have hlen : 3 + 5 * (k + 1) + 1 = 5 * k + 9 := by ring
  rwa [hsteps, hlen] at htot

private lemma collatz_3k_2_halt (M : Machine (Fin 2) (Fin 5))
    (h00 : M 0 0 = some (some 1, Stmt.write 1 Dir.right))
    (h01 : M 0 1 = some (some 2, Stmt.write 1 Dir.left))
    (h10 : M 1 0 = some (some 2, Stmt.write 1 Dir.right))
    (h11 : M 1 1 = some (some 1, Stmt.write 1 Dir.right))
    (h20 : M 2 0 = some (some 3, Stmt.write 1 Dir.right))
    (h21 : M 2 1 = some (some 4, Stmt.write 0 Dir.left))
    (h30 : M 3 0 = some (some 0, Stmt.write 1 Dir.left))
    (h40 : M 4 0 = some (none, Stmt.write 1 Dir.right))
    (h41 : M 4 1 = some (some 0, Stmt.write 0 Dir.left))
    (k : ℕ) :
    ∃ T : Tape (Fin 2),
      M.multiStep ⟨some 0, ⟨0, default, ListBlank.append (List.replicate (3 * k + 2) 1) default⟩⟩
        (6 * k + 12) = some ⟨none, T⟩ := by
  have h1 := phase_to_A M h00 h10 h11 h20 h30 (3 * k + 2)
  rw [show 3 * k + 2 + 3 = 3 * (k + 1) + 2 by omega] at h1
  have h2 := sweep_ACE_left M h01 h21 h41 (k + 1)
    (ListBlank.append (List.replicate 2 1) default)
    (ListBlank.append (List.replicate 1 1) default)
  rw [← append_replicate_add] at h2
  set tailR := ListBlank.append (List.flatten (List.replicate (k + 1) [(0 : Fin 2), 0, 1]))
    (ListBlank.append (List.replicate 1 1) default)
  have hfin : ∃ T : Tape (Fin 2),
      M.multiStep ⟨some 0, ⟨(ListBlank.append (List.replicate 2 (1 : Fin 2)) default).head,
        (ListBlank.append (List.replicate 2 (1 : Fin 2)) default).tail, tailR⟩⟩ 3 =
        some ⟨none, T⟩ := by
    simp only [Machine.multiStep_succ, Machine.multiStep_zero, Option.bind_some, Machine.step,
      List.replicate_succ, List.replicate_zero, ListBlank.append, ListBlank.head_cons,
      ListBlank.tail_cons, head_default_fin2, tail_default_fin2,
      h01, h21, h40, Option.map_some, Tape.write, Tape.move]
    exact ⟨_, rfl⟩
  obtain ⟨T, hT⟩ := hfin
  refine ⟨T, ?_⟩
  have htot := multiStep_trans (multiStep_trans h1 h2) hT
  rwa [show 3 * k + 2 + 4 + 3 * (k + 1) + 3 = 6 * k + 12 by omega] at htot

private lemma exists_champion_47176870 :
    ∃ C : Candidate 5, C.M.haltingNumber = (47176870 : ℕ) := by
  let M : Machine (Fin 2) (Fin 5) := fun q s =>
    match q.val, s.val with
    | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
    | 0, _ => some (some 2, Stmt.write 1 Dir.left)
    | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
    | 1, _ => some (some 1, Stmt.write 1 Dir.right)
    | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
    | 2, _ => some (some 4, Stmt.write 0 Dir.left)
    | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
    | 3, _ => some (some 3, Stmt.write 1 Dir.left)
    | _, 0 => some (none, Stmt.write 1 Dir.right)
    | _, _ => some (some 0, Stmt.write 0 Dir.left)
  have h00 : M 0 0 = some (some 1, Stmt.write 1 Dir.right) := rfl
  have h01 : M 0 1 = some (some 2, Stmt.write 1 Dir.left) := rfl
  have h10 : M 1 0 = some (some 2, Stmt.write 1 Dir.right) := rfl
  have h11 : M 1 1 = some (some 1, Stmt.write 1 Dir.right) := rfl
  have h20 : M 2 0 = some (some 3, Stmt.write 1 Dir.right) := rfl
  have h21 : M 2 1 = some (some 4, Stmt.write 0 Dir.left) := rfl
  have h30 : M 3 0 = some (some 0, Stmt.write 1 Dir.left) := rfl
  have h31 : M 3 1 = some (some 3, Stmt.write 1 Dir.left) := rfl
  have h40 : M 4 0 = some (none, Stmt.write 1 Dir.right) := rfl
  have h41 : M 4 1 = some (some 0, Stmt.write 0 Dir.left) := rfl
  have s01 := collatz_3k M h00 h01 h10 h11 h20 h21 h30 h31 h41 0
  have s02 := collatz_3k M h00 h01 h10 h11 h20 h21 h30 h31 h41 2
  have s03 := collatz_3k_1 M h00 h01 h10 h11 h20 h21 h30 h31 h41 5
  have s04 := collatz_3k_1 M h00 h01 h10 h11 h20 h21 h30 h31 h41 11
  have s05 := collatz_3k_1 M h00 h01 h10 h11 h20 h21 h30 h31 h41 21
  have s06 := collatz_3k M h00 h01 h10 h11 h20 h21 h30 h31 h41 38
  have s07 := collatz_3k_1 M h00 h01 h10 h11 h20 h21 h30 h31 h41 65
  have s08 := collatz_3k_1 M h00 h01 h10 h11 h20 h21 h30 h31 h41 111
  have s09 := collatz_3k M h00 h01 h10 h11 h20 h21 h30 h31 h41 188
  have s10 := collatz_3k_1 M h00 h01 h10 h11 h20 h21 h30 h31 h41 315
  have s11 := collatz_3k M h00 h01 h10 h11 h20 h21 h30 h31 h41 528
  have s12 := collatz_3k M h00 h01 h10 h11 h20 h21 h30 h31 h41 882
  have s13 := collatz_3k M h00 h01 h10 h11 h20 h21 h30 h31 h41 1472
  have s14 := collatz_3k_1 M h00 h01 h10 h11 h20 h21 h30 h31 h41 2455
  obtain ⟨T, s15⟩ := collatz_3k_2_halt M h00 h01 h10 h11 h20 h21 h30 h40 h41 4094
  norm_num only at s01 s02 s03 s04 s05 s06 s07 s08 s09 s10 s11 s12 s13 s14 s15
  have h15 := multiStep_trans s01 s02
  have h15 := multiStep_trans h15 s03
  have h15 := multiStep_trans h15 s04
  have h15 := multiStep_trans h15 s05
  have h15 := multiStep_trans h15 s06
  have h15 := multiStep_trans h15 s07
  have h15 := multiStep_trans h15 s08
  have h15 := multiStep_trans h15 s09
  have h15 := multiStep_trans h15 s10
  have h15 := multiStep_trans h15 s11
  have h15 := multiStep_trans h15 s12
  have h15 := multiStep_trans h15 s13
  have h15 := multiStep_trans h15 s14
  have h15 := multiStep_trans h15 s15
  norm_num only at h15
  have hinit : Machine.init ([] : List (Fin 2)) =
      (⟨some 0, ⟨0, default, ListBlank.append (List.replicate 0 1) default⟩⟩ : Cfg (Fin 2) (Fin 5)) := by
    rfl
  rw [← hinit] at h15
  have hstop : M.multiStep (Machine.init []) (47176870 + 1) = none := by
    rw [Machine.multiStep_succ, h15]
    rfl
  let C : Candidate 5 :=
    { Γ := Fin 2
      Λ := Fin 5
      Γ_fintype := inferInstance
      Γ_card := Fintype.card_fin _
      Γ_inhabited := inferInstance
      Λ_fintype := inferInstance
      Λ_card := Fintype.card_fin _
      Λ_inhabited := inferInstance
      M := M
      M_isHalting := (Machine.isHalting_iff_exists_haltsAt M).mpr ⟨47176870, hstop⟩ }
  exact ⟨C, Machine.haltingNumber_def M 47176870 ⟨⟨none, T⟩, h15⟩ hstop⟩

/- ## Normalization and TNF symmetry reduction -/

private lemma normalize_candidate (C : Candidate 5) :
    ∃ M : Machine (Fin 2) (Fin 5), M.IsHalting ∧ M.haltingNumber = C.M.haltingNumber := by
  classical
  let a := (Fintype.equivFinOfCardEq C.Γ_card).setValue default (default : Fin 2)
  let b := (Fintype.equivFinOfCardEq C.Λ_card).setValue default (default : Fin 5)
  let f : PointedMap C.Γ (Fin 2) := ⟨a, by simp [a]⟩
  let conf (s : Cfg C.Γ C.Λ) : Cfg (Fin 2) (Fin 5) := ⟨s.q.map b, s.tape.map f⟩
  let M : Machine (Fin 2) (Fin 5) := fun q t =>
    (C.M (b.symm q) (a.symm t)).map (fun (q', cmd) => (q'.map b, Stmt.write (f cmd.symbol) cmd.dir))
  have step (s : Cfg C.Γ C.Λ) : M.step (conf s) = (C.M.step s).map conf := by
    obtain ⟨q, T⟩ := s
    cases q with
    | none => rfl
    | some q =>
      simp only [Machine.step, conf, Option.map_some, Tape.map_fst, M]
      change ((C.M (b.symm (b q)) (a.symm (a T.head))).map _).map _ = _
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      cases h : C.M q T.head with
      | none => rfl
      | some z =>
        obtain ⟨q', ⟨t, d⟩⟩ := z
        simp [Tape.map_move, Tape.map_write]
  have start : conf (Machine.init []) = Machine.init [] := by
    simp [conf, Machine.init, Tape.map_mk₁, b]
  have trace (k : ℕ) : M.multiStep (Machine.init []) k = (C.M.multiStep (Machine.init []) k).map conf := by
    induction k with
    | zero => simp [start]
    | succ k ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
      cases he : C.M.multiStep (Machine.init []) k with
      | none => rfl
      | some s => exact step s
  have stops (k : ℕ) : M.HaltsAfter (Machine.init []) k ↔ C.M.HaltsAfter (Machine.init []) k := by
    simp only [Machine.HaltsAfter, trace, Option.map_eq_none_iff]
  refine ⟨M, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt _).mp C.M_isHalting
    exact (Machine.isHalting_iff_exists_haltsAt _).mpr ⟨k, (stops k).mpr hk⟩
  · unfold Machine.haltingNumber
    congr 1
    ext e
    constructor <;> rintro ⟨k, hk, rfl⟩
    · exact ⟨k, (stops k).mp hk, rfl⟩
    · exact ⟨k, (stops k).mpr hk, rfl⟩

private lemma mirror_machine (M : Machine (Fin 2) (Fin 5)) :
    ∃ M' : Machine (Fin 2) (Fin 5),
      (∀ q t, M' q t = (M q t).map fun (q', cmd) =>
        (q', Stmt.write cmd.symbol (match cmd.dir with | Dir.left => Dir.right | Dir.right => Dir.left))) ∧
      (M'.IsHalting ↔ M.IsHalting) ∧
      M'.haltingNumber = M.haltingNumber := by
  let flipDir : Dir → Dir
    | Dir.left => Dir.right
    | Dir.right => Dir.left
  let flipTape (T : Tape (Fin 2)) : Tape (Fin 2) := ⟨T.head, T.right, T.left⟩
  let flipCfg (s : Cfg (Fin 2) (Fin 5)) : Cfg (Fin 2) (Fin 5) := ⟨s.q, flipTape s.tape⟩
  let M' : Machine (Fin 2) (Fin 5) := fun q t =>
    (M q t).map fun (q', cmd) => (q', Stmt.write cmd.symbol (flipDir cmd.dir))
  have step (s : Cfg (Fin 2) (Fin 5)) : M'.step (flipCfg s) = (M.step s).map flipCfg := by
    obtain ⟨q, ⟨h, L, R⟩⟩ := s
    cases q with
    | none => rfl
    | some q =>
      simp only [Machine.step, flipCfg, flipTape, M']
      cases hM : M q h with
      | none => rfl
      | some z =>
        obtain ⟨q', ⟨a, d⟩⟩ := z
        cases d <;> rfl
  have start : flipCfg (Machine.init []) = Machine.init [] := rfl
  have trace (k : ℕ) : M'.multiStep (Machine.init []) k = (M.multiStep (Machine.init []) k).map flipCfg := by
    induction k with
    | zero => simp [start]
    | succ k ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
      cases he : M.multiStep (Machine.init []) k with
      | none => rfl
      | some s => exact step s
  have stops (k : ℕ) : M'.HaltsAfter (Machine.init []) k ↔ M.HaltsAfter (Machine.init []) k := by
    simp only [Machine.HaltsAfter, trace, Option.map_eq_none_iff]
  refine ⟨M', fun _ _ => rfl, ?_, ?_⟩
  · simp only [Machine.isHalting_iff_exists_haltsAt, stops]
  · unfold Machine.haltingNumber
    congr 1
    ext e
    constructor <;> rintro ⟨k, hk, rfl⟩
    · exact ⟨k, (stops k).mp hk, rfl⟩
    · exact ⟨k, (stops k).mpr hk, rfl⟩

private lemma perm_states (M : Machine (Fin 2) (Fin 5)) (e : Equiv.Perm (Fin 5)) (he0 : e 0 = 0) :
    ∃ M' : Machine (Fin 2) (Fin 5),
      (∀ q t, M' q t = (M (e.symm q) t).map fun (q', cmd) => (q'.map e, cmd)) ∧
      (M'.IsHalting ↔ M.IsHalting) ∧
      M'.haltingNumber = M.haltingNumber := by
  let conf (s : Cfg (Fin 2) (Fin 5)) : Cfg (Fin 2) (Fin 5) := ⟨s.q.map e, s.tape⟩
  let M' : Machine (Fin 2) (Fin 5) := fun q t =>
    (M (e.symm q) t).map fun (q', cmd) => (q'.map e, cmd)
  have step (s : Cfg (Fin 2) (Fin 5)) : M'.step (conf s) = (M.step s).map conf := by
    obtain ⟨q, T⟩ := s
    cases q with
    | none => rfl
    | some q =>
      simp only [Machine.step, conf, Option.map_some, M', Equiv.symm_apply_apply]
      cases hM : M q T.head with
      | none => rfl
      | some z =>
        obtain ⟨q', ⟨a, d⟩⟩ := z
        rfl
  have start : conf (Machine.init []) = Machine.init [] := by
    simp [conf, Machine.init, he0]
  have trace (k : ℕ) : M'.multiStep (Machine.init []) k = (M.multiStep (Machine.init []) k).map conf := by
    induction k with
    | zero => simp [start]
    | succ k ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
      cases he : M.multiStep (Machine.init []) k with
      | none => rfl
      | some s => exact step s
  have stops (k : ℕ) : M'.HaltsAfter (Machine.init []) k ↔ M.HaltsAfter (Machine.init []) k := by
    simp only [Machine.HaltsAfter, trace, Option.map_eq_none_iff]
  refine ⟨M', fun _ _ => rfl, ?_, ?_⟩
  · simp only [Machine.isHalting_iff_exists_haltsAt, stops]
  · unfold Machine.haltingNumber
    congr 1
    ext x
    constructor <;> rintro ⟨k, hk, rfl⟩
    · exact ⟨k, (stops k).mp hk, rfl⟩
    · exact ⟨k, (stops k).mpr hk, rfl⟩

private lemma not_halting_of_self_loop (M : Machine (Fin 2) (Fin 5)) (a : Fin 2) (d : Dir)
    (h0 : M 0 0 = some (some 0, Stmt.write a d)) : ¬ M.IsHalting := by
  rw [Machine.not_isHalting_iff_forall_isSome_multiStep]
  cases d with
  | right =>
    have hinv : ∀ n : ℕ, M.multiStep (Machine.init []) n =
        some ⟨some 0, ⟨0, ListBlank.append (List.replicate n a) default, default⟩⟩ := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [Machine.multiStep_succ, ih]
        simp only [Option.bind_some, Machine.step, h0, Option.map_some, Tape.write, Tape.move,
          head_default_fin2, tail_default_fin2]
        congr 3
    intro n
    rw [hinv (n + 1)]
    rfl
  | left =>
    have hinv : ∀ n : ℕ, M.multiStep (Machine.init []) n =
        some ⟨some 0, ⟨0, default, ListBlank.append (List.replicate n a) default⟩⟩ := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [Machine.multiStep_succ, ih]
        simp only [Option.bind_some, Machine.step, h0, Option.map_some, Tape.write, Tape.move,
          head_default_fin2, tail_default_fin2]
        congr 3
    intro n
    rw [hinv (n + 1)]
    rfl

def H1 : Prop :=
  ∀ (M : Machine (Fin 2) (Fin 5)),
    M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
    M.IsHalting → ∀ k : ℕ, M.haltingNumber = k → k ≤ 47176870

def H2 : Prop :=
  ∀ (M : Machine (Fin 2) (Fin 5)),
    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
    M.IsHalting → ∀ k : ℕ, M.haltingNumber = k → k ≤ 47176870

theorem main : H1 → H2 → type_of% @BusyBeaver.BB_5 := by
  intro hB0 hB1
  let S := {n : ℕ | ∃ C : Candidate 5, C.M.haltingNumber = n}
  have hm : 47176870 ∈ S := exists_champion_47176870
  have hub : ∀ k ∈ S, k ≤ 47176870 := by
    rintro k ⟨C, hC⟩
    obtain ⟨M, hM_halt, hM_num⟩ := normalize_candidate C
    have hk : M.haltingNumber = k := hM_num.trans hC
    have hhead : (Tape.mk₁ ([] : List (Fin 2))).head = (0 : Fin 2) := rfl
    have hdef : (default : Fin 5) = (0 : Fin 5) := rfl
    cases h0 : M 0 0 with
    | none =>
      have h0_num : M.haltingNumber = (0 : ℕ) :=
        Machine.haltingNumber_def M 0 ⟨Machine.init [], rfl⟩
          (by simp only [Machine.multiStep_succ, Machine.multiStep_zero, Option.bind_some,
            Machine.step, Machine.init, hdef, hhead, h0, Option.map_none])
      rw [h0_num] at hk
      have hk0 : k = 0 := by exact_mod_cast hk.symm
      omega
    | some z =>
      obtain ⟨q', ⟨a, d⟩⟩ := z
      cases q' with
      | none =>
        have h1_step : M.multiStep (Machine.init []) 1 = some ⟨none, ((Tape.mk₁ ([] : List (Fin 2))).write a).move d⟩ := by
          simp only [Machine.multiStep_one, Machine.step, Machine.init, hdef, hhead, h0, Option.map_some]
        have h1_stop : M.multiStep (Machine.init []) 2 = none := by
          rw [Machine.multiStep_succ, h1_step]
          rfl
        have h1_num : M.haltingNumber = (1 : ℕ) :=
          Machine.haltingNumber_def M 1 ⟨_, h1_step⟩ h1_stop
        rw [h1_num] at hk
        have hk1 : k = 1 := by exact_mod_cast hk.symm
        omega
      | some q =>
        by_cases hq0 : q = 0
        · subst hq0
          exact False.elim (not_halting_of_self_loop M a d h0 hM_halt)
        · let e : Equiv.Perm (Fin 5) := Equiv.swap (1 : Fin 5) q
          have he0 : e 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hq0)
          obtain ⟨M1, hM1_eq, hM1_halt, hM1_num⟩ := perm_states M e he0
          have hM1_00 : M1 0 0 = some (some 1, Stmt.write a d) := by
            rw [hM1_eq]
            have hes0 : e.symm 0 = 0 := by rw [Equiv.symm_apply_eq]; exact he0.symm
            rw [hes0, h0]
            simp [e]
          have hM1_h : M1.IsHalting := hM1_halt.mpr hM_halt
          have hM1_k : M1.haltingNumber = k := hM1_num.trans hk
          cases d with
          | right =>
            fin_cases a
            · exact hB0 M1 hM1_00 hM1_h k hM1_k
            · exact hB1 M1 hM1_00 hM1_h k hM1_k
          | left =>
            obtain ⟨M2, hM2_eq, hM2_halt, hM2_num⟩ := mirror_machine M1
            have hM2_00 : M2 0 0 = some (some 1, Stmt.write a Dir.right) := by
              rw [hM2_eq, hM1_00]
              rfl
            have hM2_h : M2.IsHalting := hM2_halt.mpr hM1_h
            have hM2_k : M2.haltingNumber = k := hM2_num.trans hM1_k
            fin_cases a
            · exact hB0 M2 hM2_00 hM2_h k hM2_k
            · exact hB1 M2 hM2_00 hM2_h k hM2_k
  change sSup S = 47176870
  exact le_antisymm (csSup_le ⟨47176870, hm⟩ hub) (le_csSup ⟨47176870, hub⟩ hm)

end OMA.R_BusyBeaver_BB_5_R1
