import FormalConjectures.OEIS.«260194»

/-! A finite modular certificate for the jumps of A260194. -/

namespace A260194Proof

structure Step where
  offset : ℕ
  divisor : ℕ
  jump : ℕ

structure State where
  x : ℕ
  d : ℕ
  e : ℕ

def jump (s : State) : ℕ := Nat.gcd s.x (s.d + s.e)

def next (s : State) : State := ⟨s.x + jump s, jump s, s.d⟩

def run : ℕ → State → State
  | 0, s => s
  | n+1, s => run n (next s)

theorem run_add (i j : ℕ) (s : State) : run (i+j) s = run j (run i s) := by
  induction i generalizing s with
  | zero => simp [run]
  | succ i ih => rw [Nat.succ_add, run, run, ih]

def Good (s : State) : Prop :=
  ∃ k : ℕ, (run k s).d = 1 ∧ (run k s).e = 1 ∧
    ∀ j ≤ k, (run j s).d ≤ 89

theorem Good.prepend {s : State} (h : Good (next s)) (hd : s.d ≤ 89) : Good s := by
  obtain ⟨k, hp, hq, hb⟩ := h
  refine ⟨k+1, hp, hq, ?_⟩
  intro j hj
  cases j with
  | zero => exact hd
  | succ j => exact hb j (by omega)

def Holds (x : ℕ) (hs : List Step) : Prop :=
  ∀ s ∈ hs, Nat.gcd (x + s.offset) s.divisor = s.jump

def compatible (m r : ℕ) (s : Step) : Bool :=
  Nat.gcd (r + s.offset) (Nat.gcd m s.divisor) == Nat.gcd s.jump m

theorem gcd_mod_second (x d : ℕ) : Nat.gcd x d = Nat.gcd (x % d) d := by
  rw [Nat.gcd_comm x d]
  exact Nat.gcd_rec d x

theorem compatible_mod (x m : ℕ) (s : Step)
    (hs : Nat.gcd (x + s.offset) s.divisor = s.jump) :
    compatible m (x % m) s = true := by
  simp only [compatible, beq_iff_eq]
  let g := Nat.gcd m s.divisor
  have hdiv : g ∣ m := Nat.gcd_dvd_left m s.divisor
  have hmod : (x % m + s.offset) % g = (x + s.offset) % g := by
    rw [Nat.add_mod (x % m), Nat.mod_mod_of_dvd x hdiv, ← Nat.add_mod]
  change Nat.gcd (x % m + s.offset) g = Nat.gcd s.jump m
  calc
    _ = Nat.gcd ((x % m + s.offset) % g) g := gcd_mod_second _ _
    _ = Nat.gcd ((x + s.offset) % g) g := by rw [hmod]
    _ = Nat.gcd (x + s.offset) g := (gcd_mod_second _ _).symm
    _ = Nat.gcd s.jump m := by
      dsimp [g]
      rw [Nat.gcd_comm m s.divisor, ← Nat.gcd_assoc, hs]

def impossible (m : ℕ) (hs : List Step) : Bool :=
  (0 < m) && (List.range m).all (fun r => !(hs.all (compatible m r)))

theorem impossible_false {m x : ℕ} {hs : List Step}
    (hb : impossible m hs = true) (h : Holds x hs) : False := by
  have hm : 0 < m := by
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp hb).1
  have hbad := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hb).2)
    (x % m) (List.mem_range.mpr (Nat.mod_lt _ hm))
  have hok : hs.all (compatible m (x % m)) = true :=
    List.all_eq_true.mpr (fun s hmem => compatible_mod x m s (h s hmem))
  simp [hok] at hbad

def candidates (s : ℕ) : List ℕ :=
  (List.range' 1 s).filter (fun f => s % f == 0)

def ms : List ℕ := [8,9,5,7,3,27,4,32,11,13,16,25,64,17,19,23,49,31,2,29]

def chk : ℕ → ℕ → ℕ → ℕ → List Step → Bool
  | 0, _, d, e, hs => d == 1 && e == 1 || ms.any (impossible · hs)
  | n+1, o, d, e, hs => d == 1 && e == 1 || ms.any (impossible · hs) ||
    d ≤ 89 && (candidates (d+e)).all fun f => chk n (o+f) f d (⟨o,d+e,f⟩ :: hs)

theorem chk_correct (n o d e x : ℕ) (hs : List Step)
    (hx : 0 < x) (hd : 0 < d) (he : 0 < e) (h : Holds x hs)
    (hc : chk n o d e hs = true) : Good ⟨x + o, d, e⟩ := by
  induction n generalizing o d e hs with
  | zero =>
    simp only [chk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hc
    rcases hc with ⟨rfl, rfl⟩ | ⟨m, -, hm⟩
    · exact ⟨0, rfl, rfl, fun j hj => by cases Nat.le_zero.mp hj; exact (by decide : 1 ≤ 89)⟩
    · exact (impossible_false hm h).elim
  | succ n ih =>
    simp only [chk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hc
    rcases hc with (⟨rfl, rfl⟩ | ⟨m, -, hm⟩) | ⟨hbound, hcs⟩
    · exact ⟨0, rfl, rfl, fun j hj => by cases Nat.le_zero.mp hj; exact (by decide : 1 ≤ 89)⟩
    · exact (impossible_false hm h).elim
    · let f := Nat.gcd (x + o) (d + e)
      have hf : 0 < f := Nat.gcd_pos_of_pos_left _ (by omega)
      have hfLe : f ≤ d + e := Nat.gcd_le_right _ (by omega)
      have hmem : f ∈ candidates (d + e) := by
        refine List.mem_filter.mpr ⟨List.mem_range'.mpr ⟨f-1, by omega, by omega⟩, ?_⟩
        exact beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right _ _))
      have hchild := List.all_eq_true.mp hcs f hmem
      have hnext : Holds x (⟨o, d+e, f⟩ :: hs) := by
        intro s hmem'
        rcases List.mem_cons.mp hmem' with hhead | htail
        · subst s
          rfl
        · exact h s htail
      apply Good.prepend _ (of_decide_eq_true hbound)
      simpa only [next, jump, Nat.add_assoc] using
        ih (o+f) f d (⟨o,d+e,f⟩ :: hs) hf hd hnext hchild

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 50000 in
theorem tree_checked : chk 35 2 2 1 [⟨0,2,2⟩] = true := by
  decide +kernel

theorem after_reset (x : ℕ) (hx : 0 < x) : Good (next ⟨x,1,1⟩) := by
  rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega) with h | h
  · have h2 : Nat.gcd x 2 = 2 := by rw [gcd_mod_second, h]; decide
    have hs : Holds x [⟨0,2,2⟩] := by
      intro s hmem
      have h' : s = ⟨0,2,2⟩ := by simpa using hmem
      subst s
      simpa using h2
    have hn : next ⟨x,1,1⟩ = ⟨x+2,2,1⟩ := by simp [next, jump, h2]
    rw [hn]
    exact chk_correct 35 2 2 1 x _ hx (by decide) (by decide) hs tree_checked
  · have h1 : Nat.gcd x 2 = 1 := by rw [gcd_mod_second, h]; decide
    have hn : next ⟨x,1,1⟩ = ⟨x+1,1,1⟩ := by simp [next, jump, h1]
    rw [hn]
    refine ⟨0,rfl,rfl,?_⟩
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    change 1 ≤ 89
    decide

theorem run_pos (j : ℕ) (s : State) (hs : 0 < s.x) : 0 < (run j s).x := by
  induction j generalizing s with
  | zero => exact hs
  | succ j ih => exact ih (next s) (by dsimp [next]; omega)

theorem all_good (n x : ℕ) (hx : 0 < x) : (run n ⟨x,1,1⟩).d ≤ 89 := by
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    cases n with
    | zero =>
      change 1 ≤ 89
      decide
    | succ n =>
      obtain ⟨k, hd, he, hb⟩ := after_reset x hx
      change (run n (next ⟨x,1,1⟩)).d ≤ 89
      by_cases hk : n ≤ k
      · exact hb n hk
      · have hp : 0 < (run k (next ⟨x,1,1⟩)).x :=
          run_pos k _ (by dsimp [next]; omega)
        have hr : run k (next ⟨x,1,1⟩) = ⟨(run k (next ⟨x,1,1⟩)).x,1,1⟩ := by
          cases h : run k (next ⟨x,1,1⟩) with
          | mk y d e =>
            rw [h] at hd he
            change d = 1 at hd
            change e = 1 at he
            subst d
            subst e
            rfl
        rw [show n = k + (n-k) by omega, run_add, hr]
        exact ih (n-k) (by omega) _ hp

open OeisA260194

theorem sequence_matches (n : ℕ) :
    (run n ⟨3,1,1⟩).x = a (n+4) ∧
    a (n+4) = a (n+3) + (run n ⟨3,1,1⟩).d ∧
    a (n+3) = a (n+2) + (run n ⟨3,1,1⟩).e := by
  induction n with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨hx, hd, he⟩ := ih
    change (run (n+1) ⟨3,1,1⟩).x = a (n+5) ∧
      a (n+5) = a (n+4) + (run (n+1) ⟨3,1,1⟩).d ∧
      a (n+4) = a (n+3) + (run (n+1) ⟨3,1,1⟩).e
    rw [run_add]
    let s := run n ⟨3,1,1⟩
    change (next s).x = a (n+5) ∧
      a (n+5) = a (n+4) + (next s).d ∧ a (n+4) = a (n+3) + (next s).e
    have hsum : a (n+4) = a (n+2) + (s.d + s.e) := by dsimp [s]; omega
    have hj : jump s = Nat.gcd (a (n+4)) (a (n+2)) := by
      let p := a (n+2)
      let q := s.d + s.e
      have hu : s.x = p + q := hx.trans hsum
      have hv : Nat.gcd (p+q) p = Nat.gcd q p := by
        rw [Nat.add_comm p q]
        exact Nat.gcd_add_self_left p q
      change Nat.gcd s.x q = Nat.gcd (a (n+4)) p
      calc
        _ = Nat.gcd (p+q) q := congrArg (fun z => Nat.gcd z q) hu
        _ = Nat.gcd p q := Nat.gcd_add_self_left q p
        _ = Nat.gcd q p := Nat.gcd_comm p q
        _ = Nat.gcd (p+q) p := hv.symm
        _ = Nat.gcd (a (n+4)) p := congrArg (fun z => Nat.gcd z p) hsum.symm
    have ha : a (n+5) = a (n+4) + Nat.gcd (a (n+4)) (a (n+2)) := rfl
    simp only [next]
    change s.x + jump s = a (n+5) ∧ a (n+5) = a (n+4) + jump s ∧
      a (n+4) = a (n+3) + s.d
    exact ⟨by rw [show s.x = a (n+4) from hx, hj, ← ha],
      by rw [hj, ← ha], hd⟩

end A260194Proof

theorem OMA.disproof : ¬ (type_of% @OeisA260194.conjecture) := by
  intro h
  obtain ⟨n, hn⟩ := h 90 (by decide)
  by_cases hsmall : n < 3
  · interval_cases n <;> norm_num [OeisA260194.a] at hn
  obtain ⟨k,rfl⟩ : ∃ k, n = k+3 := ⟨n-3, by omega⟩
  change OeisA260194.a (k+4) = OeisA260194.a (k+3) + 90 at hn
  have hmatch := (A260194Proof.sequence_matches k).2.1
  have hmax := A260194Proof.all_good k 3 (by decide)
  omega
