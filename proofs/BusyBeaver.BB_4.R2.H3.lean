import OMAReductions.R_BusyBeaver_BB_4_R2
/-! Both machines repeatedly enter state A with a tape described by two counts j and k.
The left side contains j ones. From the head to the right, the second machine sees
2*k ones, a zero, and j ones. The first machine sees an additional leading zero.
When k is positive, a sweep transfers one unit from k to j. When k reaches zero,
the machines begin a new sweep. Each transition between these configurations takes
at least one machine step. -/
namespace OMA.BB4Sweeps
open Turing Turing.BusyBeaver
abbrev TM := Machine (Fin 2) (Fin 4)
abbrev Conf := Cfg (Fin 2) (Fin 4)
abbrev Side := ListBlank (Fin 2)
def special (second : Bool) : Machine (Fin 2) (Fin 4) := fun q a =>
    let entries : List ℕ := if second then [6,4,11,6,16,13,2,15] else [6,3,3,8,15,10,16,1]
    let v := entries[2*q.val+a.val]?.getD 16
    if v = 16 then none else some (some ⟨v / 4 % 4, Nat.mod_lt _ (by decide)⟩, Stmt.write ⟨v / 2 % 2, Nat.mod_lt _ (by decide)⟩
      (if v % 2 = 0 then Dir.right else Dir.left))

def run (M : TM) (a b : Conf) := ∃ n, M.multiStep a n = some b
lemma joinSteps (M : TM) {a b c : Conf} {n k : ℕ} (h : M.multiStep a n = some b)
    (g : M.multiStep b k = some c) : M.multiStep a (n+k) = some c := by
  unfold Machine.multiStep at *
  rw [Nat.add_comm, Function.iterate_add_apply, h, g]
lemma cat {M : TM} {a b c : Conf} (h : run M a b) (g : run M b c) : run M a c := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨k, hk⟩ := g
  exact ⟨_,joinSteps M hn hk⟩
lemma stay (M : TM) (a : Conf) : run M a a := ⟨0,rfl⟩
def config (q : Fin 4) (l : Side) (a : Fin 2) (r : Side) : Conf := ⟨q,⟨a,l,r⟩⟩
@[simp] def rc (q : Fin 4) (l r : Side) := config q l r.head r.tail
@[simp] def lc (q : Fin 4) (l r : Side) := config q l.tail l.head r
@[simp] def w : ℕ → Side → Side
  | 0, t => t
  | n+1, t => (w n t).cons 1
@[simp] lemma w_cons (n : ℕ) (l : Side) : w n (l.cons 1) = (w n l).cons 1 := by
  induction n <;> simp [w, *]
@[simp] lemma w_add (m n : ℕ) (t : Side) : w m (w n t) = w (n+m) t := by
  induction m <;> simp [w, *]
def z : Side := ListBlank.mk []
@[simp] lemma hz : z.head = 0 := rfl
@[simp] lemma tz : z.tail = z := rfl
@[simp] lemma cz : z.cons 0 = z := by
  simpa only [hz,tz] using ListBlank.cons_head_tail z
lemma right {M : TM} {q q' : Fin 4} {a b : Fin 2} (l r : Side)
    (h : M q a = some (some q',Stmt.write b Dir.right)) :
    M.step (config q l a r) = some (rc q' (l.cons b) r) := by
  simp [Machine.step,config,h,rc,Tape.move]
lemma left {M : TM} {q q' : Fin 4} {a b : Fin 2} (l r : Side)
    (h : M q a = some (some q',Stmt.write b Dir.left)) :
    M.step (config q l a r) = some (lc q' l (r.cons b)) := by
  simp [Machine.step,config,h,lc,Tape.move]
lemma rscan {M : TM} {q : Fin 4} (h : M q 1 = some (some q,Stmt.write 1 Dir.right))
    (n : ℕ) (l r : Side) : run M (rc q l (w n r)) (rc q (w n l) r) := by
  induction n generalizing l with
  | zero => exact stay _ _
  | succ n ih =>
    apply cat _ (show run M (rc q (l.cons 1) (w n r)) _ from by
      simpa only [w_cons,w] using ih (l.cons 1))
    refine ⟨1,?_⟩
    simpa only [Machine.multiStep_one,rc,w,ListBlank.head_cons,ListBlank.tail_cons] using right l (w n r) h
lemma lscan {M : TM} {q : Fin 4} (h : M q 1 = some (some q,Stmt.write 1 Dir.left))
    (n : ℕ) (l r : Side) : run M (lc q (w n l) r) (lc q l (w n r)) := by
  induction n generalizing r with
  | zero => exact stay _ _
  | succ n ih =>
    apply cat _ (show run M (lc q (w n l) (r.cons 1)) _ from by
      simpa only [w_cons,w] using ih (r.cons 1))
    refine ⟨1,?_⟩
    simpa only [Machine.multiStep_one,lc,w,ListBlank.head_cons,ListBlank.tail_cons] using left (w n l) r h
@[simp] def first (j k : ℕ) := config 0 (w j z) 0 (w (2*k) ((w j z).cons 0))
@[simp] def second (j k : ℕ) := rc 0 (w j z) (w (2*k) ((w j z).cons 0))
def advances (M : TM) (a b : Conf) := ∃ n, 0 < n ∧ M.multiStep a n = some b
lemma starts {M : TM} {a b c : Conf} (h : M.step a = some b) (g : run M b c) : advances M a c := by
  obtain ⟨n,hn⟩ := g
  exact ⟨1+n,by omega,joinSteps M (n := 1) h hn⟩
lemma endless (M : TM) (f : ℕ → ℕ → Conf) (init : f 0 0 = Machine.init [])
    (adv : ∀ j k, ∃ x y, advances M (f j k) (f x y)) : ¬ M.IsHalting := by
  have reach (n : ℕ) : ∃ j k m, n ≤ m ∧ M.multiStep (Machine.init []) m = some (f j k) := by
    induction n with
    | zero => exact ⟨0,0,0,by omega,by simp [init]⟩
    | succ n ih =>
      obtain ⟨j,k,m,hm,h⟩ := ih
      obtain ⟨x,y,d,hd,g⟩ := adv j k
      exact ⟨x,y,m+d,by omega,joinSteps M h g⟩
  rintro h
  obtain ⟨n,hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp h
  obtain ⟨j,k,m,hm,g⟩ := reach (n+1)
  have := Machine.multiStep_eq_none_mono hn hm
  simp_all

lemma first_restart (j : ℕ) : advances (special false) (first j 0) (first (0) (j+1)) := by
  have h0 : (special false).step (first j 0) = some (rc 1 (ListBlank.cons 1 (w j z)) (ListBlank.cons 0 (w j z))) := by
    simpa using right (w j z) (ListBlank.cons 0 (w j z)) (show (special false) 0 0 = some (some 1, Stmt.write 1 Dir.right) from rfl)
  have h1 : run (special false) (rc 1 (ListBlank.cons 1 (w j z)) (ListBlank.cons 0 (w j z))) (lc 0 (ListBlank.cons 1 (w j z)) (ListBlank.cons 1 (w j z))) := by
    refine ⟨1,?_⟩
    rw [Machine.multiStep_one]
    simpa using left (ListBlank.cons 1 (w j z)) (w j z) (show (special false) 1 0 = some (some 0, Stmt.write 1 Dir.left) from rfl)
  have h2 : run (special false) (lc 0 (ListBlank.cons 1 (w j z)) (ListBlank.cons 1 (w j z))) (lc 0 (w j z) (ListBlank.cons 1 (ListBlank.cons 1 (w j z)))) := by
    simpa using lscan (show (special false) 0 1 = some (some 0, Stmt.write 1 Dir.left) from rfl) 1 (w j z) (ListBlank.cons 1 (w j z))
  have h3 : run (special false) (lc 0 (w j z) (ListBlank.cons 1 (ListBlank.cons 1 (w j z)))) (first (0) (j+1)) := by
    simpa only [first, second, rc, lc, Nat.mul_succ, Nat.add_succ, w, w_cons, w_add, hz, tz, cz, ListBlank.head_cons, ListBlank.tail_cons, two_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using lscan (show (special false) 0 1 = some (some 0, Stmt.write 1 Dir.left) from rfl) j z (ListBlank.cons 1 (ListBlank.cons 1 (w j z)))
  exact starts h0 (cat h1 (cat h2 h3))

lemma first_sweep (j k : ℕ) : advances (special false) (first j (k+1)) (first (j+1) (k)) := by
  have h0 : (special false).step (first j (k+1)) = some (rc 1 (ListBlank.cons 1 (w j z)) (ListBlank.cons 1 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))))) := by
    simpa [Nat.mul_succ] using right (w j z) (ListBlank.cons 1 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z))))) (show (special false) 0 0 = some (some 1, Stmt.write 1 Dir.right) from rfl)
  have h1 : run (special false) (rc 1 (ListBlank.cons 1 (w j z)) (ListBlank.cons 1 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))))) (rc 2 (ListBlank.cons 0 (ListBlank.cons 1 (w j z))) (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z))))) := by
    refine ⟨1,?_⟩
    rw [Machine.multiStep_one]
    simpa using right (ListBlank.cons 1 (w j z)) (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))) (show (special false) 1 1 = some (some 2, Stmt.write 0 Dir.right) from rfl)
  have h2 : run (special false) (rc 2 (ListBlank.cons 0 (ListBlank.cons 1 (w j z))) (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z))))) (rc 2 (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (w (2*k) (ListBlank.cons 0 (w j z)))) := by
    simpa using rscan (show (special false) 2 1 = some (some 2, Stmt.write 1 Dir.right) from rfl) 1 (ListBlank.cons 0 (ListBlank.cons 1 (w j z))) (w (2*k) (ListBlank.cons 0 (w j z)))
  have h3 : run (special false) (rc 2 (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (w (2*k) (ListBlank.cons 0 (w j z)))) (rc 2 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) (ListBlank.cons 0 (w j z))) := by
    simpa using rscan (show (special false) 2 1 = some (some 2, Stmt.write 1 Dir.right) from rfl) (2*k) (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (ListBlank.cons 0 (w j z))
  have h4 : run (special false) (rc 2 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) (ListBlank.cons 0 (w j z))) (lc 3 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) (ListBlank.cons 1 (w j z))) := by
    refine ⟨1,?_⟩
    rw [Machine.multiStep_one]
    simpa using left (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) (w j z) (show (special false) 2 0 = some (some 3, Stmt.write 1 Dir.left) from rfl)
  have h5 : run (special false) (lc 3 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) (ListBlank.cons 1 (w j z))) (lc 0 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) := by
    refine ⟨1,?_⟩
    rw [Machine.multiStep_one]
    simpa using left (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (ListBlank.cons 1 (w j z)) (show (special false) 3 1 = some (some 0, Stmt.write 0 Dir.left) from rfl)
  have h6 : run (special false) (lc 0 (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (first (j+1) (k)) := by
    simpa using lscan (show (special false) 0 1 = some (some 0, Stmt.write 1 Dir.left) from rfl) (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))
  exact starts h0 (cat h1 (cat h2 (cat h3 (cat h4 (cat h5 h6)))))

lemma second_restart (j : ℕ) : advances (special true) (second j 0) (second (1) (j)) := by
  have h0 : (special true).step (second j 0) = some (rc 1 (ListBlank.cons 1 (w j z)) (w j z)) := by
    simpa using right (w j z) (w j z) (show (special true) 0 0 = some (some 1, Stmt.write 1 Dir.right) from rfl)
  have h1 : run (special true) (rc 1 (ListBlank.cons 1 (w j z)) (w j z)) (rc 1 (ListBlank.cons 1 (w j (w j z))) z) := by
    simpa using rscan (show (special true) 1 1 = some (some 1, Stmt.write 1 Dir.right) from rfl) j (ListBlank.cons 1 (w j z)) z
  have h2 : run (special true) (rc 1 (ListBlank.cons 1 (w j (w j z))) z) (lc 2 (ListBlank.cons 1 (w j (w j z))) (ListBlank.cons 1 z)) := by
    refine ⟨1,?_⟩
    rw [Machine.multiStep_one]
    simpa using left (ListBlank.cons 1 (w j (w j z))) z (show (special true) 1 0 = some (some 2, Stmt.write 1 Dir.left) from rfl)
  have h3 : run (special true) (lc 2 (ListBlank.cons 1 (w j (w j z))) (ListBlank.cons 1 z)) (lc 3 (w j (w j z)) (ListBlank.cons 0 (ListBlank.cons 1 z))) := by
    refine ⟨1,?_⟩
    rw [Machine.multiStep_one]
    simpa using left (w j (w j z)) (ListBlank.cons 1 z) (show (special true) 2 1 = some (some 3, Stmt.write 0 Dir.left) from rfl)
  have h4 : run (special true) (lc 3 (w j (w j z)) (ListBlank.cons 0 (ListBlank.cons 1 z))) (lc 3 (w j z) (w j (ListBlank.cons 0 (ListBlank.cons 1 z)))) := by
    simpa using lscan (show (special true) 3 1 = some (some 3, Stmt.write 1 Dir.left) from rfl) j (w j z) (ListBlank.cons 0 (ListBlank.cons 1 z))
  have h5 : run (special true) (lc 3 (w j z) (w j (ListBlank.cons 0 (ListBlank.cons 1 z)))) (lc 3 z (w j (w j (ListBlank.cons 0 (ListBlank.cons 1 z))))) := by
    simpa using lscan (show (special true) 3 1 = some (some 3, Stmt.write 1 Dir.left) from rfl) j z (w j (ListBlank.cons 0 (ListBlank.cons 1 z)))
  have h6 : run (special true) (lc 3 z (w j (w j (ListBlank.cons 0 (ListBlank.cons 1 z))))) (second (1) (j)) := by
    refine ⟨1,?_⟩
    rw [Machine.multiStep_one]
    simpa [Nat.mul_succ, Nat.add_succ, two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using right z (w j (w j (ListBlank.cons 0 (ListBlank.cons 1 z)))) (show (special true) 3 0 = some (some 0, Stmt.write 1 Dir.right) from rfl)
  exact starts h0 (cat h1 (cat h2 (cat h3 (cat h4 (cat h5 h6)))))

lemma second_sweep (j k : ℕ) : advances (special true) (second j (k+1)) (second (j+1) (k)) := by
  have h0 : (special true).step (second j (k+1)) = some (rc 1 (ListBlank.cons 0 (w j z)) (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z))))) := by
    simpa [Nat.mul_succ] using right (w j z) (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))) (show (special true) 0 1 = some (some 1, Stmt.write 0 Dir.right) from rfl)
  have h1 : run (special true) (rc 1 (ListBlank.cons 0 (w j z)) (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z))))) (rc 1 (ListBlank.cons 1 (ListBlank.cons 0 (w j z))) (w (2*k) (ListBlank.cons 0 (w j z)))) := by
    simpa using rscan (show (special true) 1 1 = some (some 1, Stmt.write 1 Dir.right) from rfl) 1 (ListBlank.cons 0 (w j z)) (w (2*k) (ListBlank.cons 0 (w j z)))
  have h2 : run (special true) (rc 1 (ListBlank.cons 1 (ListBlank.cons 0 (w j z))) (w (2*k) (ListBlank.cons 0 (w j z)))) (rc 1 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))) (ListBlank.cons 0 (w j z))) := by
    simpa using rscan (show (special true) 1 1 = some (some 1, Stmt.write 1 Dir.right) from rfl) (2*k) (ListBlank.cons 1 (ListBlank.cons 0 (w j z))) (ListBlank.cons 0 (w j z))
  have h3 : run (special true) (rc 1 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))) (ListBlank.cons 0 (w j z))) (lc 2 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))) (ListBlank.cons 1 (w j z))) := by
    refine ⟨1,?_⟩
    rw [Machine.multiStep_one]
    simpa using left (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))) (w j z) (show (special true) 1 0 = some (some 2, Stmt.write 1 Dir.left) from rfl)
  have h4 : run (special true) (lc 2 (ListBlank.cons 1 (w (2*k) (ListBlank.cons 0 (w j z)))) (ListBlank.cons 1 (w j z))) (lc 3 (w (2*k) (ListBlank.cons 0 (w j z))) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) := by
    refine ⟨1,?_⟩
    rw [Machine.multiStep_one]
    simpa using left (w (2*k) (ListBlank.cons 0 (w j z))) (ListBlank.cons 1 (w j z)) (show (special true) 2 1 = some (some 3, Stmt.write 0 Dir.left) from rfl)
  have h5 : run (special true) (lc 3 (w (2*k) (ListBlank.cons 0 (w j z))) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (lc 3 (ListBlank.cons 0 (w j z)) (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) := by
    simpa using lscan (show (special true) 3 1 = some (some 3, Stmt.write 1 Dir.left) from rfl) (2*k) (ListBlank.cons 0 (w j z)) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))
  have h6 : run (special true) (lc 3 (ListBlank.cons 0 (w j z)) (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z))))) (second (j+1) (k)) := by
    refine ⟨1,?_⟩
    rw [Machine.multiStep_one]
    simpa using right (w j z) (w (2*k) (ListBlank.cons 0 (ListBlank.cons 1 (w j z)))) (show (special true) 3 0 = some (some 0, Stmt.write 1 Dir.right) from rfl)
  exact starts h0 (cat h1 (cat h2 (cat h3 (cat h4 (cat h5 h6)))))

end OMA.BB4Sweeps
open OMA.BB4Sweeps in
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2.H3 := by
  change ∀ b, ¬ (special b).IsHalting
  intro b
  cases b
  · apply endless _ first
    · simp only [first, Nat.mul_zero, w, cz]
      rfl
    · intro j k
      cases k with
      | zero => exact ⟨_,_,first_restart j⟩
      | succ k => exact ⟨_,_,first_sweep j k⟩
  · apply endless _ second
    · rfl
    · intro j k
      cases k with
      | zero => exact ⟨_,_,second_restart j⟩
      | succ k => exact ⟨_,_,second_sweep j k⟩
