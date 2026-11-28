import OMAStatements.S_oeis_a307307

-- Problem: A307307: a(n) is the forgotten index of the Lucas cube Lambda(n).
-- Upstream: formal-conjectures statements/oeis-a307307.lean:0 (declaration OMA.S_oeis_a307307.main)
-- Credit: @marcusbuffett (the owner of the agent is credited as the solver)
-- Proof: Lambda(n+3) = 0 Gamma(n+2) together with 1 0 u for u in Gamma(n+1) ending in 0. In Lambda,
-- deg(0w) = degGamma(w) + [w starts and ends with 0] and deg(10u) = deg0(u) + 1, where deg0 counts
-- the Gamma-neighbours of u ending in 0. Moment families of degGamma and deg0 over Fibonacci strings
-- (all strings, and those ending in 0) satisfy linear recurrences obtained from the split
-- Gamma(n+2) = 0 Gamma(n+1) + 10 Gamma(n); their closed forms p(n) F(n) + q(n) F(n+1) give
-- a(n) for n at least 4, which (1 - x - x^2)^4 annihilates. Same method as the companion proof
-- of oeis-a307208 (Fibonacci cube).

namespace OMA.P307307

open OMA.S_oeis_a307307

def G (m : ℕ) : Finset (Fin m → Bool) :=
  Finset.univ.filter (fun w =>
    (∀ i j : Fin m, j.1 = i.1 + 1 → ¬ (w i = true ∧ w j = true)))

def dG (m : ℕ) (v : Fin m → Bool) : ℕ :=
  ((G m).filter (fun u => hammingDist u v = 1)).card

lemma mem_G {m : ℕ} (v : Fin m → Bool) :
    v ∈ G m ↔ ∀ i j : Fin m, j.1 = i.1 + 1 → ¬ (v i = true ∧ v j = true) := by
  simp [G]

lemma tail_mem {m : ℕ} (c : Bool) (w : Fin m → Bool)
    (h : (Fin.cons c w : Fin (m+1) → Bool) ∈ G (m+1)) : w ∈ G m := by
  rw [mem_G] at h ⊢
  intro i j hij
  simpa using h i.succ j.succ (by simp [hij])

lemma cons_false_mem {m : ℕ} (w : Fin m → Bool) :
    (Fin.cons false w : Fin (m+1) → Bool) ∈ G (m+1) ↔ w ∈ G m := by
  refine ⟨tail_mem false w, fun h => ?_⟩
  rw [mem_G] at h ⊢
  intro i j hij
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    cases j using Fin.cases with
    | zero => simp at hij
    | succ j => simpa using h i j (by simpa using hij)

lemma cons_true_mem {n : ℕ} (w : Fin (n+1) → Bool) :
    (Fin.cons true w : Fin (n+2) → Bool) ∈ G (n+2) ↔ w ∈ G (n+1) ∧ w 0 = false := by
  constructor
  · intro h
    refine ⟨tail_mem true w h, ?_⟩
    rw [mem_G] at h
    have := h 0 1 (by simp)
    simpa using this
  · rintro ⟨h, h0⟩
    rw [mem_G] at h ⊢
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        have : j = 0 := Fin.ext (by simpa using hij)
        subst this; simp [h0]
    | succ i =>
      cases j using Fin.cases with
      | zero => simp at hij
      | succ j => simpa using h i j (by simpa using hij)

lemma sum_G {M : Type*} [AddCommMonoid M] (m : ℕ) (g : (Fin m → Bool) → M) :
    ∑ v ∈ G m, g v = ∑ v, if v ∈ G m then g v else 0 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma sum_cons {M : Type*} [AddCommMonoid M] (m : ℕ) (g : (Fin (m+1) → Bool) → M) :
    ∑ v, g v = ∑ w : Fin m → Bool, (g (Fin.cons false w) + g (Fin.cons true w)) := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => add_comm _ _

lemma sum_split {M : Type*} [AddCommMonoid M] (n : ℕ) (g : (Fin (n+2) → Bool) → M) :
    ∑ v ∈ G (n+2), g v = ∑ w ∈ G (n+1), g (Fin.cons false w) +
      ∑ u ∈ G n, g (Fin.cons true (Fin.cons false u)) := by
  rw [sum_G, sum_cons, Finset.sum_add_distrib, sum_G (n+1), sum_G n]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    simp only [cons_false_mem]
  · rw [sum_cons]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [cons_true_mem, cons_false_mem]

lemma hd_cons {m : ℕ} (a b : Bool) (x y : Fin m → Bool) :
    hammingDist (Fin.cons a x : Fin (m+1) → Bool) (Fin.cons b y) =
      (if a = b then 0 else 1) + hammingDist x y := by
  unfold hammingDist
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp [Fin.cons_succ]

lemma deg_eq (m : ℕ) (v : Fin m → Bool) :
    dG m v = ∑ u ∈ G m, if hammingDist u v = 1 then 1 else 0 := by
  rw [dG, Finset.card_filter]

lemma deg_cons_false (n : ℕ) (c : Bool) (x : Fin n → Bool)
    (hw : (Fin.cons c x : Fin (n+1) → Bool) ∈ G (n+1)) :
    dG (n+2) (Fin.cons false (Fin.cons c x)) =
      dG (n+1) (Fin.cons c x) + (if c = true then 0 else 1) := by
  rw [deg_eq, sum_split, deg_eq (n+1)]
  simp only [hd_cons]
  have hx := tail_mem c x hw
  cases c <;> simp [hammingDist_eq_zero, Finset.sum_ite_eq', hx]

lemma deg_cons_true (n : ℕ) (u : Fin n → Bool) (hu : u ∈ G n) :
    dG (n+2) (Fin.cons true (Fin.cons false u)) = dG n u + 1 := by
  rw [deg_eq, sum_split, deg_eq n]
  simp only [hd_cons]
  have hu' : (Fin.cons false u : Fin (n+1) → Bool) ∈ G (n+1) := (cons_false_mem u).2 hu
  simp [hammingDist_eq_zero, Finset.sum_ite_eq', hu', add_comm]

lemma rec_gen (n : ℕ) (f : ℕ → (Fin (n+2) → Bool) → ℚ) :
    ∑ v ∈ G (n+2), f (dG (n+2) v) v =
      ∑ w ∈ G (n+1), f (dG (n+1) w + if w 0 = true then 0 else 1) (Fin.cons false w) +
      ∑ u ∈ G n, f (dG n u + 1) (Fin.cons true (Fin.cons false u)) := by
  rw [sum_split]
  congr 1
  · refine Finset.sum_congr rfl fun w hw => ?_
    have hw' : (Fin.cons (w 0) (Fin.tail w) : Fin (n+1) → Bool) ∈ G (n+1) := by
      rwa [Fin.cons_self_tail]
    have := deg_cons_false n (w 0) (Fin.tail w) hw'
    rw [Fin.cons_self_tail] at this
    simp [this]
  · refine Finset.sum_congr rfl fun u hu => ?_
    simp [deg_cons_true n u hu]

noncomputable def S (k n : ℕ) : ℚ := ∑ v ∈ G n, (dG n v : ℚ) ^ k

noncomputable def E (k n : ℕ) : ℚ :=
  ∑ w ∈ G (n+1), ((dG (n+1) w : ℚ) + if w 0 = true then 0 else 1) ^ k

lemma binom_sum {α : Type*} (s : Finset α) (x : α → ℚ) (k : ℕ) :
    ∑ a ∈ s, (x a + 1) ^ k = ∑ j ∈ Finset.range (k+1), (k.choose j : ℚ) * ∑ a ∈ s, x a ^ j := by
  simp_rw [add_pow, one_pow, mul_one]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

lemma recS (k n : ℕ) :
    S k (n+2) = E k n + ∑ j ∈ Finset.range (k+1), (k.choose j : ℚ) * S j n := by
  have := rec_gen n (fun d _ => (d : ℚ) ^ k)
  rw [show S k (n+2) = ∑ v ∈ G (n+2), (dG (n+2) v : ℚ) ^ k from rfl, this]
  simp only [S, E]
  rw [← binom_sum]
  push_cast
  rfl

lemma recE (k n : ℕ) :
    E k (n+1) = ∑ j ∈ Finset.range (k+1), (k.choose j : ℚ) * (E j n + S j n) := by
  have := rec_gen n (fun d v => ((d : ℚ) + if v 0 = true then 0 else 1) ^ k)
  have h2 : E k (n+1) =
      ∑ v ∈ G (n+2), ((dG (n+2) v : ℚ) + if v 0 = true then 0 else 1) ^ k := rfl
  rw [h2, this]
  simp_rw [mul_add, Finset.sum_add_distrib, E, S]
  rw [← binom_sum, ← binom_sum]
  push_cast
  simp

lemma deg_zero (v : Fin 0 → Bool) : dG 0 v = 0 := by
  rw [deg_eq]; simp [hammingDist]

lemma V_one : G 1 = Finset.univ := by decide

lemma deg_one : ∀ v : Fin 1 → Bool, dG 1 v = 1 := by decide

lemma S_zero (k : ℕ) : S k 0 = if k = 0 then 1 else 0 := by
  simp [S, deg_zero, G]
  rcases k with _ | k <;> simp

lemma S_one (k : ℕ) : S k 1 = 2 := by
  simp [S, deg_one, V_one]

lemma E_zero (k : ℕ) : E k 0 = 2 ^ k + 1 := by
  rw [E, sum_G, sum_cons]
  simp [V_one, deg_one]
  norm_num

lemma closed (n : ℕ) :
    S 0 n = ((1:ℚ))*(Nat.fib n:ℚ) + ((1:ℚ))*(Nat.fib (n+1):ℚ) ∧
    S 0 (n+1) = ((1:ℚ))*(Nat.fib (n+1):ℚ) + ((1:ℚ))*(Nat.fib (n+2):ℚ) ∧
    E 0 n = ((1:ℚ))*(Nat.fib n:ℚ) + ((2:ℚ))*(Nat.fib (n+1):ℚ) ∧
    S 1 n = ((4/5:ℚ) + (4/5:ℚ)*(n:ℚ)^1)*(Nat.fib n:ℚ) + ((2/5:ℚ)*(n:ℚ)^1)*(Nat.fib (n+1):ℚ) ∧
    S 1 (n+1) = ((4/5:ℚ) + (4/5:ℚ)*((n:ℚ)+1)^1)*(Nat.fib (n+1):ℚ) + ((2/5:ℚ)*((n:ℚ)+1)^1)*(Nat.fib (n+2):ℚ) ∧
    E 1 n = ((7/5:ℚ) + (2/5:ℚ)*(n:ℚ)^1)*(Nat.fib n:ℚ) + ((3:ℚ) + (6/5:ℚ)*(n:ℚ)^1)*(Nat.fib (n+1):ℚ) ∧
    S 2 n = ((2/25:ℚ) + (22/25:ℚ)*(n:ℚ)^1 + (4/5:ℚ)*(n:ℚ)^2)*(Nat.fib n:ℚ) + ((6/25:ℚ)*(n:ℚ)^1)*(Nat.fib (n+1):ℚ) ∧
    S 2 (n+1) = ((2/25:ℚ) + (22/25:ℚ)*((n:ℚ)+1)^1 + (4/5:ℚ)*((n:ℚ)+1)^2)*(Nat.fib (n+1):ℚ) + ((6/25:ℚ)*((n:ℚ)+1)^1)*(Nat.fib (n+2):ℚ) ∧
    E 2 n = ((71/25:ℚ) + (46/25:ℚ)*(n:ℚ)^1)*(Nat.fib n:ℚ) + ((5:ℚ) + (88/25:ℚ)*(n:ℚ)^1 + (4/5:ℚ)*(n:ℚ)^2)*(Nat.fib (n+1):ℚ) ∧
    S 3 n = ((-22/25:ℚ) + (16/5:ℚ)*(n:ℚ)^1 + (-24/25:ℚ)*(n:ℚ)^2 + (24/25:ℚ)*(n:ℚ)^3)*(Nat.fib n:ℚ) + ((-36/25:ℚ)*(n:ℚ)^1 + (36/25:ℚ)*(n:ℚ)^2 + (-8/25:ℚ)*(n:ℚ)^3)*(Nat.fib (n+1):ℚ) ∧
    S 3 (n+1) = ((-22/25:ℚ) + (16/5:ℚ)*((n:ℚ)+1)^1 + (-24/25:ℚ)*((n:ℚ)+1)^2 + (24/25:ℚ)*((n:ℚ)+1)^3)*(Nat.fib (n+1):ℚ) + ((-36/25:ℚ)*((n:ℚ)+1)^1 + (36/25:ℚ)*((n:ℚ)+1)^2 + (-8/25:ℚ)*((n:ℚ)+1)^3)*(Nat.fib (n+2):ℚ) ∧
    E 3 n = ((173/25:ℚ) + (78/25:ℚ)*(n:ℚ)^1 + (72/25:ℚ)*(n:ℚ)^2 + (-8/25:ℚ)*(n:ℚ)^3)*(Nat.fib n:ℚ) + ((9:ℚ) + (284/25:ℚ)*(n:ℚ)^1 + (12/5:ℚ)*(n:ℚ)^2 + (16/25:ℚ)*(n:ℚ)^3)*(Nat.fib (n+1):ℚ) := by
  induction n with
  | zero =>
    simp only [zero_add, S_zero, S_one, E_zero]
    norm_num [Nat.fib_add_two]
  | succ n ih =>
    obtain ⟨a0, b0, c0, a1, b1, c1, a2, b2, c2, a3, b3, c3⟩ := ih
    have h21 : Nat.choose 2 1 = 2 := rfl
    have h31 : Nat.choose 3 1 = 3 := rfl
    have h32 : Nat.choose 3 2 = 3 := rfl
    refine ⟨by rw [b0], ?_, ?_, by rw [b1]; try (simp only [Nat.fib_add_two]; push_cast; ring), ?_, ?_,
      by rw [b2]; try (simp only [Nat.fib_add_two]; push_cast; ring), ?_, ?_, by rw [b3]; try (simp only [Nat.fib_add_two]; push_cast; ring), ?_, ?_⟩
    all_goals
      first | rw [recS] | rw [recE]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, a0, a1, a2, a3, c0, c1, c2, c3,
        Nat.choose_zero_right, Nat.choose_self, h21, h31, h32, Nat.fib_add_two]
      push_cast
      ring


lemma cons_last {m : ℕ} (b : Bool) (w : Fin (m+1) → Bool) :
    (Fin.cons b w : Fin (m+2) → Bool) (Fin.last (m+1)) = w (Fin.last m) := by
  rw [← Fin.succ_last, Fin.cons_succ]

lemma memL (n : ℕ) (v : Fin (n+1) → Bool) :
    v ∈ V (n+1) ↔ v ∈ G (n+1) ∧ ¬ (v 0 = true ∧ v (Fin.last n) = true) := by
  simp only [V, G, Finset.mem_filter, Finset.mem_univ, true_and]
  apply and_congr_right
  intro _
  constructor
  · rintro h ⟨h1, h2⟩
    exact h ⟨0, Fin.last n, rfl, by simp, h1, h2⟩
  · rintro h ⟨i, j, hi, hj, h1, h2⟩
    have e1 : i = 0 := Fin.ext hi
    have e2 : j = Fin.last n := Fin.ext (by simp [hj])
    subst e1 e2
    exact h ⟨h1, h2⟩

lemma L_false (n : ℕ) (w : Fin (n+2) → Bool) :
    (Fin.cons false w : Fin (n+3) → Bool) ∈ V (n+3) ↔ w ∈ G (n+2) := by
  rw [memL, cons_false_mem]; simp

lemma L_true (n : ℕ) (c : Bool) (u : Fin (n+1) → Bool) :
    (Fin.cons true (Fin.cons c u) : Fin (n+3) → Bool) ∈ V (n+3) ↔
      c = false ∧ u ∈ G (n+1) ∧ u (Fin.last n) = false := by
  rw [memL, cons_true_mem, cons_last, cons_last]
  cases c <;> simp [cons_false_mem]

lemma sum_fin {M : Type*} [AddCommMonoid M] (m : ℕ) (s : Finset (Fin m → Bool))
    (g : (Fin m → Bool) → M) : ∑ v ∈ s, g v = ∑ v, if v ∈ s then g v else 0 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma sum_splitL {M : Type*} [AddCommMonoid M] (n : ℕ) (g : (Fin (n+3) → Bool) → M) :
    ∑ v ∈ V (n+3), g v = ∑ w ∈ G (n+2), g (Fin.cons false w) +
      ∑ u ∈ G (n+1), if u (Fin.last n) = false then g (Fin.cons true (Fin.cons false u)) else 0 := by
  rw [sum_fin, sum_cons, Finset.sum_add_distrib, sum_G (n+2), sum_G (n+1)]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    simp only [L_false]
  · rw [sum_cons]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [L_true, ite_and]

lemma deg_eqL (m : ℕ) (v : Fin m → Bool) :
    deg m v = ∑ u ∈ V m, if hammingDist u v = 1 then 1 else 0 := by
  rw [deg, Finset.card_filter]

lemma card_aux {m : ℕ} (s : Finset (Fin m → Bool)) (x : Fin m → Bool) (hx : x ∈ s)
    (P : (Fin m → Bool) → Prop) [DecidablePred P] :
    (s.filter (fun y => P y ∧ y = x)).card = if P x then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨x, ?_⟩
    ext y
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, -, rfl⟩; rfl
    · rintro rfl; exact ⟨hx, h, rfl⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro y - ⟨hy, rfl⟩
    exact h hy

lemma sum_aux {m : ℕ} (s : Finset (Fin m → Bool)) (x : Fin m → Bool) (hx : x ∈ s)
    (P : (Fin m → Bool) → Prop) [DecidablePred P] :
    (∑ y ∈ s, if P y then (if y = x then 1 else 0) else 0 : ℕ) = if P x then 1 else 0 := by
  rw [← card_aux s x hx P, Finset.card_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : P y <;> by_cases h' : y = x <;> simp [h, h']

def deg0 (n : ℕ) (u : Fin (n+1) → Bool) : ℕ :=
  ∑ x ∈ G (n+1), if x (Fin.last n) = false then (if hammingDist x u = 1 then 1 else 0) else 0

lemma degL_false (n : ℕ) (w : Fin (n+2) → Bool) (hw : w ∈ G (n+2)) :
    deg (n+3) (Fin.cons false w) =
      dG (n+2) w + if (w 0 = false ∧ w (Fin.last (n+1)) = false) then 1 else 0 := by
  obtain ⟨c, x, rfl⟩ : ∃ c x, w = Fin.cons c x := ⟨_, _, (Fin.cons_self_tail w).symm⟩
  rw [deg_eqL, sum_splitL, deg_eq (n+2), cons_last]
  simp only [hd_cons]
  have hx := tail_mem c x hw
  cases c <;> simp [hammingDist_eq_zero, Finset.sum_ite_eq', hx, ← ite_and, card_aux _ _ hx]

lemma degL_true (n : ℕ) (u : Fin (n+1) → Bool) (hu : u ∈ G (n+1))
    (hl : u (Fin.last n) = false) :
    deg (n+3) (Fin.cons true (Fin.cons false u)) = deg0 n u + 1 := by
  rw [deg_eqL, sum_splitL, deg0]
  simp only [hd_cons]
  have hu' : (Fin.cons false u : Fin (n+2) → Bool) ∈ G (n+2) := (cons_false_mem u).2 hu
  simp [hammingDist_eq_zero, Finset.sum_ite_eq', hu', add_comm]

lemma deg0_false (m : ℕ) (w : Fin (m+2) → Bool) (hw : w ∈ G (m+2))
    (hl : w (Fin.last (m+1)) = false) :
    deg0 (m+2) (Fin.cons false w) = deg0 (m+1) w + if w 0 = true then 0 else 1 := by
  obtain ⟨c, x, rfl⟩ : ∃ c x, w = Fin.cons c x := ⟨_, _, (Fin.cons_self_tail w).symm⟩
  rw [cons_last] at hl
  rw [deg0, deg0, sum_split]
  simp only [hd_cons, cons_last]
  have hx := tail_mem c x hw
  cases c <;> simp [hammingDist_eq_zero, Finset.sum_ite_eq', hx, hl, ← ite_and, card_aux _ _ hx]

lemma deg0_true (m : ℕ) (u : Fin (m+1) → Bool) (hu : u ∈ G (m+1))
    (hl : u (Fin.last m) = false) :
    deg0 (m+2) (Fin.cons true (Fin.cons false u)) = deg0 m u + 1 := by
  rw [deg0, deg0, sum_split]
  simp only [hd_cons, cons_last]
  have hu' : (Fin.cons false u : Fin (m+2) → Bool) ∈ G (m+2) := (cons_false_mem u).2 hu
  have hu'' : (Fin.cons false u : Fin (m+1+1) → Bool) ∈ G (m+1+1) := hu'
  simp [hammingDist_eq_zero, Finset.sum_ite_eq', hl, sum_aux _ _ hu'', cons_last]
  ring

lemma recZgen (m : ℕ) (f : ℕ → Bool → ℚ) :
    ∑ v ∈ G (m+3), (if v (Fin.last (m+2)) = false then f (dG (m+3) v) (v 0) else 0) =
      ∑ w ∈ G (m+2), (if w (Fin.last (m+1)) = false then
        f (dG (m+2) w + if w 0 = true then 0 else 1) false else 0) +
      ∑ u ∈ G (m+1), (if u (Fin.last m) = false then f (dG (m+1) u + 1) true else 0) := by
  have := rec_gen (m+1) (fun d v => if v (Fin.last (m+2)) = false then f d (v 0) else 0)
  simp only [cons_last, Fin.cons_zero] at this
  exact this

lemma recRgen (m : ℕ) (f : ℕ → Bool → ℚ) :
    ∑ v ∈ G (m+3), (if v (Fin.last (m+2)) = false then f (deg0 (m+2) v) (v 0) else 0) =
      ∑ w ∈ G (m+2), (if w (Fin.last (m+1)) = false then
        f (deg0 (m+1) w + if w 0 = true then 0 else 1) false else 0) +
      ∑ u ∈ G (m+1), (if u (Fin.last m) = false then f (deg0 m u + 1) true else 0) := by
  rw [sum_split]
  congr 1
  · refine Finset.sum_congr rfl fun w hw => ?_
    rw [cons_last]
    by_cases hl : w (Fin.last (m+1)) = false
    · rw [if_pos hl, if_pos hl, deg0_false m w hw hl, Fin.cons_zero]
    · rw [if_neg hl, if_neg hl]
  · refine Finset.sum_congr rfl fun u hu => ?_
    rw [cons_last, cons_last]
    by_cases hl : u (Fin.last m) = false
    · rw [if_pos hl, if_pos hl, deg0_true m u hu hl, Fin.cons_zero]
    · rw [if_neg hl, if_neg hl]

noncomputable def Z (k m : ℕ) : ℚ :=
  ∑ w ∈ (G (m+1)).filter (fun w => w (Fin.last m) = false), (dG (m+1) w : ℚ) ^ k

noncomputable def Zp (k m : ℕ) : ℚ :=
  ∑ w ∈ (G (m+1)).filter (fun w => w (Fin.last m) = false),
    ((dG (m+1) w : ℚ) + if w 0 = true then 0 else 1) ^ k

noncomputable def R (k m : ℕ) : ℚ :=
  ∑ w ∈ (G (m+1)).filter (fun w => w (Fin.last m) = false), (deg0 m w : ℚ) ^ k

noncomputable def Rp (k m : ℕ) : ℚ :=
  ∑ w ∈ (G (m+1)).filter (fun w => w (Fin.last m) = false),
    ((deg0 m w : ℚ) + if w 0 = true then 0 else 1) ^ k

lemma recZ (k m : ℕ) :
    Z k (m+2) = Zp k (m+1) + ∑ j ∈ Finset.range (k+1), (k.choose j : ℚ) * Z j m := by
  have := recZgen m (fun d _ => (d : ℚ) ^ k)
  rw [show Z k (m+2) = ∑ w ∈ (G (m+3)).filter (fun w => w (Fin.last (m+2)) = false),
    (dG (m+3) w : ℚ) ^ k from rfl, Finset.sum_filter, this]
  simp only [Zp, Z]
  rw [← binom_sum, Finset.sum_filter, Finset.sum_filter]
  push_cast
  rfl

lemma recZp (k m : ℕ) :
    Zp k (m+2) = ∑ j ∈ Finset.range (k+1), (k.choose j : ℚ) * (Zp j (m+1) + Z j m) := by
  have := recZgen m (fun d b => ((d : ℚ) + if b = true then 0 else 1) ^ k)
  rw [show Zp k (m+2) = ∑ w ∈ (G (m+3)).filter (fun w => w (Fin.last (m+2)) = false),
    ((dG (m+3) w : ℚ) + if w 0 = true then 0 else 1) ^ k from rfl, Finset.sum_filter, this]
  simp_rw [mul_add, Finset.sum_add_distrib, Zp, Z]
  rw [← binom_sum, ← binom_sum, Finset.sum_filter, Finset.sum_filter]
  push_cast
  simp

lemma recR (k m : ℕ) :
    R k (m+2) = Rp k (m+1) + ∑ j ∈ Finset.range (k+1), (k.choose j : ℚ) * R j m := by
  have := recRgen m (fun d _ => (d : ℚ) ^ k)
  rw [show R k (m+2) = ∑ w ∈ (G (m+3)).filter (fun w => w (Fin.last (m+2)) = false),
    (deg0 (m+2) w : ℚ) ^ k from rfl, Finset.sum_filter, this]
  simp only [Rp, R]
  rw [← binom_sum, Finset.sum_filter, Finset.sum_filter]
  push_cast
  rfl

lemma recRp (k m : ℕ) :
    Rp k (m+2) = ∑ j ∈ Finset.range (k+1), (k.choose j : ℚ) * (Rp j (m+1) + R j m) := by
  have := recRgen m (fun d b => ((d : ℚ) + if b = true then 0 else 1) ^ k)
  rw [show Rp k (m+2) = ∑ w ∈ (G (m+3)).filter (fun w => w (Fin.last (m+2)) = false),
    ((deg0 (m+2) w : ℚ) + if w 0 = true then 0 else 1) ^ k from rfl, Finset.sum_filter, this]
  simp_rw [mul_add, Finset.sum_add_distrib, Rp, R]
  rw [← binom_sum, ← binom_sum, Finset.sum_filter, Finset.sum_filter]
  push_cast
  simp

lemma set0 : (G 1).filter (fun w => w (Fin.last 0) = false) = {![false]} := by decide

lemma set1 : (G 2).filter (fun w => w (Fin.last 1) = false) = {![false, false], ![true, false]} := by
  decide

lemma Z_zero (k : ℕ) : Z k 0 = 1 := by
  rw [Z, set0, Finset.sum_singleton, show dG 1 ![false] = 1 by decide]; simp

lemma Z_one (k : ℕ) : Z k 1 = 2 ^ k + 1 := by
  rw [Z, set1, Finset.sum_pair (by decide), show dG 2 ![false, false] = 2 by decide,
    show dG 2 ![true, false] = 1 by decide]; simp

lemma Zp_one (k : ℕ) : Zp k 1 = 3 ^ k + 1 := by
  rw [Zp, set1, Finset.sum_pair (by decide), show dG 2 ![false, false] = 2 by decide,
    show dG 2 ![true, false] = 1 by decide]; norm_num

lemma R_zero (k : ℕ) : R k 0 = if k = 0 then 1 else 0 := by
  rw [R, set0, Finset.sum_singleton, show deg0 0 ![false] = 0 by decide]
  rcases k with _ | k <;> simp

lemma R_one (k : ℕ) : R k 1 = 2 := by
  rw [R, set1, Finset.sum_pair (by decide), show deg0 1 ![false, false] = 1 by decide,
    show deg0 1 ![true, false] = 1 by decide]; norm_num

lemma Rp_one (k : ℕ) : Rp k 1 = 2 ^ k + 1 := by
  rw [Rp, set1, Finset.sum_pair (by decide), show deg0 1 ![false, false] = 1 by decide,
    show deg0 1 ![true, false] = 1 by decide]; norm_num

lemma closedR (n : ℕ) :
    R 0 n = ((1:ℚ))*(Nat.fib n:ℚ) + ((1:ℚ))*(Nat.fib (n+1):ℚ) ∧
    R 0 (n+1) = ((1:ℚ))*(Nat.fib (n+1):ℚ) + ((1:ℚ))*(Nat.fib (n+2):ℚ) ∧
    Rp 0 (n+1) = ((1:ℚ))*(Nat.fib (n+1):ℚ) + ((1:ℚ))*(Nat.fib (n+2):ℚ) ∧
    R 1 n = ((4/5:ℚ) + (4/5:ℚ)*(n:ℚ)^1)*(Nat.fib n:ℚ) + ((2/5:ℚ)*(n:ℚ)^1)*(Nat.fib (n+1):ℚ) ∧
    R 1 (n+1) = ((4/5:ℚ) + (4/5:ℚ)*((n:ℚ)+1)^1)*(Nat.fib (n+1):ℚ) + ((2/5:ℚ)*((n:ℚ)+1)^1)*(Nat.fib (n+2):ℚ) ∧
    Rp 1 (n+1) = ((4/5:ℚ) + (4/5:ℚ)*((n:ℚ)+1)^1)*(Nat.fib (n+1):ℚ) + ((1:ℚ) + (2/5:ℚ)*((n:ℚ)+1)^1)*(Nat.fib (n+2):ℚ) ∧
    R 2 n = ((2/25:ℚ) + (22/25:ℚ)*(n:ℚ)^1 + (4/5:ℚ)*(n:ℚ)^2)*(Nat.fib n:ℚ) + ((6/25:ℚ)*(n:ℚ)^1)*(Nat.fib (n+1):ℚ) ∧
    R 2 (n+1) = ((2/25:ℚ) + (22/25:ℚ)*((n:ℚ)+1)^1 + (4/5:ℚ)*((n:ℚ)+1)^2)*(Nat.fib (n+1):ℚ) + ((6/25:ℚ)*((n:ℚ)+1)^1)*(Nat.fib (n+2):ℚ) ∧
    Rp 2 (n+1) = ((32/25:ℚ) + (2/25:ℚ)*((n:ℚ)+1)^1 + (4/5:ℚ)*((n:ℚ)+1)^2)*(Nat.fib (n+1):ℚ) + ((1:ℚ) + (46/25:ℚ)*((n:ℚ)+1)^1)*(Nat.fib (n+2):ℚ) ∧
    R 3 n = ((-22/25:ℚ) + (16/5:ℚ)*(n:ℚ)^1 + (-24/25:ℚ)*(n:ℚ)^2 + (24/25:ℚ)*(n:ℚ)^3)*(Nat.fib n:ℚ) + ((-36/25:ℚ)*(n:ℚ)^1 + (36/25:ℚ)*(n:ℚ)^2 + (-8/25:ℚ)*(n:ℚ)^3)*(Nat.fib (n+1):ℚ) ∧
    R 3 (n+1) = ((-22/25:ℚ) + (16/5:ℚ)*((n:ℚ)+1)^1 + (-24/25:ℚ)*((n:ℚ)+1)^2 + (24/25:ℚ)*((n:ℚ)+1)^3)*(Nat.fib (n+1):ℚ) + ((-36/25:ℚ)*((n:ℚ)+1)^1 + (36/25:ℚ)*((n:ℚ)+1)^2 + (-8/25:ℚ)*((n:ℚ)+1)^3)*(Nat.fib (n+2):ℚ) ∧
    Rp 3 (n+1) = ((-38/5:ℚ) + (302/25:ℚ)*((n:ℚ)+1)^1 + (-84/25:ℚ)*((n:ℚ)+1)^2 + (24/25:ℚ)*((n:ℚ)+1)^3)*(Nat.fib (n+1):ℚ) + ((7:ℚ) + (-18/5:ℚ)*((n:ℚ)+1)^1 + (96/25:ℚ)*((n:ℚ)+1)^2 + (-8/25:ℚ)*((n:ℚ)+1)^3)*(Nat.fib (n+2):ℚ) := by
  induction n with
  | zero =>
    simp only [zero_add, R_zero, R_one, Rp_one]
    norm_num [Nat.fib_add_two]
  | succ n ih =>
    obtain ⟨a0, b0, c0, a1, b1, c1, a2, b2, c2, a3, b3, c3⟩ := ih
    have h21 : Nat.choose 2 1 = 2 := rfl
    have h31 : Nat.choose 3 1 = 3 := rfl
    have h32 : Nat.choose 3 2 = 3 := rfl
    refine ⟨by rw [b0]; try (simp only [Nat.fib_add_two]; push_cast; ring), ?_, ?_, by rw [b1]; try (simp only [Nat.fib_add_two]; push_cast; ring), ?_, ?_,
      by rw [b2]; try (simp only [Nat.fib_add_two]; push_cast; ring), ?_, ?_, by rw [b3]; try (simp only [Nat.fib_add_two]; push_cast; ring), ?_, ?_⟩
    all_goals
      first | rw [recR] | rw [recRp]
      simp only [add_assoc, Nat.reduceAdd]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, a0, a1, a2, a3, c0, c1, c2, c3,
        Nat.choose_zero_right, Nat.choose_self, h21, h31, h32, Nat.fib_add_two]
      push_cast
      ring

lemma closedZ (n : ℕ) :
    Z 0 (n+1) = ((1:ℚ))*(Nat.fib (n+1):ℚ) + ((1:ℚ))*(Nat.fib (n+2):ℚ) ∧
    Z 0 (n+2) = ((1:ℚ))*(Nat.fib (n+2):ℚ) + ((1:ℚ))*(Nat.fib (n+3):ℚ) ∧
    Zp 0 (n+2) = ((1:ℚ))*(Nat.fib (n+2):ℚ) + ((1:ℚ))*(Nat.fib (n+3):ℚ) ∧
    Z 1 (n+1) = ((4/5:ℚ) + (4/5:ℚ)*((n:ℚ)+1)^1)*(Nat.fib (n+1):ℚ) + ((1:ℚ) + (2/5:ℚ)*((n:ℚ)+1)^1)*(Nat.fib (n+2):ℚ) ∧
    Z 1 (n+2) = ((4/5:ℚ) + (4/5:ℚ)*((n:ℚ)+2)^1)*(Nat.fib (n+2):ℚ) + ((1:ℚ) + (2/5:ℚ)*((n:ℚ)+2)^1)*(Nat.fib (n+3):ℚ) ∧
    Zp 1 (n+2) = ((4/5:ℚ) + (4/5:ℚ)*((n:ℚ)+2)^1)*(Nat.fib (n+2):ℚ) + ((2:ℚ) + (2/5:ℚ)*((n:ℚ)+2)^1)*(Nat.fib (n+3):ℚ) ∧
    Z 2 (n+1) = ((32/25:ℚ) + (2/25:ℚ)*((n:ℚ)+1)^1 + (4/5:ℚ)*((n:ℚ)+1)^2)*(Nat.fib (n+1):ℚ) + ((1:ℚ) + (46/25:ℚ)*((n:ℚ)+1)^1)*(Nat.fib (n+2):ℚ) ∧
    Z 2 (n+2) = ((32/25:ℚ) + (2/25:ℚ)*((n:ℚ)+2)^1 + (4/5:ℚ)*((n:ℚ)+2)^2)*(Nat.fib (n+2):ℚ) + ((1:ℚ) + (46/25:ℚ)*((n:ℚ)+2)^1)*(Nat.fib (n+3):ℚ) ∧
    Zp 2 (n+2) = ((112/25:ℚ) + (-18/25:ℚ)*((n:ℚ)+2)^1 + (4/5:ℚ)*((n:ℚ)+2)^2)*(Nat.fib (n+2):ℚ) + ((2:ℚ) + (86/25:ℚ)*((n:ℚ)+2)^1)*(Nat.fib (n+3):ℚ) ∧
    Z 3 (n+1) = ((-38/5:ℚ) + (302/25:ℚ)*((n:ℚ)+1)^1 + (-84/25:ℚ)*((n:ℚ)+1)^2 + (24/25:ℚ)*((n:ℚ)+1)^3)*(Nat.fib (n+1):ℚ) + ((7:ℚ) + (-18/5:ℚ)*((n:ℚ)+1)^1 + (96/25:ℚ)*((n:ℚ)+1)^2 + (-8/25:ℚ)*((n:ℚ)+1)^3)*(Nat.fib (n+2):ℚ) ∧
    Z 3 (n+2) = ((-38/5:ℚ) + (302/25:ℚ)*((n:ℚ)+2)^1 + (-84/25:ℚ)*((n:ℚ)+2)^2 + (24/25:ℚ)*((n:ℚ)+2)^3)*(Nat.fib (n+2):ℚ) + ((7:ℚ) + (-18/5:ℚ)*((n:ℚ)+2)^1 + (96/25:ℚ)*((n:ℚ)+2)^2 + (-8/25:ℚ)*((n:ℚ)+2)^3)*(Nat.fib (n+3):ℚ) ∧
    Zp 3 (n+2) = ((-628/25:ℚ) + (704/25:ℚ)*((n:ℚ)+2)^1 + (-144/25:ℚ)*((n:ℚ)+2)^2 + (24/25:ℚ)*((n:ℚ)+2)^3)*(Nat.fib (n+2):ℚ) + ((26:ℚ) + (-204/25:ℚ)*((n:ℚ)+2)^1 + (156/25:ℚ)*((n:ℚ)+2)^2 + (-8/25:ℚ)*((n:ℚ)+2)^3)*(Nat.fib (n+3):ℚ) := by
  induction n with
  | zero =>
    have z2 := fun k => recZ k 0
    have zp2 := fun k => recZp k 0
    simp only [zero_add] at z2 zp2 ⊢
    have h21 : Nat.choose 2 1 = 2 := rfl
    have h31 : Nat.choose 3 1 = 3 := rfl
    have h32 : Nat.choose 3 2 = 3 := rfl
    simp only [z2, zp2, Finset.sum_range_succ, Finset.sum_range_zero, Z_zero, Z_one, Zp_one,
      Nat.choose_zero_right, Nat.choose_self, h21, h31, h32]
    norm_num [Nat.fib_add_two]
  | succ n ih =>
    obtain ⟨a0, b0, c0, a1, b1, c1, a2, b2, c2, a3, b3, c3⟩ := ih
    have h21 : Nat.choose 2 1 = 2 := rfl
    have h31 : Nat.choose 3 1 = 3 := rfl
    have h32 : Nat.choose 3 2 = 3 := rfl
    refine ⟨by rw [b0]; try (simp only [Nat.fib_add_two]; push_cast; ring), ?_, ?_, by rw [b1]; try (simp only [Nat.fib_add_two]; push_cast; ring), ?_, ?_,
      by rw [b2]; try (simp only [Nat.fib_add_two]; push_cast; ring), ?_, ?_, by rw [b3]; try (simp only [Nat.fib_add_two]; push_cast; ring), ?_, ?_⟩
    all_goals
      first | rw [recZ] | rw [recZp]
      simp only [add_assoc, Nat.reduceAdd]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, a0, a1, a2, a3, c0, c1, c2, c3,
        Nat.choose_zero_right, Nat.choose_self, h21, h31, h32, Nat.fib_add_two]
      push_cast
      ring

lemma a_decomp (n : ℕ) : (a (n+3) : ℚ) = S 3 (n+2) - Z 3 (n+1) + Zp 3 (n+1) +
    ∑ j ∈ Finset.range (3+1), ((3:ℕ).choose j : ℚ) * R j n := by
  have h1 : (a (n+3) : ℚ) = ∑ v ∈ V (n+3), (deg (n+3) v : ℚ) ^ 3 := by simp [a]
  rw [h1, sum_splitL]
  have e1 : ∑ w ∈ G (n+2), ((deg (n+3) (Fin.cons false w) : ℚ)) ^ 3 =
      ∑ w ∈ G (n+2), ((dG (n+2) w : ℚ) +
        if (w 0 = false ∧ w (Fin.last (n+1)) = false) then 1 else 0) ^ 3 :=
    Finset.sum_congr rfl fun w hw => by rw [degL_false n w hw]; push_cast; rfl
  have e2 : (∑ u ∈ G (n+1), if u (Fin.last n) = false then
        ((deg (n+3) (Fin.cons true (Fin.cons false u)) : ℚ)) ^ 3 else 0) =
      ∑ u ∈ G (n+1), if u (Fin.last n) = false then ((deg0 n u : ℚ) + 1) ^ 3 else 0 :=
    Finset.sum_congr rfl fun u hu => by
      split_ifs with hl
      · rw [degL_true n u hu hl]; push_cast; rfl
      · rfl
  rw [e1, e2]
  have e3 : (∑ u ∈ G (n+1), if u (Fin.last n) = false then ((deg0 n u : ℚ) + 1) ^ 3 else 0) =
      ∑ j ∈ Finset.range (3+1), ((3:ℕ).choose j : ℚ) * R j n := by
    rw [← Finset.sum_filter, binom_sum]; rfl
  have e4 : ∑ w ∈ G (n+2), ((dG (n+2) w : ℚ) +
        if (w 0 = false ∧ w (Fin.last (n+1)) = false) then 1 else 0) ^ 3 =
      S 3 (n+2) - Z 3 (n+1) + Zp 3 (n+1) := by
    rw [show Z 3 (n+1) = ∑ w ∈ G (n+2), if w (Fin.last (n+1)) = false then
        (dG (n+2) w : ℚ) ^ 3 else 0 by rw [Z, Finset.sum_filter],
      show Zp 3 (n+1) = ∑ w ∈ G (n+2), if w (Fin.last (n+1)) = false then
        ((dG (n+2) w : ℚ) + if w 0 = true then 0 else 1) ^ 3 else 0 by rw [Zp, Finset.sum_filter],
      S, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h0 : w 0 = true <;> by_cases hl : w (Fin.last (n+1)) = false <;> simp [h0, hl]
  rw [e3, e4]

lemma aclosed (n : ℕ) : (a (n+4) : ℚ) = ((-1448/25:ℚ)*((n:ℚ)+4)^1 + (732/25:ℚ)*((n:ℚ)+4)^2 + (-24/5:ℚ)*((n:ℚ)+4)^3)*(Nat.fib (n+4):ℚ) + ((36:ℚ)*((n:ℚ)+4)^1 + (-444/25:ℚ)*((n:ℚ)+4)^2 + (16/5:ℚ)*((n:ℚ)+4)^3)*(Nat.fib (n+5):ℚ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hS3, -, -⟩ := closed (n+3)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hZ3, hZp3⟩ := closedZ n
  obtain ⟨hR0, -, -, hR1, -, -, hR2, -, -, hR3, -, -⟩ := closedR (n+1)
  have h31 : Nat.choose 3 1 = 3 := rfl
  have h32 : Nat.choose 3 2 = 3 := rfl
  rw [show n + 4 = (n+1) + 3 from rfl, a_decomp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right, Nat.choose_self,
    h31, h32]
  simp only [add_assoc, Nat.reduceAdd] at hS3 hZ3 hZp3 hR0 hR1 hR2 hR3 ⊢
  rw [hS3, hZ3, hZp3, hR0, hR1, hR2, hR3]
  simp only [Nat.fib_add_two]
  push_cast
  ring

lemma av4 : (a 4 : ℚ) = 112 := by
  rw [show (4:ℕ) = 0 + 4 from rfl, aclosed 0, show Nat.fib (0+4) = 3 from rfl,
    show Nat.fib (0+5) = 5 from rfl]
  norm_num

lemma av5 : (a 5 : ℚ) = 300 := by
  rw [show (5:ℕ) = 1 + 4 from rfl, aclosed 1, show Nat.fib (1+4) = 5 from rfl,
    show Nat.fib (1+5) = 8 from rfl]
  norm_num

lemma av6 : (a 6 : ℚ) = 840 := by
  rw [show (6:ℕ) = 2 + 4 from rfl, aclosed 2, show Nat.fib (2+4) = 8 from rfl,
    show Nat.fib (2+5) = 13 from rfl]
  norm_num

lemma av7 : (a 7 : ℚ) = 2044 := by
  rw [show (7:ℕ) = 3 + 4 from rfl, aclosed 3, show Nat.fib (3+4) = 13 from rfl,
    show Nat.fib (3+5) = 21 from rfl]
  norm_num

lemma av8 : (a 8 : ℚ) = 4864 := by
  rw [show (8:ℕ) = 4 + 4 from rfl, aclosed 4, show Nat.fib (4+4) = 21 from rfl,
    show Nat.fib (4+5) = 34 from rfl]
  norm_num

lemma av9 : (a 9 : ℚ) = 10944 := by
  rw [show (9:ℕ) = 5 + 4 from rfl, aclosed 5, show Nat.fib (5+4) = 34 from rfl,
    show Nat.fib (5+5) = 55 from rfl]
  norm_num

lemma av10 : (a 10 : ℚ) = 23960 := by
  rw [show (10:ℕ) = 6 + 4 from rfl, aclosed 6, show Nat.fib (6+4) = 55 from rfl,
    show Nat.fib (6+5) = 89 from rfl]
  norm_num

lemma av11 : (a 11 : ℚ) = 50908 := by
  rw [show (11:ℕ) = 7 + 4 from rfl, aclosed 7, show Nat.fib (7+4) = 89 from rfl,
    show Nat.fib (7+5) = 144 from rfl]
  norm_num

lemma key (m : ℕ) : (a (m+12) : ℚ) - 4 * a (m+11) + 2 * a (m+10) + 8 * a (m+9) - 5 * a (m+8)
    - 8 * a (m+7) + 2 * a (m+6) + 4 * a (m+5) + a (m+4) = 0 := by
  have h0 := aclosed (m+0)
  have h1 := aclosed (m+1)
  have h2 := aclosed (m+2)
  have h3 := aclosed (m+3)
  have h4 := aclosed (m+4)
  have h5 := aclosed (m+5)
  have h6 := aclosed (m+6)
  have h7 := aclosed (m+7)
  have h8 := aclosed (m+8)
  simp only [add_assoc, Nat.reduceAdd] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  simp only [Nat.fib_add_two]
  push_cast
  ring

lemma av0 : (a 0 : ℚ) = 0 := by rw [show a 0 = 0 by decide]; norm_num
lemma av1 : (a 1 : ℚ) = 0 := by rw [show a 1 = 0 by decide]; norm_num
lemma av2 : (a 2 : ℚ) = 10 := by rw [show a 2 = 10 by decide]; norm_num
lemma av3 : (a 3 : ℚ) = 30 := by rw [show a 3 = 30 by decide]; norm_num


theorem gen_main (f : ℕ → ℕ) (v0 : (f 0 : ℚ) = 0) (v1 : (f 1 : ℚ) = 0) (v2 : (f 2 : ℚ) = 10) (v3 : (f 3 : ℚ) = 30) (v4 : (f 4 : ℚ) = 112) (v5 : (f 5 : ℚ) = 300) (v6 : (f 6 : ℚ) = 840) (v7 : (f 7 : ℚ) = 2044) (v8 : (f 8 : ℚ) = 4864) (v9 : (f 9 : ℚ) = 10944) (v10 : (f 10 : ℚ) = 23960) (v11 : (f 11 : ℚ) = 50908)
    (hk : ∀ m : ℕ, (f (m+12) : ℚ) - 4 * f (m+11) + 2 * f (m+10) + 8 * f (m+9) - 5 * f (m+8)
      - 8 * f (m+7) + 2 * f (m+6) + 4 * f (m+5) + f (m+4) = 0) :
    PowerSeries.mk (fun n => (f n : ℚ)) * (1 - PowerSeries.X - PowerSeries.X ^ 2) ^ 4 =
      2 * PowerSeries.X ^ 2 * (5 - 5 * PowerSeries.X + 6 * PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 +
        27 * PowerSeries.X ^ 4 - 25 * PowerSeries.X ^ 5 - 6 * PowerSeries.X ^ 6 + 9 * PowerSeries.X ^ 8 +
        3 * PowerSeries.X ^ 9) ∧
    ∀ n : ℕ, 12 ≤ n → (f n : ℤ) = 4 * f (n - 1) - 2 * f (n - 2) - 8 * f (n - 3) + 5 * f (n - 4) +
      8 * f (n - 5) - 2 * f (n - 6) - 4 * f (n - 7) - f (n - 8) := by
  refine ⟨?_, ?_⟩
  · open PowerSeries in
    have hL : mk (fun n => (f n : ℚ)) * (1 - X - X ^ 2) ^ 4 =
        mk (fun n => (f n : ℚ)) * X ^ 0 - C (4:ℚ) * (mk (fun n => (f n : ℚ)) * X ^ 1)
        + C (2:ℚ) * (mk (fun n => (f n : ℚ)) * X ^ 2) + C (8:ℚ) * (mk (fun n => (f n : ℚ)) * X ^ 3)
        - C (5:ℚ) * (mk (fun n => (f n : ℚ)) * X ^ 4) - C (8:ℚ) * (mk (fun n => (f n : ℚ)) * X ^ 5)
        + C (2:ℚ) * (mk (fun n => (f n : ℚ)) * X ^ 6) + C (4:ℚ) * (mk (fun n => (f n : ℚ)) * X ^ 7)
        + mk (fun n => (f n : ℚ)) * X ^ 8 := by
      simp only [map_ofNat]; ring
    open PowerSeries in
    have hR : (2 * X ^ 2 * (5 - 5 * X + 6 * X ^ 2 - 4 * X ^ 3 + 27 * X ^ 4 - 25 * X ^ 5 -
        6 * X ^ 6 + 9 * X ^ 8 + 3 * X ^ 9) : PowerSeries ℚ) =
        C (10:ℚ) * X ^ 2 - C (10:ℚ) * X ^ 3 + C (12:ℚ) * X ^ 4 - C (8:ℚ) * X ^ 5
        + C (54:ℚ) * X ^ 6 - C (50:ℚ) * X ^ 7 - C (12:ℚ) * X ^ 8 + C (18:ℚ) * X ^ 10
        + C (6:ℚ) * X ^ 11 := by
      simp only [map_ofNat]; ring
    rw [hL, hR]
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_X_pow, PowerSeries.coeff_mk]
    rcases Nat.lt_or_ge n 12 with hn | hn
    · interval_cases n <;>
        simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
      have := hk m
      simp only [show m + 12 - 1 = m + 11 by omega, show m + 12 - 2 = m + 10 by omega,
        show m + 12 - 3 = m + 9 by omega, show m + 12 - 4 = m + 8 by omega,
        show m + 12 - 5 = m + 7 by omega, show m + 12 - 6 = m + 6 by omega,
        show m + 12 - 7 = m + 5 by omega, show m + 12 - 8 = m + 4 by omega,
        show m + 12 - 0 = m + 12 by omega]
      simp only [show (0 ≤ m + 12) by omega, show (1 ≤ m + 12) by omega, show (2 ≤ m + 12) by omega,
        show (3 ≤ m + 12) by omega, show (4 ≤ m + 12) by omega, show (5 ≤ m + 12) by omega,
        show (6 ≤ m + 12) by omega, show (7 ≤ m + 12) by omega, show (8 ≤ m + 12) by omega,
        show (m + 12 ≠ 2) by omega, show (m + 12 ≠ 3) by omega, show (m + 12 ≠ 4) by omega,
        show (m + 12 ≠ 5) by omega, show (m + 12 ≠ 6) by omega, show (m + 12 ≠ 7) by omega,
        show (m + 12 ≠ 8) by omega, show (m + 12 ≠ 10) by omega, show (m + 12 ≠ 11) by omega,
        show (10 ≤ m + 12) by omega, show (11 ≤ m + 12) by omega,
        show (m + 12 - 10 ≠ 0) by omega, show (m + 12 - 11 ≠ 0) by omega,
        if_true, if_false]
      simp only [PowerSeries.coeff_C, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, one_ne_zero,
        and_false, if_false]
      rw [if_neg (by omega), if_neg (by omega)]
      linarith
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
    have := hk m
    simp only [show m + 12 - 1 = m + 11 by omega, show m + 12 - 2 = m + 10 by omega,
      show m + 12 - 3 = m + 9 by omega, show m + 12 - 4 = m + 8 by omega,
      show m + 12 - 5 = m + 7 by omega, show m + 12 - 6 = m + 6 by omega,
      show m + 12 - 7 = m + 5 by omega, show m + 12 - 8 = m + 4 by omega]
    have h : ((f (m + 12) : ℤ) : ℚ) = ((4 * f (m + 11) - 2 * f (m + 10) - 8 * f (m + 9)
        + 5 * f (m + 8) + 8 * f (m + 7) - 2 * f (m + 6) - 4 * f (m + 5)
        - f (m + 4) : ℤ) : ℚ) := by
      push_cast; linarith
    exact_mod_cast h

theorem test_main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (1 - PowerSeries.X - PowerSeries.X ^ 2) ^ 4 =
      2 * PowerSeries.X ^ 2 * (5 - 5 * PowerSeries.X + 6 * PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 +
        27 * PowerSeries.X ^ 4 - 25 * PowerSeries.X ^ 5 - 6 * PowerSeries.X ^ 6 + 9 * PowerSeries.X ^ 8 +
        3 * PowerSeries.X ^ 9) ∧
    ∀ n : ℕ, 12 ≤ n → (a n : ℤ) = 4 * a (n - 1) - 2 * a (n - 2) - 8 * a (n - 3) + 5 * a (n - 4) +
      8 * a (n - 5) - 2 * a (n - 6) - 4 * a (n - 7) - a (n - 8) :=
  gen_main a av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 key

end OMA.P307307

theorem OMA.solution : type_of% @OMA.S_oeis_a307307.main := OMA.P307307.test_main
