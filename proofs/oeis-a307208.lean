import OMAStatements.S_oeis_a307208

-- Problem: A307208: a(n) is the forgotten index of the Fibonacci cube Gamma(n).
-- Upstream: formal-conjectures statements/oeis-a307208.lean:0 (declaration OMA.S_oeis_a307208.main)
-- Credit: @marcusbuffett (the owner of the agent is credited as the solver)
-- Proof: every Fibonacci string of length n+2 is 0w (w of length n+1) or 10u (u of length n),
-- with deg(0w) = deg(w) + [w starts with 0] and deg(10u) = deg(u) + 1. This gives linear
-- recurrences for the moments S k n = sum of deg^k and E k n = sum of (deg + [head is 0])^k,
-- k = 0..3, whose solutions are p(n) F(n) + q(n) F(n+1) with cubic p, q. The closed form of
-- a(n) = S 3 n is then annihilated by (1 - x - x^2)^4.

namespace OMA.P307208

open OMA.S_oeis_a307208

lemma mem_V {m : ℕ} (v : Fin m → Bool) :
    v ∈ V m ↔ ∀ i j : Fin m, j.1 = i.1 + 1 → ¬ (v i = true ∧ v j = true) := by
  simp [V]

lemma tail_mem {m : ℕ} (c : Bool) (w : Fin m → Bool)
    (h : (Fin.cons c w : Fin (m+1) → Bool) ∈ V (m+1)) : w ∈ V m := by
  rw [mem_V] at h ⊢
  intro i j hij
  simpa using h i.succ j.succ (by simp [hij])

lemma cons_false_mem {m : ℕ} (w : Fin m → Bool) :
    (Fin.cons false w : Fin (m+1) → Bool) ∈ V (m+1) ↔ w ∈ V m := by
  refine ⟨tail_mem false w, fun h => ?_⟩
  rw [mem_V] at h ⊢
  intro i j hij
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    cases j using Fin.cases with
    | zero => simp at hij
    | succ j => simpa using h i j (by simpa using hij)

lemma cons_true_mem {n : ℕ} (w : Fin (n+1) → Bool) :
    (Fin.cons true w : Fin (n+2) → Bool) ∈ V (n+2) ↔ w ∈ V (n+1) ∧ w 0 = false := by
  constructor
  · intro h
    refine ⟨tail_mem true w h, ?_⟩
    rw [mem_V] at h
    have := h 0 1 (by simp)
    simpa using this
  · rintro ⟨h, h0⟩
    rw [mem_V] at h ⊢
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

lemma sum_V {M : Type*} [AddCommMonoid M] (m : ℕ) (g : (Fin m → Bool) → M) :
    ∑ v ∈ V m, g v = ∑ v, if v ∈ V m then g v else 0 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma sum_cons {M : Type*} [AddCommMonoid M] (m : ℕ) (g : (Fin (m+1) → Bool) → M) :
    ∑ v, g v = ∑ w : Fin m → Bool, (g (Fin.cons false w) + g (Fin.cons true w)) := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => add_comm _ _

lemma sum_split {M : Type*} [AddCommMonoid M] (n : ℕ) (g : (Fin (n+2) → Bool) → M) :
    ∑ v ∈ V (n+2), g v = ∑ w ∈ V (n+1), g (Fin.cons false w) +
      ∑ u ∈ V n, g (Fin.cons true (Fin.cons false u)) := by
  rw [sum_V, sum_cons, Finset.sum_add_distrib, sum_V (n+1), sum_V n]
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
    deg m v = ∑ u ∈ V m, if hammingDist u v = 1 then 1 else 0 := by
  rw [deg, Finset.card_filter]

lemma deg_cons_false (n : ℕ) (c : Bool) (x : Fin n → Bool)
    (hw : (Fin.cons c x : Fin (n+1) → Bool) ∈ V (n+1)) :
    deg (n+2) (Fin.cons false (Fin.cons c x)) =
      deg (n+1) (Fin.cons c x) + (if c = true then 0 else 1) := by
  rw [deg_eq, sum_split, deg_eq (n+1)]
  simp only [hd_cons]
  have hx := tail_mem c x hw
  cases c <;> simp [hammingDist_eq_zero, Finset.sum_ite_eq', hx]

lemma deg_cons_true (n : ℕ) (u : Fin n → Bool) (hu : u ∈ V n) :
    deg (n+2) (Fin.cons true (Fin.cons false u)) = deg n u + 1 := by
  rw [deg_eq, sum_split, deg_eq n]
  simp only [hd_cons]
  have hu' : (Fin.cons false u : Fin (n+1) → Bool) ∈ V (n+1) := (cons_false_mem u).2 hu
  simp [hammingDist_eq_zero, Finset.sum_ite_eq', hu', add_comm]

lemma rec_main (n : ℕ) (f : ℕ → Bool → ℚ) :
    ∑ v ∈ V (n+2), f (deg (n+2) v) (v 0) =
      ∑ w ∈ V (n+1), f (deg (n+1) w + if w 0 = true then 0 else 1) false +
      ∑ u ∈ V n, f (deg n u + 1) true := by
  rw [sum_split]
  congr 1
  · refine Finset.sum_congr rfl fun w hw => ?_
    have hw' : (Fin.cons (w 0) (Fin.tail w) : Fin (n+1) → Bool) ∈ V (n+1) := by
      rwa [Fin.cons_self_tail]
    have := deg_cons_false n (w 0) (Fin.tail w) hw'
    rw [Fin.cons_self_tail] at this
    simp [this]
  · refine Finset.sum_congr rfl fun u hu => ?_
    simp [deg_cons_true n u hu]

noncomputable def S (k n : ℕ) : ℚ := ∑ v ∈ V n, (deg n v : ℚ) ^ k

noncomputable def E (k n : ℕ) : ℚ :=
  ∑ w ∈ V (n+1), ((deg (n+1) w : ℚ) + if w 0 = true then 0 else 1) ^ k

lemma binom_sum {α : Type*} (s : Finset α) (x : α → ℚ) (k : ℕ) :
    ∑ a ∈ s, (x a + 1) ^ k = ∑ j ∈ Finset.range (k+1), (k.choose j : ℚ) * ∑ a ∈ s, x a ^ j := by
  simp_rw [add_pow, one_pow, mul_one]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

lemma recS (k n : ℕ) :
    S k (n+2) = E k n + ∑ j ∈ Finset.range (k+1), (k.choose j : ℚ) * S j n := by
  have := rec_main n (fun d _ => (d : ℚ) ^ k)
  rw [show S k (n+2) = ∑ v ∈ V (n+2), (deg (n+2) v : ℚ) ^ k from rfl, this]
  simp only [S, E]
  rw [← binom_sum]
  push_cast
  rfl

lemma recE (k n : ℕ) :
    E k (n+1) = ∑ j ∈ Finset.range (k+1), (k.choose j : ℚ) * (E j n + S j n) := by
  have := rec_main n (fun d b => ((d : ℚ) + if b = true then 0 else 1) ^ k)
  have h2 : E k (n+1) =
      ∑ v ∈ V (n+2), ((deg (n+2) v : ℚ) + if v 0 = true then 0 else 1) ^ k := rfl
  rw [h2, this]
  simp_rw [mul_add, Finset.sum_add_distrib, E, S]
  rw [← binom_sum, ← binom_sum]
  push_cast
  simp

lemma deg_zero (v : Fin 0 → Bool) : deg 0 v = 0 := by
  rw [deg_eq]; simp [hammingDist]

lemma V_one : V 1 = Finset.univ := by decide

lemma deg_one : ∀ v : Fin 1 → Bool, deg 1 v = 1 := by decide

lemma S_zero (k : ℕ) : S k 0 = if k = 0 then 1 else 0 := by
  simp [S, deg_zero, V]
  rcases k with _ | k <;> simp

lemma S_one (k : ℕ) : S k 1 = 2 := by
  simp [S, deg_one, V_one]

lemma E_zero (k : ℕ) : E k 0 = 2 ^ k + 1 := by
  rw [E, sum_V, sum_cons]
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
    refine ⟨by rw [b0], ?_, ?_, by rw [b1]; push_cast; try rfl, ?_, ?_,
      by rw [b2]; push_cast; try rfl, ?_, ?_, by rw [b3]; push_cast; try rfl, ?_, ?_⟩
    all_goals
      first | rw [recS] | rw [recE]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, a0, a1, a2, a3, c0, c1, c2, c3,
        Nat.choose_zero_right, Nat.choose_self, h21, h31, h32, Nat.fib_add_two]
      push_cast
      ring

lemma aq (n : ℕ) : (a n : ℚ) = S 3 n := by simp [a, S]

lemma acl (n : ℕ) : (a n : ℚ) =
    ((-22/25:ℚ) + (16/5:ℚ)*(n:ℚ)^1 + (-24/25:ℚ)*(n:ℚ)^2 + (24/25:ℚ)*(n:ℚ)^3)*(Nat.fib n:ℚ) +
      ((-36/25:ℚ)*(n:ℚ)^1 + (36/25:ℚ)*(n:ℚ)^2 + (-8/25:ℚ)*(n:ℚ)^3)*(Nat.fib (n+1):ℚ) := by
  rw [aq]; exact (closed n).2.2.2.2.2.2.2.2.2.1

lemma key (m : ℕ) : (a (m+8) : ℚ) - 4 * a (m+7) + 2 * a (m+6) + 8 * a (m+5) - 5 * a (m+4)
    - 8 * a (m+3) + 2 * a (m+2) + 4 * a (m+1) + a m = 0 := by
  simp only [acl]
  push_cast
  simp only [Nat.fib_add_two, Nat.cast_add]
  ring

theorem test_main : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - PowerSeries.X - PowerSeries.X ^ 2) ^ 4 =
      2 * PowerSeries.X * (1 + PowerSeries.X + 8 * PowerSeries.X ^ 2 - 7 * PowerSeries.X ^ 3 +
        4 * PowerSeries.X ^ 4 - 3 * PowerSeries.X ^ 5 + 3 * PowerSeries.X ^ 6) ∧
    ∀ n : ℕ, 9 ≤ n → (a n : ℤ) = 4 * a (n - 1) - 2 * a (n - 2) - 8 * a (n - 3) + 5 * a (n - 4) +
      8 * a (n - 5) - 2 * a (n - 6) - 4 * a (n - 7) - a (n - 8) := by
  refine ⟨?_, ?_⟩
  · open PowerSeries in
    have hL : mk (fun n => (a n : ℚ)) * (1 - X - X ^ 2) ^ 4 =
        mk (fun n => (a n : ℚ)) * X ^ 0 - C (4:ℚ) * (mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (2:ℚ) * (mk (fun n => (a n : ℚ)) * X ^ 2) + C (8:ℚ) * (mk (fun n => (a n : ℚ)) * X ^ 3)
        - C (5:ℚ) * (mk (fun n => (a n : ℚ)) * X ^ 4) - C (8:ℚ) * (mk (fun n => (a n : ℚ)) * X ^ 5)
        + C (2:ℚ) * (mk (fun n => (a n : ℚ)) * X ^ 6) + C (4:ℚ) * (mk (fun n => (a n : ℚ)) * X ^ 7)
        + mk (fun n => (a n : ℚ)) * X ^ 8 := by
      simp only [map_ofNat]; ring
    open PowerSeries in
    have hR : (2 * X * (1 + X + 8 * X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4 - 3 * X ^ 5 + 3 * X ^ 6) :
        PowerSeries ℚ) = C (2:ℚ) * X ^ 1 + C (2:ℚ) * X ^ 2 + C (16:ℚ) * X ^ 3 - C (14:ℚ) * X ^ 4
        + C (8:ℚ) * X ^ 5 - C (6:ℚ) * X ^ 6 + C (6:ℚ) * X ^ 7 := by
      simp only [map_ofNat]; ring
    rw [hL, hR]
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X_pow, PowerSeries.coeff_mk]
    rcases Nat.lt_or_ge n 8 with hn | hn
    · interval_cases n <;> simp [acl, Nat.fib_add_two] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      have := key m
      simp only [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
        show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega,
        show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega,
        show m + 8 - 7 = m + 1 by omega, show m + 8 - 8 = m by omega, show m + 8 - 0 = m + 8 by omega]
      simp only [show (0 ≤ m + 8) by omega, show (1 ≤ m + 8) by omega, show (2 ≤ m + 8) by omega,
        show (3 ≤ m + 8) by omega, show (4 ≤ m + 8) by omega, show (5 ≤ m + 8) by omega,
        show (6 ≤ m + 8) by omega, show (7 ≤ m + 8) by omega, show (8 ≤ m + 8) by omega,
        show (m + 8 ≠ 1) by omega, show (m + 8 ≠ 2) by omega, show (m + 8 ≠ 3) by omega,
        show (m + 8 ≠ 4) by omega, show (m + 8 ≠ 5) by omega, show (m + 8 ≠ 6) by omega,
        show (m + 8 ≠ 7) by omega, if_true, if_false]
      simp only [PowerSeries.coeff_C, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, one_ne_zero, and_false, if_false]
      linarith
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    have := key (m + 1)
    simp only [show m + 9 - 1 = m + 1 + 7 by omega, show m + 9 - 2 = m + 1 + 6 by omega,
      show m + 9 - 3 = m + 1 + 5 by omega, show m + 9 - 4 = m + 1 + 4 by omega,
      show m + 9 - 5 = m + 1 + 3 by omega, show m + 9 - 6 = m + 1 + 2 by omega,
      show m + 9 - 7 = m + 1 + 1 by omega, show m + 9 - 8 = m + 1 by omega,
      show m + 9 = m + 1 + 8 by omega]
    have h : ((a (m + 1 + 8) : ℤ) : ℚ) = ((4 * a (m + 1 + 7) - 2 * a (m + 1 + 6) - 8 * a (m + 1 + 5)
        + 5 * a (m + 1 + 4) + 8 * a (m + 1 + 3) - 2 * a (m + 1 + 2) - 4 * a (m + 1 + 1)
        - a (m + 1) : ℤ) : ℚ) := by
      push_cast; linarith
    exact_mod_cast h

end OMA.P307208

theorem OMA.solution : type_of% @OMA.S_oeis_a307208.main := OMA.P307208.test_main
