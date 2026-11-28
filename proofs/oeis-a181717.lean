import OMAStatements.S_oeis_a181717
import Mathlib

-- Credit: @Aryan-Poonacha
-- Ralf Stephan's sequence and Giovanni Resta's conjecture, OEIS A181717 (2010).
namespace FibonacciCollatz

open OMA.S_oeis_a181717

private def b (x : ℕ) := 5*x+1

private lemma big (x y : ℕ) (h : (x+y)%2 ≠ 0) :
    b (OMA.S_oeis_a181717.next x y) = 3*(b x+b y) := by
  simp [OMA.S_oeis_a181717.next, h, b]
  omega

private lemma preserve (k x y : ℕ) (hx : 3^k ∣ b x) (hy : 3^k ∣ b y) :
    3^k ∣ b (OMA.S_oeis_a181717.next x y) := by
  by_cases h : (x+y)%2=0
  · have hc : (3^k).Coprime 2 := (by decide : Nat.Coprime 3 2).pow_left k
    apply hc.dvd_of_dvd_mul_left
    have he : 2*b (OMA.S_oeis_a181717.next x y) = b x+b y := by
      simp [OMA.S_oeis_a181717.next, h, b]
      omega
    rw [he]
    exact dvd_add hx hy
  · rw [big x y h]
    exact dvd_mul_of_dvd_right (dvd_add hx hy) _

private lemma gain (k x y : ℕ) (h : (x+y)%2 ≠ 0)
    (hx : 3^k ∣ b x) (hy : 3^k ∣ b y) : 3^(k+1) ∣ b (OMA.S_oeis_a181717.next x y) := by
  rw [big x y h, pow_succ']
  exact Nat.mul_dvd_mul_left 3 (dvd_add hx hy)

def u (s : ℕ × ℕ) (n : ℕ) := (orbit s n).1

private lemma rec (s : ℕ × ℕ) (n : ℕ) : u s (n+2) = OMA.S_oeis_a181717.next (u s n) (u s (n+1)) := rfl

private lemma tail_div (s : ℕ × ℕ) (k t : ℕ) (h₀ : 3^k ∣ b (u s t))
    (h₁ : 3^k ∣ b (u s (t+1))) : ∀ n, t ≤ n → 3^k ∣ b (u s n) := by
  have H (j : ℕ) : 3^k ∣ b (u s (t+j)) ∧ 3^k ∣ b (u s (t+j+1)) := by
    induction j with
    | zero => exact ⟨h₀,h₁⟩
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      change 3^k ∣ b (u s ((t+j)+2))
      rw [rec s (t+j)]
      exact preserve k _ _ ih.1 ih.2
  intro n hn
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn
  exact (H j).1

private lemma many (s : ℕ × ℕ)
    (hs : ∀ t, ∃ n, t ≤ n ∧ u s n % 2 = 0 ∧ u s (n+1) % 2 = 1) :
    ∀ k : ℕ, ∃ t, ∀ n, t ≤ n → 3^k ∣ b (u s n) := by
  intro k
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨t,ht⟩ := ih
    obtain ⟨j,hj,he,ho⟩ := hs t
    have h : (u s j+u s (j+1))%2 ≠ 0 := by omega
    have hz : u s (j+2)%2=0 := by rw [rec s j]; simp [OMA.S_oeis_a181717.next, h]; omega
    refine ⟨j+2, tail_div s (k+1) (j+2) ?_ ?_⟩
    · rw [rec s j]
      exact gain k _ _ h (ht j hj) (ht _ (by omega))
    · rw [rec s (j+1)]
      have hz' : u s (j+1+1)%2 = 0 := hz
      exact gain k _ _ (by omega) (ht _ (by omega)) (ht _ (by omega))

private lemma fixed (s : ℕ × ℕ) (t : ℕ) (h : u s t = u s (t+1)) :
    ∀ n, t ≤ n → u s n = u s t := by
  have H (j : ℕ) : u s (t+j) = u s t ∧ u s (t+j+1) = u s t := by
    induction j with
    | zero => exact ⟨rfl,h.symm⟩
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      change u s ((t+j)+2) = u s t
      rw [rec s (t+j), ih.1, ih.2]
      simp [OMA.S_oeis_a181717.next, ← two_mul]
  intro n hn
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn
  exact (H j).1

private lemma few (s : ℕ × ℕ)
    (hs : ¬ ∀ t, ∃ n, t ≤ n ∧ u s n % 2 = 0 ∧ u s (n+1) % 2 = 1) :
    ∃ t, ∀ n, t ≤ n → u s n = u s t := by
  push Not at hs
  obtain ⟨t,ht⟩ := hs
  have par : ∃ T, ∀ n, T ≤ n → (u s n+u s (n+1))%2=0 := by
    by_cases h : ∃ j, t ≤ j ∧ u s j % 2=0
    · obtain ⟨j,hj,he⟩ := h
      have H (l : ℕ) : u s (j+l)%2=0 := by
        induction l with
        | zero => exact he
        | succ l ih =>
          change u s (j+l+1)%2=0
          have H := ht (j+l) (by omega) ih
          omega
      refine ⟨j, fun n hn => ?_⟩
      obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hn
      have h1 := H l
      have h2 : u s (j+l+1)%2=0 := H (l+1)
      omega
    · push Not at h
      exact ⟨t, fun n hn => by have h1 := h n hn; have h2 := h (n+1) (by omega); omega⟩
  obtain ⟨T,hT⟩ := par
  by_cases h : ∃ n, T ≤ n ∧ u s n = u s (n+1)
  · obtain ⟨n,_,he⟩ := h
    exact ⟨n, fixed s n he⟩
  · push Not at h
    let D (n : ℕ) := Nat.dist (u s n) (u s (n+1))
    have dec (n : ℕ) (hn : T ≤ n) : D (n+1) < D n := by
      dsimp only [D]
      rw [rec s n, OMA.S_oeis_a181717.next, if_pos (hT n hn)]
      have H := h n hn
      have hpar := hT n hn
      unfold Nat.dist
      omega
    have bound (j : ℕ) : D (T+j)+j ≤ D T := by
      induction j with
      | zero => simp
      | succ j ih =>
        change D (T+j+1)+(j+1) ≤ D T
        have H := dec (T+j) (by omega)
        omega
    have H := bound (D T+1)
    omega

/-- Every orbit with distinct initial values converges 3-adically to −1/5. -/
theorem centered_limit (s : ℕ × ℕ) (hs : s.1 ≠ s.2) (k : ℕ) :
    ∃ t, ∀ n, t ≤ n → 3^k ∣ 5*u s n+1 := by
  apply many s _ k
  by_contra h
  obtain ⟨t,ht⟩ := few s h
  have distinct (n : ℕ) : u s n ≠ u s (n+1) := by
    induction n with
    | zero => exact hs
    | succ n ih =>
      change u s (n+1) ≠ u s (n+2)
      rw [rec s n, OMA.S_oeis_a181717.next]
      split_ifs <;> omega
  exact distinct t (ht (t+1) (by omega)).symm

theorem stabilization (s : ℕ × ℕ) (k : ℕ) :
    ∃ t r, ∀ n, t ≤ n → u s n % 3^k = r := by
  classical
  by_cases he : s.1 = s.2
  · have H := fixed s 0 he
    exact ⟨0,u s 0 % 3^k,fun n hn => by rw [H n hn]⟩
  · obtain ⟨t,ht⟩ := centered_limit s he k
    refine ⟨t,u s t % 3^k,fun n hn => ?_⟩
    have h := (Nat.modEq_zero_iff_dvd.mpr (ht n hn)).trans
      (Nat.modEq_zero_iff_dvd.mpr (ht t le_rfl)).symm
    have hc : (3^k).Coprime 5 := (by decide : Nat.Coprime 3 5).pow_left k
    apply Nat.ModEq.cancel_left_of_coprime hc
    exact Nat.ModEq.add_right_cancel' 1 h

end FibonacciCollatz

theorem OMA.solution : type_of% @OMA.S_oeis_a181717.main := by
  intro k _
  obtain ⟨t,r,ht⟩ := FibonacciCollatz.stabilization (0,1) k
  refine ⟨t,r,fun n hn => ?_⟩
  cases n with
  | zero => omega
  | succ i => exact ht i (by omega)
