import OMAStatements.S_oeis_a236539

/-! The source asks for uniqueness among all Fibonacci-sided integer-area triangles.
The triangle inequality forces equal sides. The case of two shorter equal sides is
Harborth and Kemnitz's first theorem (Fibonacci Triangles, 1990). For a shorter
base and two equal longer sides, the remaining hypothesis only needs to exclude
pairs not already ruled out by the powers of two in their indices. -/

namespace OMA.R_oeis_a236539_R1



/-- Three distinct positive Fibonacci lengths cannot form a nondegenerate triangle. -/
theorem fibonacci_triangle_isosceles (i j k : ℕ)
    (hij : Nat.fib i ≤ Nat.fib j) (hjk : Nat.fib j ≤ Nat.fib k)
    (ht : Nat.fib k < Nat.fib i + Nat.fib j) :
    Nat.fib i = Nat.fib j ∨ Nat.fib j = Nat.fib k := by
  by_contra! h
  have h₁ : i < j := lt_of_not_ge fun h' => h.1 (le_antisymm hij (Nat.fib_mono h'))
  have h₂ : j < k := lt_of_not_ge fun h' => h.2 (le_antisymm hjk (Nat.fib_mono h'))
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hsum : Nat.fib i + Nat.fib (j+1) ≤ Nat.fib (j+2) := by
    rw [Nat.fib_add_two]
    have := Nat.fib_mono (by omega : i ≤ j)
    omega
  exact (not_lt_of_ge (hsum.trans (Nat.fib_mono (by omega : j+2 ≤ k)))) ht




private theorem prime_three_factor : ∀ a : ℕ, a % 4 = 3 →
    ∃ p, p.Prime ∧ p % 4 = 3 ∧ p ∣ a := by
  apply Nat.recOnMul
  · norm_num
  · norm_num
  · exact fun p hp h => ⟨p,hp,h,dvd_rfl⟩
  · intro a b ha hb hh
    have h : a % 4 = 3 ∨ b % 4 = 3 := by
      rw [Nat.mul_mod] at hh
      have aa := Nat.mod_lt a (by decide : 0 < 4)
      have bb := Nat.mod_lt b (by decide : 0 < 4)
      interval_cases a % 4 <;> interval_cases b % 4 <;> norm_num at *
    rcases h with h | h
    · obtain ⟨p,hp,he,hd⟩ := ha h
      exact ⟨p,hp,he,dvd_mul_of_dvd_left hd _⟩
    · obtain ⟨p,hp,he,hd⟩ := hb h
      exact ⟨p,hp,he,dvd_mul_of_dvd_right hd _⟩

private theorem fib_mod_four_six (n : ℕ) :
    Nat.fib (n+6) % 4 = Nat.fib n % 4 := by
  have step (j : ℕ) : Nat.fib (j+6) = 5 * Nat.fib j + 8 * Nat.fib (j+1) := by
    rw [@Nat.fib_add_two (j+4), @Nat.fib_add_two (j+3), @Nat.fib_add_two (j+2),
        @Nat.fib_add_two (j+1), @Nat.fib_add_two j]
    omega
  rw [step]
  omega

private theorem fib_mod_four_reduce (n : ℕ) : Nat.fib n % 4 = Nat.fib (n%6) % 4 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 6
    · rw [Nat.mod_eq_of_lt hn]
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (by omega : 6 ≤ n)
      rw [Nat.add_comm 6 j, fib_mod_four_six, ih j (by omega)]
      congr 2
      omega

private theorem two_pow_mod_six (a : ℕ) :
    2^(a+1) % 6 = 2 ∨ 2^(a+1) % 6 = 4 := by
  induction a with
  | zero => decide
  | succ a ih => rw [pow_succ (2:ℕ) (a+1)]; omega

private theorem dyadic_prime (a : ℕ) (h : ℕ) (hh : h=2^(a+1)) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ p ∣ Nat.fib (2*h) ∧ ¬ p ∣ Nat.fib h := by
  let L := 2 * Nat.fib (h+1) - Nat.fib h
  have hn := Nat.fib_le_fib_succ (n:=h)
  have hu : L % 4 = 3 := by
    have ha := fib_mod_four_reduce h
    have hb := fib_mod_four_reduce (h+1)
    have hf := two_pow_mod_six a
    rw [← hh] at hf
    dsimp [L]
    rcases hf with he | he
    · rw [he] at ha
      rw [show (h+1)%6 = 3 by omega] at hb
      change Nat.fib h % 4 = 1 at ha
      change Nat.fib (h+1) % 4 = 2 at hb
      omega
    · rw [he] at ha
      rw [show (h+1)%6 = 5 by omega] at hb
      change Nat.fib h % 4 = 3 at ha
      change Nat.fib (h+1) % 4 = 1 at hb
      omega
  obtain ⟨p,hp,hp4,hd⟩ := prime_three_factor L hu
  refine ⟨p,hp,hp4,?_,?_⟩
  · rw [Nat.fib_two_mul]
    exact dvd_mul_of_dvd_right hd _
  · intro hd'
    have : p ∣ 2 * Nat.fib (h+1) := by
      have h := dvd_add hd hd'
      dsimp [L] at h
      rwa [Nat.sub_add_cancel (by omega)] at h
    rcases hp.dvd_mul.mp this with h2 | hs
    · have := Nat.le_of_dvd (by decide : 0<2) h2
      omega
    · have hdiv := Nat.dvd_gcd hd' hs
      rw [(Nat.fib_coprime_fib_succ h).gcd_eq_one] at hdiv
      exact hp.not_dvd_one hdiv

/-- A uniform obstruction for any mismatched pair of dyadic index valuations.
The index of the repeated length is divisible by `2^(s+2)`, and the base index is not. -/
theorem fibonacci_dyadic_obstruction (s m n A : ℕ)
    (hm : 2^(s+2) ∣ m) (hn : ¬ 2^(s+2) ∣ n)
    (area : 16*A^2 + Nat.fib n ^ 4 = 4 * Nat.fib n ^ 2 * Nat.fib m ^ 2) : False := by
  obtain ⟨p,hp,hp4,hpd,hpnd⟩ := dyadic_prime s _ rfl
  have hmul : 2*2^(s+1) = (2:ℕ)^(s+2) := by rw [pow_succ (2:ℕ) (s+1),Nat.mul_comm]
  rw [hmul] at hpd
  have hm' : p ∣ Nat.fib m := hpd.trans (Nat.fib_dvd _ _ hm)
  have hn' : ¬p ∣ Nat.fib n := by
    intro hd
    have h := Nat.dvd_gcd hpd hd
    rw [← Nat.fib_gcd] at h
    obtain ⟨j,hj,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_left (2^(s+2)) n)
    have hne : j ≠ s+2 := by
      intro hjj
      apply hn
      rw [hjj] at he
      have hdvd := Nat.gcd_dvd_right (2^(s+2)) n
      rwa [he] at hdvd
    rw [he] at h
    exact hpnd (h.trans (Nat.fib_dvd _ _ (pow_dvd_pow 2 (by omega : j ≤ s+1))))
  let : Fact p.Prime := ⟨hp⟩
  have hm0 : (Nat.fib m : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hm'
  have hn0 : (Nat.fib n : ZMod p) ≠ 0 := fun h => hn' ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have he : 16*(A : ZMod p)^2 + (Nat.fib n : ZMod p)^4 =
      4*(Nat.fib n : ZMod p)^2*(Nat.fib m : ZMod p)^2 := by
    simpa using congrArg (fun x : ℕ => (x : ZMod p)) area
  rw [hm0] at he
  have hsq : (4*(A : ZMod p))^2 = -((Nat.fib n : ZMod p)^2)^2 := by linear_combination he
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (pow_ne_zero _ hn0) hsq hp4


/-- The precise sorted-side Heron test used in OEIS A236539, with two longer sides equal. -/
theorem fibonacci_dyadic_heron (s m n A : ℕ)
    (hm : 2^(s+2) ∣ m) (hn : ¬2^(s+2) ∣ n) (hlen : Nat.fib n ≤ Nat.fib m) :
    16 * A^2 ≠ (Nat.fib n + Nat.fib m + Nat.fib m) *
      (Nat.fib n + Nat.fib m - Nat.fib m) * (Nat.fib n + Nat.fib m - Nat.fib m) *
      (Nat.fib m + Nat.fib m - Nat.fib n) := by
  intro h
  apply fibonacci_dyadic_obstruction s m n A hm hn
  simp only [Nat.add_sub_cancel] at h
  generalize hb : Nat.fib n = b at *
  generalize hu : Nat.fib m = u at *
  obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hlen
  rw [hv] at h ⊢
  rw [show b+v+(b+v)-b = b+v+v by omega] at h
  rw [h]
  ring


/-- Equal shorter sides, including the equilateral boundary. -/
def H1 : Prop := ∀ i k A : ℕ, 0 < Nat.fib i → Nat.fib i ≤ Nat.fib k →
  Nat.fib k < Nat.fib i + Nat.fib i → 0 < A →
  16*A^2 = (Nat.fib i+Nat.fib i+Nat.fib k) * (Nat.fib i+Nat.fib i-Nat.fib k) *
    (Nat.fib i+Nat.fib k-Nat.fib i) * (Nat.fib i+Nat.fib k-Nat.fib i) →
  Nat.fib i = 5 ∧ Nat.fib k = 8 ∧ A = 12

/-- Equal longer sides, restricted to the dyadically admissible indices. -/
def H2 : Prop := ∀ i j A : ℕ, 0 < Nat.fib i → Nat.fib i < Nat.fib j → 0 < A →
  (∀ s : ℕ, 2^(s+2) ∣ j → 2^(s+2) ∣ i) →
  16*A^2 ≠ (Nat.fib i+Nat.fib j+Nat.fib j) * (Nat.fib i+Nat.fib j-Nat.fib j) *
    (Nat.fib i+Nat.fib j-Nat.fib j) * (Nat.fib j+Nat.fib j-Nat.fib i)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a236539.main := by
  intro h₁ h₂ a b c A
  constructor
  · rintro ⟨ha, hab, hbc, ht, hA, ⟨i,rfl⟩, ⟨j,rfl⟩, ⟨k,rfl⟩, h⟩
    by_cases hi : Nat.fib i = Nat.fib j
    · rw [← hi] at hbc ht h ⊢
      obtain ⟨h5,h8,h12⟩ := h₁ i k A ha hbc ht hA h
      exact ⟨h5,h5,h8,h12⟩
    · have hj := (fibonacci_triangle_isosceles i j k hab hbc ht).resolve_left hi
      rw [← hj] at h
      exfalso
      apply h₂ i j A ha (lt_of_le_of_ne hab hi) hA _ h
      intro s hs
      by_contra hns
      exact fibonacci_dyadic_heron s j i A hs hns hab h
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    exact ⟨by decide,by decide,by decide,by decide,by decide,
      ⟨5,by decide⟩,⟨5,by decide⟩,⟨6,by decide⟩,by decide⟩

end OMA.R_oeis_a236539_R1
