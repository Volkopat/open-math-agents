import OMAStatements.S_oeis_a307792

/-!
OEIS A307792 asks when the product of the decimal digits of T(n) equals n.
All such n are 7-smooth. When 5 divides n, the factor 2 occurs at most once:
if 20 divides n, the positive triangular number T(n) ends in zero.
This leaves two families with three independent unbounded exponents each.
Credit: @jiyongparkphysics
-/
namespace OMA.R_oeis_a307792_R1

/-- Exclude the nontrivial indices whose prime factors lie in {2, 3, 7}. -/
def H1 : Prop :=
  ∀ u v w : ℕ, let n := 2^u * 3^v * 7^w
    (Nat.digits 10 (n*(n+1)/2)).prod = n → n = 1

/-- The factor 5 occurs, and the 2-adic valuation is either zero or one. -/
def H2 : Prop :=
  ∀ (i : Fin 2) (u v w : ℕ), let n := 2^i.val * 3^u * 5^(v+1) * 7^w
    (Nat.digits 10 (n*(n+1)/2)).prod = n → n = 5

lemma digit_product_factors (l : List ℕ) (small : ∀ t ∈ l, t < 10)
    (nonzero : l.prod ≠ 0) :
    ∃ a b c d : ℕ, l.prod = 2^a * 3^b * 5^c * 7^d := by
  induction l with
  | nil => exact ⟨0,0,0,0,by simp⟩
  | cons x xs ih =>
    have hx : x < 10 := small x (by simp)
    have hn : x ≠ 0 := by intro h; simp [h] at nonzero
    have ht : xs.prod ≠ 0 := by intro h; simp [h] at nonzero
    have digits : ∀ j : Fin 10, j.val ≠ 0 →
        ∃ a b c d : Fin 4, j.val = 2^a.val*3^b.val*5^c.val*7^d.val := by decide
    obtain ⟨a,b,c,d,hx'⟩ := digits ⟨x,hx⟩ hn
    obtain ⟨i,j,k,m,hm⟩ := ih (fun t h => small t (by simp [h])) ht
    refine ⟨a.val+i,b.val+j,c.val+k,d.val+m,?_⟩
    change x = _ at hx'
    rw [List.prod_cons, hx', hm]
    simp only [pow_add]
    ring

lemma trailing_zero {n : ℕ} (hpos : 0 < n) (h : 20 ∣ n) :
    (Nat.digits 10 (n*(n+1)/2)).prod = 0 := by
  obtain ⟨j, rfl⟩ := h
  have hj : 0 < j := by omega
  have t : 20*j*(20*j+1)/2 = 10*(j*(20*j+1)) := by
    rw [show 20*j*(20*j+1) = (10*(j*(20*j+1)))*2 by ring]
    simp
  rw [t, Nat.digits_def' (by decide : 1 < 10) (show 0 < 10*(j*(20*j+1)) by positivity)]
  simp

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a307792.main := by
  intro h1 h2 n hn
  constructor
  · intro h
    have hz : (Nat.digits 10 (n*(n+1)/2)).prod ≠ 0 := by omega
    obtain ⟨a,b,c,d,he⟩ := digit_product_factors _ (fun _ hx =>
      Nat.digits_lt_base (by decide : 1 < 10) hx) hz
    rw [h] at he
    cases c with
    | zero =>
      simp only [pow_zero, mul_one] at he
      subst n
      exact Or.inl (h1 a b d h)
    | succ c =>
      have small : a < 2 := by
        by_contra! ha
        obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le ha
        have dvd20 : 20 ∣ n := by
          refine ⟨2^j*3^b*5^c*7^d,?_⟩
          rw [he, pow_add, pow_succ (5:ℕ) c]
          ring
        exact hz (trailing_zero hn dvd20)
      exact Or.inr (he.trans (h2 ⟨a,small⟩ b c d (he ▸ h)))
  · rintro (rfl | rfl) <;> decide

end OMA.R_oeis_a307792_R1
