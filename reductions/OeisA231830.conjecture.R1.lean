import FormalConjectures.OEIS.«231830»
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
For a prime divisor $p$, the sequence modulo $p$ cannot repeat before its
first zero. Distinct terms are coprime, so a repetition would shift that zero
to an earlier index. Hence a square divisor $p^2$ only needs to be tested
at indices at most $p$. Every prime divisor is 1 modulo 4.

The two hypotheses test the bounded modular recurrence for primes up to
1000 and for larger primes, respectively.
-/

namespace OMA.R_OeisA231830_conjecture_R1

open OeisA231830 (a)

private theorem a_pos (n : ℕ) : 0 < a n := by
  cases n with
  | zero => decide
  | succ n =>
    cases n with
    | zero => decide
    | succ n =>
      change 0 < (a (n + 1) - 1) * a (n + 1) ^ 2 + 1
      omega

private theorem predecessor_step (n : ℕ) :
    a (n + 2) - 1 = (a (n + 1) - 1) * ((a (n + 1) - 1) + 1) ^ 2 := by
  change ((a (n + 1) - 1) * a (n + 1) ^ 2 + 1) - 1 = _
  rw [Nat.add_sub_cancel, Nat.sub_add_cancel (a_pos (n + 1))]

private theorem orbit_modEq (m n : ℕ) :
    let orbit := Nat.rec (motive := fun _ => ℕ) (4 % m) (fun _ x => (x * (x + 1) ^ 2) % m)
    Nat.ModEq m (orbit n) (a (n + 1) - 1) := by
  dsimp only
  induction n with
  | zero =>
    change Nat.ModEq m (4 % m) 4
    exact Nat.mod_modEq _ _
  | succ n ih =>
    rw [predecessor_step]
    change Nat.ModEq m ((_ * (_ + 1) ^ 2) % m) _
    exact (Nat.mod_modEq _ _).trans (ih.mul ((ih.add_right 1).pow 2))

private theorem dvd_iff_orbit (m n : ℕ) :
    let orbit := Nat.rec (motive := fun _ => ℕ) (4 % m) (fun _ x => (x * (x + 1) ^ 2) % m)
    m ∣ a (n + 1) ↔ (orbit n + 1) % m = 0 := by
  dsimp only
  have he := (orbit_modEq m n).add_right 1
  rw [Nat.sub_add_cancel (a_pos (n + 1))] at he
  unfold Nat.ModEq at he
  rw [Nat.dvd_iff_mod_eq_zero, he]

private theorem coprime_of_lt {i j : ℕ} (hij : i < j) : (a i).Coprime (a j) := by
  have h : Nat.ModEq (a i) (a j) 1 := by
    induction j with
    | zero => omega
    | succ j ih =>
      cases j with
      | zero => have : i = 0 := by omega
                subst i
                exact Nat.modEq_one
      | succ j =>
        by_cases h : i = j + 1
        · subst i
          change Nat.ModEq (a (j + 1)) ((a (j + 1) - 1) * a (j + 1) ^ 2 + 1) 1
          have hzero : Nat.ModEq (a (j + 1)) (a (j + 1)) 0 := by simp [Nat.ModEq]
          simpa using ((Nat.ModEq.refl (a (j + 1) - 1)).mul (hzero.pow 2)).add_right 1
        · have hprev := ih (by omega)
          have hsub : Nat.ModEq (a i) (a (j + 1) - 1) 0 := by
            apply Nat.ModEq.add_right_cancel' 1
            rw [Nat.sub_add_cancel (a_pos (j + 1)), zero_add]
            exact hprev
          change Nat.ModEq (a i) ((a (j + 1) - 1) * a (j + 1) ^ 2 + 1) 1
          simpa using (hsub.mul (Nat.ModEq.refl (a (j + 1) ^ 2))).add_right 1
  exact (Nat.coprime_of_mul_modEq_one 1 (by simpa using h)).symm

private theorem term_eq_square_add_one (n : ℕ) : ∃ x : ℕ, a n = (2 * x) ^ 2 + 1 := by
  cases n with
  | zero => exact ⟨0, rfl⟩
  | succ n =>
    induction n with
    | zero => exact ⟨1, rfl⟩
    | succ n ih =>
      obtain ⟨x, hx⟩ := ih
      refine ⟨x * a (n + 1), ?_⟩
      change (a (n + 1) - 1) * a (n + 1) ^ 2 + 1 = _
      have hsub : a (n + 1) - 1 = (2 * x) ^ 2 := by rw [hx]; omega
      rw [hsub]
      ring

private theorem prime_divisor_mod_four {n p : ℕ} (hp : p.Prime) (hd : p ∣ a n) : p % 4 = 1 := by
  obtain ⟨x, hx⟩ := term_eq_square_add_one n
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hx, mul_pow] at hd
    omega
  let _ : Fact p.Prime := ⟨hp⟩
  have hz := (ZMod.natCast_eq_zero_iff (a n) p).mpr hd
  rw [hx] at hz
  push_cast at hz
  have hsq : (2 * (x : ZMod p)) ^ 2 = -1 := eq_neg_of_add_eq_zero_left hz
  have hne := ZMod.mod_four_ne_three_of_sq_eq_neg_one hsq
  have hodd := hp.odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hodd
  omega

private theorem orbit_add_eq (step : ℕ → ℕ) (seed i j d : ℕ) :
    let orbit := Nat.rec (motive := fun _ => ℕ) seed (fun _ x => step x)
    orbit i = orbit j → orbit (i + d) = orbit (j + d) := by
  dsimp only
  intro h
  induction d with
  | zero => simpa using h
  | succ d ih => exact congrArg step ih

private theorem index_le_prime_of_dvd {p n : ℕ} (hp : p.Prime) (hd : p ∣ a n) : n ≤ p := by
  cases n with
  | zero => omega
  | succ n =>
    let step := fun x : ℕ => (x * (x + 1) ^ 2) % p
    let orbit := Nat.rec (motive := fun _ => ℕ) (4 % p) (fun _ x => step x)
    have orbit_lt (j : ℕ) : orbit j < p := by
      cases j <;> exact Nat.mod_lt _ hp.pos
    let f (i : Fin (n + 1)) : Fin p := ⟨orbit i.val, orbit_lt i.val⟩
    have distinct {i j : Fin (n + 1)} (hlt : i.val < j.val) (heq : f i = f j) : False := by
      have he := orbit_add_eq step (4 % p) i.val j.val (n - j.val) (congrArg Fin.val heq)
      change orbit (i.val + (n - j.val)) = orbit (j.val + (n - j.val)) at he
      have hj : j.val + (n - j.val) = n := by omega
      rw [hj] at he
      have hi : p ∣ a (i.val + (n - j.val) + 1) := by
        apply (dvd_iff_orbit p _).mpr
        change (orbit (i.val + (n - j.val)) + 1) % p = 0
        rw [he]
        exact (dvd_iff_orbit p n).mp hd
      have hcop := coprime_of_lt (i := i.val + (n - j.val) + 1) (j := n + 1) (by omega)
      exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hi hd) hcop
    have hinj : Function.Injective f := by
      intro i j he
      apply Fin.ext
      rcases lt_trichotomy i.val j.val with h | h | h
      · exact (distinct h he).elim
      · exact h
      · exact (distinct h he.symm).elim
    simpa using Fintype.card_le_of_injective f hinj

/-- The finite modular check for small primes. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 → p ≤ 1000 → ∀ n < p,
    let m := p ^ 2
    let x := Nat.rec (motive := fun _ => ℕ) (4 % m) (fun _ x => (x * (x + 1) ^ 2) % m) n
    (x + 1) % m ≠ 0

/-- The same modular check for the remaining primes. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 → 1000 < p → ∀ n < p,
    let m := p ^ 2
    let x := Nat.rec (motive := fun _ => ℕ) (4 % m) (fun _ x => (x * (x + 1) ^ 2) % m) n
    (x + 1) % m ≠ 0

theorem main : H1 → H2 → type_of% @OeisA231830.conjecture := by
  intro h1 h2 n
  cases n with
  | zero => exact squarefree_one
  | succ n =>
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hd
    have hd' : p ^ 2 ∣ a (n + 1) := by simpa [pow_two] using hd
    have hdiv : p ∣ a (n + 1) := (dvd_mul_right p p).trans hd
    have hc := prime_divisor_mod_four hp hdiv
    have hn : n < p := index_le_prime_of_dvd hp hdiv
    have hz := (dvd_iff_orbit (p ^ 2) n).mp hd'
    by_cases hs : p ≤ 1000
    · exact h1 p hp hc hs n hn hz
    · exact h2 p hp hc (Nat.lt_of_not_ge hs) n hn hz

end OMA.R_OeisA231830_conjecture_R1
