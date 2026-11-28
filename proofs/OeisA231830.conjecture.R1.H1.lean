import OMAReductions.R_OeisA231830_conjecture_R1

-- Step OeisA231830.conjecture.R1.H1: hypothesis H1 of reduction OeisA231830.conjecture.R1
-- Credit: @Raimo33

namespace RaimoA231830

def f (m x : ℕ) : ℕ := (x * (x + 1) ^ 2) % m

def go (m : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | x, k + 1 => ((x + 1) % m != 0) && go m (f m x) k

lemma go_spec (m : ℕ) : ∀ k x, go m x k = true → ∀ n < k, ((f m)^[n] x + 1) % m ≠ 0 := by
  intro k
  induction k with
  | zero => intro x _ n hn; omega
  | succ k ih =>
    intro x hx n hn
    simp only [go, Bool.and_eq_true, bne_iff_ne, ne_eq] at hx
    cases n with
    | zero => simpa using hx.1
    | succ n =>
      rw [Function.iterate_succ_apply]
      exact ih _ hx.2 n (by omega)

lemma rec_eq (m n : ℕ) : Nat.rec (motive := fun _ => ℕ) (4 % m)
    (fun _ x => (x * (x + 1) ^ 2) % m) n = (f m)^[n] (4 % m) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih]; rfl

def allOK : ℕ → Bool
  | 0 => true
  | p + 1 => (if (p + 1) % 4 = 1 ∧ 2 ≤ p + 1 then go ((p + 1) ^ 2) (4 % (p + 1) ^ 2) (p + 1)
      else true) && allOK p

lemma allOK_spec : ∀ N, allOK N = true → ∀ p, p ≤ N → p % 4 = 1 → 2 ≤ p →
    go (p ^ 2) (4 % p ^ 2) p = true := by
  intro N
  induction N with
  | zero => intro _ p hp _ h2; omega
  | succ N ih =>
    intro h p hp h4 h2
    simp only [allOK, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge p (N + 1) with hlt | hge
    · exact ih h.2 p (by omega) h4 h2
    · have : p = N + 1 := by omega
      subst this
      have h1 := h.1
      rw [if_pos ⟨h4, h2⟩] at h1
      exact h1

lemma allOK1000 : allOK 1000 = true := by decide +kernel

end RaimoA231830

theorem OMA.solution : OMA.R_OeisA231830_conjecture_R1.H1 := by
  intro p hp h4 hle n hn
  dsimp only
  rw [RaimoA231830.rec_eq]
  exact RaimoA231830.go_spec _ p _
    (RaimoA231830.allOK_spec 1000 RaimoA231830.allOK1000 p hle h4 hp.two_le) n hn
