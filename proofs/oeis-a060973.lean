import OMAStatements.S_oeis_a060973

/-!
The sequence increases by zero or one at each step. Composition and
subtraction from the index preserve this property. Each side of Bala's
identities also doubles when its argument is doubled beyond a fixed
threshold. These two facts determine the value at every odd index from
the two neighboring even indices.
-/

namespace NestedSequences

open OMA.S_oeis_a060973

private def Step (f : ℕ → ℕ) : Prop :=
  ∀ n, f n ≤ f (n + 1) ∧ f (n + 1) ≤ f n + 1

private theorem step_comp {f g : ℕ → ℕ} (hf : Step f) (hg : Step g) :
    Step (fun n => f (g n)) := by
  intro n
  have h := hg n
  rcases show g (n + 1) = g n ∨ g (n + 1) = g n + 1 by omega with h | h
  · simp [h]
  · simpa only [h] using hf (g n)

private theorem step_sub {g : ℕ → ℕ} (hg : Step g) : Step (fun n => n - g n) := by
  intro n
  have h := hg n
  dsimp
  omega

private theorem even_rule (n : ℕ) (hn : 2 ≤ n) : a (2 * n) = 2 * a n := by
  have h : 2 * n - 3 + 3 = 2 * n := by omega
  conv_lhs => rw [← h, a]
  rw [h, if_pos (by omega), show 2 * n / 2 = n by omega]

private theorem odd_rule (n : ℕ) : a (2 * n + 1) = a (n + 1) + a n := by
  cases n with
  | zero => norm_num [a]
  | succ k =>
    have h : 2 * k + 3 = 2 * (k + 1) + 1 := by omega
    conv_lhs => rw [← h, a]
    rw [if_neg (by omega), show (2 * k + 3) / 2 = k + 1 by omega]

private theorem step_a : Step a := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 4
    · interval_cases n <;> norm_num [a]
    · let k := n / 2
      have hk : 2 ≤ k := by dsimp [k]; omega
      have h := ih k (by dsimp [k]; omega)
      rcases show n = 2 * k ∨ n = 2 * k + 1 by dsimp [k]; omega with he | he
      · rw [he, even_rule k hk, odd_rule]
        omega
      · rw [he, odd_rule, show 2 * k + 1 + 1 = 2 * (k + 1) by omega,
            even_rule (k + 1) (by omega)]
        omega

private def nest (f g : ℕ → ℕ) (n : ℕ) : ℕ := f (n - g n)

private structure Layer (f g : ℕ → ℕ) : Prop where
  step : Step g
  doubles : ∀ n, 8 ≤ n → g (2 * n) = 2 * g n
  bound : ∀ n, g n ≤ f n

private theorem next_layer {f g : ℕ → ℕ} (hf : Step f)
    (hdouble : ∀ n, 4 ≤ n → f (2 * n) = 2 * f n) (hgap : 4 ≤ 8 - f 8)
    (hg : Layer f g) : Layer f (nest f g) := by
  refine ⟨step_comp (f := f) (g := fun n => n - g n) hf (step_sub hg.step), ?_, ?_⟩
  · intro n hn
    have hmono : Monotone (fun i => i - f i) :=
      monotone_nat_of_le_succ fun i => (step_sub hf i).1
    have hle : 8 - f 8 ≤ n - f n := hmono hn
    have hb := hg.bound n
    have hx : 4 ≤ n - g n := by omega
    simp only [nest, hg.doubles n hn, ← Nat.mul_sub, hdouble _ hx]
  · intro n
    exact (monotone_nat_of_le_succ fun i => (hf i).1) (Nat.sub_le n (g n))

private theorem odd_from_neighbors {f : ℕ → ℕ} (hf : Step f)
    (hd : ∀ n, 8 ≤ n → f (2 * n) = 2 * f n) (k : ℕ) (hk : 8 ≤ k) :
    f (2 * k + 1) = f k + f (k + 1) := by
  have h := hf k
  have h₀ := hf (2 * k)
  have h₁ := hf (2 * k + 1)
  rw [hd k hk] at h₀
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, hd (k + 1) (by omega)] at h₁
  omega

private theorem extend {f g h : ℕ → ℕ} (hg : Layer f g) (hh : Layer f h)
    (hbase : ∀ n < 18, g n = h n) (n : ℕ) : g n = h n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 18
    · exact hbase n hn
    · let k := n / 2
      have hk : 8 ≤ k := by dsimp [k]; omega
      have h₀ := ih k (by dsimp [k]; omega)
      have h₁ := ih (k + 1) (by dsimp [k]; omega)
      rcases show n = 2 * k ∨ n = 2 * k + 1 by dsimp [k]; omega with he | he
      · rw [he, hg.doubles k hk, hh.doubles k hk, h₀]
      · rw [he, odd_from_neighbors hg.step hg.doubles k hk,
            odd_from_neighbors hh.step hh.doubles k hk, h₀, h₁]

private theorem identity (f : ℕ → ℕ) (hf : Step f)
    (hd : ∀ n, 4 ≤ n → f (2 * n) = 2 * f n) (hgap : 4 ≤ 8 - f 8)
    (hbase : ∀ n < 18, nest f f n = nest f (nest f (nest f f)) n) (n : ℕ) :
    nest f f n = nest f (nest f (nest f f)) n := by
  have h₀ : Layer f f := ⟨hf, fun i hi => hd i (by omega), fun _ => le_rfl⟩
  have h₁ := next_layer hf hd hgap h₀
  have h₂ := next_layer hf hd hgap h₁
  exact extend h₁ (next_layer hf hd hgap h₂) hbase n

theorem identities : type_of% @OMA.S_oeis_a060973.main := by
  have db (n : ℕ) (hn : 4 ≤ n) : b (2 * n) = 2 * b n := by
    have hm : Monotone a := monotone_nat_of_le_succ fun i => (step_a i).1
    have hlo : 2 ≤ a n := le_trans (by norm_num [a] : 2 ≤ a 4) (hm hn)
    simp only [b, even_rule n (by omega), even_rule (a n) hlo]
  constructor
  · intro n _
    apply identity a step_a (fun i hi => even_rule i (by omega)) (by norm_num [a]) _ n
    intro i hi
    interval_cases i <;> norm_num [nest, a]
  · intro n _
    apply identity b (step_comp (f := a) (g := a) step_a step_a) db (by norm_num [b, a]) _ n
    intro i hi
    interval_cases i <;> norm_num [nest, b, a]

end NestedSequences

theorem OMA.solution : type_of% @OMA.S_oeis_a060973.main :=
  NestedSequences.identities
