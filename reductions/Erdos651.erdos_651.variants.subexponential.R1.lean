import FormalConjectures.ErdosProblems.«651»

/-!
The bound (1 + c)^n in every dimension k ≥ 3 is derived from two published facts:
the Pohoata-Zakharov theorem in dimension three, f_3(n) ≤ 2^(εn) for every ε > 0
and all large n (arXiv:2208.04878, Theorem 1.1), and Valtr's projection inequality
f_(k+1)(n) ≤ f_k(n). The derivation takes ε = log_2 (1 + c).
-/
open Filter

namespace OMA.R_Erdos651_erdos_651_variants_subexponential_R1

def H1 : Prop := ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
  (Erdos651.f 3 n : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ))

def H2 : Prop := ∀ k n : ℕ, 3 ≤ k → Erdos651.f (k + 1) n ≤ Erdos651.f k n

theorem main : H1 → H2 → type_of% @Erdos651.erdos_651.variants.subexponential := by
  intro h1 h2 k hk c hc
  have hmono : ∀ n : ℕ, Erdos651.f k n ≤ Erdos651.f 3 n := by
    intro n
    induction k, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ d hd ih => exact (h2 d n hd).trans ih
  have hε : 0 < Real.logb 2 (1 + c) := Real.logb_pos (by norm_num) (by linarith)
  filter_upwards [h1 _ hε] with n hn
  calc (Erdos651.f k n : ℝ) ≤ (Erdos651.f 3 n : ℝ) := by exact_mod_cast hmono n
    _ ≤ (2 : ℝ) ^ (Real.logb 2 (1 + c) * (n : ℝ)) := hn
    _ = (1 + c) ^ n := by
      rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by linarith),
        Real.rpow_natCast]

end OMA.R_Erdos651_erdos_651_variants_subexponential_R1
