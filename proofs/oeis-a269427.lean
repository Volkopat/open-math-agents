import OMAStatements.S_oeis_a269427

-- Problem: A269427: a(1) = 1, a(n) counts m < n for which n == a(m) (mod m).
-- Upstream: formal-conjectures statements/oeis-a269427.lean:0 (declaration OMA.S_oeis_a269427.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea (R. Israel, in the entry): take the first B+1 primes p_i; by the Chinese remainder
-- theorem some k has k == a(p_i) (mod p_i) for all i; then n = k + 2 * prod p_i exceeds every
-- p_i and has n == a(p_i) (mod p_i), so all p_i are counted in a(n), and a(n) >= B+1.
-- A solution of the recursion exists by well-founded recursion (WellFounded.fix).

namespace H15A269427

def F (n : ℕ) (g : ∀ m : ℕ, m < n → ℕ) : ℕ :=
  if n ≤ 1 then 1 else
    ((Finset.Ico 1 n).filter (fun m => n % m = (if h : m < n then g m h else 0) % m)).card

noncomputable def f : ℕ → ℕ := WellFounded.fix (C := fun _ => ℕ) wellFounded_lt F

theorem f_eq (n : ℕ) : f n = F n (fun m _ => f m) := by
  unfold f
  exact WellFounded.fix_eq _ _ _

theorem f_one : f 1 = 1 := by
  rw [f_eq]
  unfold F
  rw [if_pos (le_refl 1)]

theorem f_rec (n : ℕ) (hn : 2 ≤ n) :
    f n = ((Finset.Ico 1 n).filter (fun m => n % m = f m % m)).card := by
  rw [f_eq]
  unfold F
  rw [if_neg (show ¬ n ≤ 1 by omega)]
  congr 1
  apply Finset.filter_congr
  intro m hm
  rw [Finset.mem_Ico] at hm
  rw [dif_pos hm.2]

end H15A269427

open OMA.S_oeis_a269427 in
theorem OMA.solution : type_of% @OMA.S_oeis_a269427.main := by
  refine ⟨⟨H15A269427.f, ?_⟩, ?_⟩
  · unfold IsA269427
    exact ⟨H15A269427.f_one, H15A269427.f_rec⟩
  · intro a ha B
    unfold IsA269427 at ha
    obtain ⟨_, hrec⟩ := ha
    obtain ⟨s, hs_def⟩ : ∃ s : ℕ → ℕ, s = Nat.nth Nat.Prime := ⟨_, rfl⟩
    have hsprime : ∀ i, Nat.Prime (s i) := by
      intro i
      rw [hs_def]
      exact Nat.prime_nth_prime i
    have hsinj : Function.Injective s := by
      rw [hs_def]
      exact Nat.nth_injective Nat.infinite_setOfPred_prime
    have hs0 : ∀ i ∈ Finset.range (B + 1), s i ≠ 0 := fun i _ => (hsprime i).ne_zero
    have pp : Set.Pairwise (↑(Finset.range (B + 1)) : Set ℕ) (Function.onFun Nat.Coprime s) := by
      intro i _ j _ hij
      exact (Nat.coprime_primes (hsprime i) (hsprime j)).mpr (fun h => hij (hsinj h))
    obtain ⟨k, hk⟩ :=
      Nat.chineseRemainderOfFinset (fun i => a (s i)) s (Finset.range (B + 1)) hs0 pp
    obtain ⟨P, hP⟩ : ∃ P, P = ∏ i ∈ Finset.range (B + 1), s i := ⟨_, rfl⟩
    have hPpos : 0 < P := by
      rw [hP]
      exact Finset.prod_pos (fun i _ => (hsprime i).pos)
    have hsP : ∀ i ∈ Finset.range (B + 1), s i ∣ P := by
      intro i hi
      rw [hP]
      exact Finset.dvd_prod_of_mem s hi
    have hsn : ∀ i ∈ Finset.range (B + 1), s i < k + 2 * P := by
      intro i hi
      have h3 := Nat.le_of_dvd hPpos (hsP i hi)
      omega
    have hmod : ∀ i ∈ Finset.range (B + 1), (k + 2 * P) % s i = a (s i) % s i := by
      intro i hi
      obtain ⟨c, hc⟩ := hsP i hi
      have h1 : k % s i = a (s i) % s i := hk i hi
      rw [hc, show 2 * (s i * c) = s i * (2 * c) by ring, Nat.add_mul_mod_self_left]
      exact h1
    refine ⟨k + 2 * P, by omega, ?_⟩
    rw [hrec (k + 2 * P) (by omega)]
    have hsub : (Finset.range (B + 1)).image s ⊆
        (Finset.Ico 1 (k + 2 * P)).filter (fun m => (k + 2 * P) % m = a m % m) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [Finset.mem_filter, Finset.mem_Ico]
      have h2 := (hsprime i).two_le
      exact ⟨⟨by omega, hsn i hi⟩, hmod i hi⟩
    have hcard : ((Finset.range (B + 1)).image s).card = B + 1 := by
      rw [Finset.card_image_of_injective _ hsinj, Finset.card_range]
    have hle := Finset.card_le_card hsub
    have hlt : B < ((Finset.range (B + 1)).image s).card := by
      rw [hcard]
      omega
    exact lt_of_lt_of_le hlt hle
