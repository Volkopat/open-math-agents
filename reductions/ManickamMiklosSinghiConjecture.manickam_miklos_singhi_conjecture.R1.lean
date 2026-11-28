import FormalConjectures.Paper.ManickamMiklosSinghiConjecture
import Mathlib.Tactic

/-! # The Manickam–Miklós–Singhi conjecture: reduction to the open core

Cyclic averaging (Katona style) proves, for every 1 ≤ k ≤ n, that
gcd(n,k) * C(n,k) ≤ n * N, where N counts nonnegative k-sets.
When k divides n this is the classical case of Manickam–Miklós (1988)
and Manickam–Singhi (1988). Chowdhury–Sarkis–Shahriari (2014) settle
n ≥ 8k^2. The open core is 4k ≤ n < 8k^2 with k not dividing n. -/

namespace OMA.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_R1

open Finset ManickamMiklosSinghiConjecture

-- The quadratic range of Chowdhury, Sarkis and Shahriari.
def H1 : Prop := ∀ (n k : ℕ), 1 ≤ k → 8*k^2 ≤ n → ∀ x : Fin n → ℝ,
    ∑ v, x v = 0 → (n-1).choose (k-1) ≤ nonnegSubsetCount n k x

-- The open core: below the quadratic range and k not dividing n.
def H2 : Prop := ∀ (n k : ℕ), 2 ≤ k → 4*k ≤ n → n < 8*k^2 → ¬ k ∣ n →
    ∀ x : Fin n → ℝ, ∑ v, x v = 0 → (n-1).choose (k-1) ≤ nonnegSubsetCount n k x

-- Averaging over permutations transfers the edge frequency to all k-sets.
lemma average {n k : ℕ} {ι : Type} [Fintype ι] [Nonempty ι]
    (E : ι → Finset (Fin n)) (hE : ∀ a, (E a).card = k)
    (x : Fin n → ℝ) (d : ℕ)
    (lower : ∀ σ : Equiv.Perm (Fin n),
      d ≤ (univ.filter (fun a : ι => 0 ≤ ∑ v ∈ E a, x (σ v))).card) :
    d * n.choose k ≤ Fintype.card ι * nonnegSubsetCount n k x := by
  classical
  let U := (univ : Finset (Fin n)).powersetCard k
  let good (s : Finset (Fin n)) : ℕ := if 0 ≤ ∑ v ∈ s, x v then 1 else 0
  let mass (s : Finset (Fin n)) := ∑ σ : Equiv.Perm (Fin n), good (s.map σ.toEmbedding)
  let a₀ : ι := Classical.choice ‹Nonempty ι›
  let M := mass (E a₀)
  have same (s : Finset (Fin n)) (hs : s.card = k) : mass s = M := by
    obtain ⟨p, hp⟩ := Equiv.Perm.exists_map_finset_eq (E a₀) s ((hE a₀).trans hs.symm)
    rw [← hp]
    calc
      mass ((E a₀).map p.toEmbedding) =
          ∑ σ : Equiv.Perm (Fin n), good ((E a₀).map ((σ * p).toEmbedding)) := by
            apply sum_congr rfl
            intro σ _
            rw [map_map]
            rfl
      _ = M := Equiv.sum_comp (Equiv.mulRight p) (fun σ : Equiv.Perm (Fin n) => good ((E a₀).map σ.toEmbedding))
  have total (σ : Equiv.Perm (Fin n)) :
      ∑ s ∈ U, good (s.map σ.toEmbedding) = nonnegSubsetCount n k x := by
    have permutes : U.map (mapEmbedding σ.toEmbedding).toEmbedding = U := by
      dsimp [U]
      rw [← powersetCard_map]
      simp
    calc
      _ = ∑ s ∈ U.map (mapEmbedding σ.toEmbedding).toEmbedding, good s := (sum_map ..).symm
      _ = _ := by rw [permutes]; simp [U, good, nonnegSubsetCount]
  let N := Fintype.card (Equiv.Perm (Fin n))
  have complete : U.card * M = N * nonnegSubsetCount n k x := by
    calc
      U.card * M = ∑ s ∈ U, mass s := by
        rw [sum_congr rfl (fun s h => same s (mem_powersetCard.mp h).2)]
        exact (sum_const_nat (fun _ _ => rfl)).symm
      _ = ∑ σ : Equiv.Perm (Fin n), ∑ s ∈ U, good (s.map σ.toEmbedding) := sum_comm
      _ = _ := by simp [total, N]
  have sparse : N*d ≤ Fintype.card ι * M := by
    calc
      N*d = ∑ _σ : Equiv.Perm (Fin n), d := by simp [N]
      _ ≤ ∑ σ : Equiv.Perm (Fin n), ∑ a : ι, good ((E a).map σ.toEmbedding) := by
        apply sum_le_sum
        intro σ _
        simpa [good, sum_map] using lower σ
      _ = ∑ a : ι, mass (E a) := sum_comm
      _ = _ := by simp [same _ (hE _)]
  have cU : U.card = n.choose k := by simp [U]
  have h := Nat.mul_le_mul_right U.card sparse
  rw [Nat.mul_assoc (Fintype.card ι), Nat.mul_comm M U.card, complete] at h
  apply Nat.le_of_mul_le_mul_left (c := N)
  · simpa only [cU, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  · exact Fintype.card_pos

-- Sums of an n-periodic function over c full periods.
lemma sum_range_mul_periodic {n : ℕ} (f : ℕ → ℝ) (hf : ∀ u, f (u + n) = f u) (c : ℕ) :
    ∑ u ∈ range (c * n), f u = c * ∑ u ∈ range n, f u := by
  have per : ∀ c u, f (c * n + u) = f u := by
    intro c
    induction c with
    | zero => intro u; simp
    | succ c ih =>
      intro u
      rw [Nat.succ_mul, show c * n + n + u = (c * n + u) + n by ring, hf, ih]
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Nat.succ_mul, sum_range_add, ih]
    simp only [per]
    push_cast
    ring

-- Cyclic averaging: the n/g blocks {mk, ..., mk+k-1} mod n cover Fin n
-- exactly k/g times, so under every relabelling one block is nonnegative.
theorem cyclic_bound (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (x : Fin n → ℝ)
    (hx : ∑ i, x i = 0) :
    n.choose k ≤ (n / Nat.gcd n k) * nonnegSubsetCount n k x := by
  classical
  have hn : 0 < n := by omega
  obtain ⟨a, ha⟩ := Nat.gcd_dvd_left n k
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_right n k
  have hg : 0 < Nat.gcd n k := Nat.gcd_pos_of_pos_left _ hn
  generalize hgdef : Nat.gcd n k = g at *
  have hqa : n / g = a := by
    rw [ha]
    exact Nat.mul_div_cancel_left a hg
  have hqk : (n / g) * k = b * n := by
    rw [hqa]
    rw [ha, hb]
    ring
  have hq : 0 < n / g := by
    rw [hqa]
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h] at ha
      omega
    · exact h
  set q := n / g with hqdef
  let e : Fin q → Fin k → Fin n := fun m t => ⟨(m.val*k + t.val) % n, Nat.mod_lt _ hn⟩
  have inj (m : Fin q) : Function.Injective (e m) := by
    intro s t h
    have h1 : (m.val*k + s.val) % n = (m.val*k + t.val) % n := congrArg Fin.val h
    have h2 : s.val % n = t.val % n := Nat.ModEq.add_left_cancel' _ h1
    have := s.isLt
    have := t.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
    exact Fin.ext h2
  let E : Fin q → Finset (Fin n) := fun m => univ.image (e m)
  have cardE (m : Fin q) : (E m).card = k := by
    simp [E, card_image_of_injective _ (inj m)]
  have lower (σ : Equiv.Perm (Fin n)) :
      1 ≤ (univ.filter (fun m : Fin q => 0 ≤ ∑ v ∈ E m, x (σ v))).card := by
    have hy : ∑ v, x (σ v) = 0 := (Equiv.sum_comp σ x).trans hx
    let f : ℕ → ℝ := fun u => x (σ ⟨u % n, Nat.mod_lt _ hn⟩)
    have hf : ∀ u, f (u + n) = f u := by
      intro u
      simp [f, Nat.add_mod_right]
    have hfi : ∀ i : Fin n, f i = x (σ i) := by
      intro i
      simp [f, Nat.mod_eq_of_lt i.isLt]
    have tot : ∑ m : Fin q, ∑ v ∈ E m, x (σ v) = 0 := by
      calc ∑ m : Fin q, ∑ v ∈ E m, x (σ v)
          = ∑ m : Fin q, ∑ t : Fin k, f (m.val*k + t.val) := by
            apply sum_congr rfl
            intro m _
            rw [sum_image (fun a _ b _ h => inj m h)]
        _ = ∑ u ∈ range (q*k), f u := by
            rw [Finset.sum_range (fun u => f u), ← Equiv.sum_comp finProdFinEquiv,
              Fintype.sum_prod_type]
            apply sum_congr rfl
            intro m _
            apply sum_congr rfl
            intro t _
            rw [finProdFinEquiv_apply_val]
            congr 1
            ring
        _ = (b : ℝ) * ∑ u ∈ range n, f u := by
            rw [hqk]
            exact sum_range_mul_periodic f hf b
        _ = 0 := by
            rw [Finset.sum_range (fun u => f u)]
            simp [hfi, hy]
    by_contra hcon
    rw [not_le, Nat.lt_one_iff, card_eq_zero, filter_eq_empty_iff] at hcon
    have hall : ∀ m ∈ (univ : Finset (Fin q)), ∑ v ∈ E m, x (σ v) < 0 := by
      intro m hm
      simpa using hcon hm
    have hne : (univ : Finset (Fin q)).Nonempty := ⟨⟨0, hq⟩, mem_univ _⟩
    have := sum_neg hall hne
    linarith
  have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have avg := average E cardE x 1 lower
  simpa using avg

-- The classical divisible case.
theorem dvd_case (n k : ℕ) (hk : 1 ≤ k) (hdvd : k ∣ n) (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∑ i, x i = 0) : (n-1).choose (k-1) ≤ nonnegSubsetCount n k x := by
  have hkn : k ≤ n := Nat.le_of_dvd hn hdvd
  have hb := cyclic_bound n k hk hkn x hx
  rw [Nat.gcd_eq_right hdvd] at hb
  have bin : n * (n-1).choose (k-1) = n.choose k * k := by
    obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    exact Nat.add_one_mul_choose_eq n' k'
  obtain ⟨q, rfl⟩ := hdvd
  rw [Nat.mul_div_cancel_left q (by omega)] at hb
  have hq : 0 < q := Nat.pos_of_mul_pos_left hn
  have key : q * (k*q-1).choose (k-1) = (k*q).choose k := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < k by omega)
    calc q * (k*q-1).choose (k-1) * k = k*q * (k*q-1).choose (k-1) := by ring
      _ = _ := bin
  apply Nat.le_of_mul_le_mul_left (c := q) _ hq
  rw [key]
  exact hb

theorem main : H1 → H2 → type_of% @ManickamMiklosSinghiConjecture.manickam_miklos_singhi_conjecture := by
  intro quadratic core n k hk hn x hx
  by_cases large : 8*k^2 ≤ n
  · exact quadratic n k hk large x hx
  by_cases hd : k ∣ n
  · exact dvd_case n k hk hd (by omega) x hx
  have two : 2 ≤ k := by
    by_contra h
    exact hd (by rw [show k = 1 by omega]; exact one_dvd n)
  exact core n k two hn (by omega) hd x hx

end OMA.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_R1
