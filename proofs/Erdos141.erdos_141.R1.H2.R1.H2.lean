import OMAReductions.R_Erdos141_erdos_141_R1_H2_R1

/-!
Proof of `OMA.R_Erdos141_erdos_141_R1_H2_R1.H2`.
Take `s = {p + n * d | n < k}`. It is an arithmetic progression of length `k` since
`n ↦ p + n * d` is injective for `d > 0`. With `a` the number of primes below `p`, induction on
`n` shows that exactly `a + n` primes lie below `p + n * d`: each window
`[p + n * d, p + (n + 1) * d)` contains the single prime `p + n * d`. Hence
`Nat.nth Nat.Prime (a + n) = p + n * d`, so `s` also consists of `k` consecutive primes.
-/

namespace OMAProof.Erdos141ConsecutiveAP

open Erdos141

theorem count_step {p d k : ℕ} (hd : 0 < d)
    (hp : ∀ n < k, (p + n * d).Prime)
    (hg : ∀ n, n + 1 < k → ∀ m, p + n * d < m → m < p + (n + 1) * d → ¬ m.Prime) :
    ∀ n < k, Nat.count Nat.Prime (p + n * d) = Nat.count Nat.Prime p + n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have heq : p + (n + 1) * d = (p + n * d) + d := by ring
    rw [heq, Nat.count_add, h1,
      Nat.count_eq_card_filter_range (fun j => Nat.Prime (p + n * d + j)) d]
    have hfil : (Finset.range d).filter (fun j => Nat.Prime (p + n * d + j)) = {0} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hj, hpr⟩
        by_contra h0
        exact hg n hn (p + n * d + j) (by omega) (by rw [heq]; omega) hpr
      · rintro rfl
        exact ⟨hd, by simpa using hp n (by omega)⟩
    rw [hfil, Finset.card_singleton]
    ring

theorem consecutive_ap {p d k : ℕ} (hd : 0 < d)
    (hp : ∀ n < k, (p + n * d).Prime)
    (hg : ∀ n, n + 1 < k → ∀ m, p + n * d < m → m < p + (n + 1) * d → ¬ m.Prime) :
    ∃ s : Set ℕ, s.IsAPAndPrimeProgressionOfLength k := by
  classical
  let s : Set ℕ := {x | ∃ (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞)), p + n • d = x}
  have hs : s = ↑((Finset.range k).image (fun n => p + n * d)) := by
    ext x
    simp only [s, Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_range, Set.mem_image,
      Set.mem_Iio, smul_eq_mul, Nat.cast_lt, exists_prop]
  have hinj : Function.Injective (fun n : ℕ => p + n * d) := by
    intro a b hab
    simp only at hab
    exact Nat.eq_of_mul_eq_mul_right hd (by omega)
  have hcard : ENat.card s = k := by
    rw [hs, ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _ hinj, Finset.card_range]
  refine ⟨s, ⟨p, d, hcard, rfl⟩, Nat.count Nat.Prime p, hcard, ?_⟩
  have hnth : ∀ n < k, Nat.nth Nat.Prime (Nat.count Nat.Prime p + n) = p + n * d := by
    intro n hn
    rw [← count_step hd hp hg n hn]
    exact Nat.nth_count (hp n hn)
  ext x
  simp only [s, Set.mem_ofPred_eq, smul_eq_mul, Nat.cast_lt, exists_prop]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, hnth n hn⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (hnth n hn).symm⟩

end OMAProof.Erdos141ConsecutiveAP

open OMAProof.Erdos141ConsecutiveAP in
theorem OMA.solution : OMA.R_Erdos141_erdos_141_R1_H2_R1.H2 :=
  fun hd hp hg => consecutive_ap hd hp hg
