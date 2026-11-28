import OMAStatements.S_oeis_a365383

namespace OMA.A365383Proof
open OMA.S_oeis_a365383

variable {n : ℕ}

theorem R0 (p : Nat.Partition n) : Represents p 0 := ⟨0, by simp, by simp⟩

theorem Radd {p : Nat.Partition n} {k : ℕ} (h : Represents p k) : Represents p (k + n) := by
  obtain ⟨xs, h1, h2⟩ := h
  refine ⟨xs + p.parts, fun x hx => ?_, by rw [Multiset.sum_add, h2, p.parts_sum]⟩
  rcases Multiset.mem_add.1 hx with hx | hx
  · exact h1 x hx
  · exact hx

theorem Rmul {p : Nat.Partition n} {k : ℕ} (h : Represents p k) (j : ℕ) : Represents p (k + n * j) := by
  induction j with
  | zero => simpa using h
  | succ j ih => rw [Nat.mul_succ, ← Nat.add_assoc]; exact Radd ih

theorem jump {p : Nat.Partition n} {a b : ℕ} (ha : Represents p (a + n)) (hb : ¬ Represents p b)
    (hab : a < b) (e : a % n = b % n) : False := by
  obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hab.le).1 e
  rcases c with _ | c
  · omega
  · rw [Nat.mul_succ] at hc
    apply hb
    have := Rmul ha c
    generalize n * c = m at *
    rwa [show b = a + n + m by omega]

theorem ev (p : Nat.Partition n) : ∃ K, ∀ k ≥ K, (Represents p (k + n) ↔ Represents p k) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, fun k _ => Iff.rfl⟩
  have hJ : {k | ¬ Represents p k ∧ Represents p (k + n)}.Finite := by
    refine Set.Finite.of_finite_image (f := (· % n)) ((Set.finite_Iio n).subset ?_) ?_
    · rintro _ ⟨k, -, rfl⟩; exact Nat.mod_lt _ hn
    · intro a ha b hb e
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact jump ha.2 hb.1 h e
      · exact jump hb.2 ha.1 h e.symm
  obtain ⟨M, hM⟩ := hJ.bddAbove
  refine ⟨M + 1, fun k hk => ⟨fun h => ?_, Radd⟩⟩
  by_contra h'
  have := hM ⟨h', h⟩
  omega

theorem part1 (n : ℕ) : ∃ K, ∀ k ≥ K, row n (k + n) = row n k := by
  classical
  choose K hK using @ev n
  refine ⟨Finset.univ.sup K, fun k hk => ?_⟩
  simp only [row]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hK p k (le_trans (Finset.le_sup (Finset.mem_univ p)) hk)

theorem Rdvd {k : ℕ} (hn : n ≠ 0) (h : Represents (Nat.Partition.indiscrete n) k) : n ∣ k := by
  obtain ⟨xs, h1, rfl⟩ := h
  refine Multiset.dvd_sum fun x hx => ?_
  have := h1 x hx
  rw [Nat.Partition.indiscrete_parts hn, Multiset.mem_singleton] at this
  rw [this]

theorem part2 (n t : ℕ) (hn : 0 < n) (h : ∃ K, ∀ k ≥ K, row n (k + t) = row n k) : n ∣ t := by
  classical
  obtain ⟨K, hK⟩ := h
  by_contra ht
  have e := hK (n * K) (Nat.le_mul_of_pos_left K hn)
  have h1 : row n (n * K) = (Finset.univ : Finset (Nat.Partition n)).card := by
    simp only [row]
    congr 1
    exact Finset.filter_true_of_mem fun p _ => by simpa using Rmul (R0 p) K
  have h2 : row n (n * K + t) < (Finset.univ : Finset (Nat.Partition n)).card := by
    simp only [row]
    refine Finset.card_lt_card (Finset.filter_ssubset.2 ⟨Nat.Partition.indiscrete n, Finset.mem_univ _, fun h => ht ?_⟩)
    exact (Nat.dvd_add_right (dvd_mul_right n K)).1 (Rdvd hn.ne' h)
  omega


end OMA.A365383Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a365383.main := ⟨OMA.A365383Proof.part1, OMA.A365383Proof.part2⟩
