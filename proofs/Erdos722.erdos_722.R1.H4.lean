import OMAReductions.R_Erdos722_erdos_722_R1

/-!
Proof of `OMA.R_Erdos722_erdos_722_R1.H4`: a `1-(n, k, 1)` design exists whenever `k ∣ n`.

The divisibility hypothesis at `i = 0` says `k ∣ n`; write `n = k q`. The blocks
`B j = {j k, j k + 1, …, j k + k - 1}` for `j < q` all have `k` points, and a point `x` lies in
`B j` exactly when `j = x / k`, so every one-point set is in exactly one block.
-/

namespace OMAProof.Erdos722Partition

theorem bound {j q k t : ℕ} (hj : j < q) (ht : t < k) : j * k + t < q * k := by
  have h : (j + 1) * k ≤ q * k := Nat.mul_le_mul_right k hj
  rw [Nat.succ_mul] at h
  omega

/-- The `j`-th block `{j k, …, j k + k - 1}` inside `Fin (q * k)`. -/
def block (q k : ℕ) (j : Fin q) : Finset (Fin (q * k)) :=
  (Finset.univ : Finset (Fin k)).map
    ⟨fun t => ⟨j.val * k + t.val, bound j.2 t.2⟩, fun a b h => by
      simp only [Fin.mk.injEq] at h
      exact Fin.ext (by omega)⟩

theorem mem_block {q k : ℕ} (hk : 0 < k) (j : Fin q) (x : Fin (q * k)) :
    x ∈ block q k j ↔ j.val = x.val / k := by
  unfold block
  rw [Finset.mem_map]
  constructor
  · rintro ⟨t, -, ht⟩
    have hx : x.val = j.val * k + t.val := by rw [← ht]; rfl
    rw [hx]
    symm
    apply Nat.div_eq_of_lt_le
    · rw [mul_comm]; omega
    · have := t.2
      calc j.val * k + t.val < j.val * k + k := by omega
        _ = (j.val + 1) * k := by ring
  · intro hj
    refine ⟨⟨x.val % k, Nat.mod_lt _ hk⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    show j.val * k + x.val % k = x.val
    rw [hj]
    exact Nat.div_add_mod' x.val k

theorem card_block (q k : ℕ) (j : Fin q) : (block q k j).card = k := by
  simp [block]

end OMAProof.Erdos722Partition

open OMAProof.Erdos722Partition in
theorem OMA.solution : OMA.R_Erdos722_erdos_722_R1.H4 := by
  intro n k hk hkn hdiv
  have hkd : k ∣ n := by simpa using hdiv 0 (by norm_num)
  obtain ⟨q, rfl⟩ := hkd
  rw [mul_comm k q]
  refine ⟨Finset.univ.image (block q k), ?_, ?_⟩
  · intro e he
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp he
    exact card_block q k j
  · intro S hS
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hS
    have hxq : x.val / k < q := by
      rw [Nat.div_lt_iff_lt_mul hk]
      exact x.2
    refine ⟨block q k ⟨x.val / k, hxq⟩,
      ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
        Finset.singleton_subset_iff.mpr ((mem_block hk _ x).mpr rfl)⟩, ?_⟩
    rintro e ⟨he, hsub⟩
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp he
    have hj := (mem_block hk j x).mp (Finset.singleton_subset_iff.mp hsub)
    exact congrArg (block q k) (Fin.ext hj)
