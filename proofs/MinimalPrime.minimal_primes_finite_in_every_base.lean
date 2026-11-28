import FormalConjectures.Wikipedia.MinimalPrime

/-!
Higman's lemma applied to the digit lists of an infinite sequence of
distinct minimal primes. Each prime in the sequence certifies the base
condition. The original proof was submitted by @harshshah1618.
-/

theorem OMA.solution : type_of% @MinimalPrime.minimal_primes_finite_in_every_base := by
  intro b
  by_contra infinite
  let e := Set.Infinite.natEmbedding _ infinite
  have higman := (Finset.range b).partiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ Eq
  obtain ⟨i, j, ij, sublist⟩ := higman.exists_lt (f := fun i => Nat.digits b (e i))
    (fun i d hd => Finset.mem_range.mpr (Nat.digits_lt_base (e i).2.1 hd))
  simp only [List.sublistForall₂_iff, List.forall₂_eq_eq_eq, exists_eq_left'] at sublist
  exact (e j).2.2.2 ⟨e i, (e i).2.2.1,
    fun eq => ij.ne (e.injective (Subtype.ext eq)), sublist⟩
