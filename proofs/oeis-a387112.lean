import OMAStatements.S_oeis_a387112

-- Credit: @oh-meh
open OMA.S_oeis_a387112

theorem OMA.solution : type_of% @OMA.S_oeis_a387112.main := by
  intro n _
  constructor
  · rintro ⟨f, hf, hb⟩ i
    have hm : Monotone (primeIndex n) :=
      Nat.monotone_primeCounting.comp (Nat.primeFactorsList_sorted n).monotone_get
    -- The representatives of slots 0 through i lie among the first primeIndex n i integers.
    let g (j : Fin (i.val + 1)) : Fin (primeIndex n i) :=
      let k : Fin n.primeFactorsList.length := ⟨j, by have := j.isLt; have := i.isLt; omega⟩
      ⟨f k - 1, by
        have hk : k ≤ i := by change j.val ≤ i.val; omega
        have := (hb k).2.trans (hm hk)
        have := (hb k).1
        omega⟩
    have hg : Function.Injective g := by
      intro j l eq
      let k : Fin n.primeFactorsList.length := ⟨j, by have := j.isLt; have := i.isLt; omega⟩
      let t : Fin n.primeFactorsList.length := ⟨l, by have := l.isLt; have := i.isLt; omega⟩
      have h : f k - 1 = f t - 1 := congrArg Fin.val eq
      have hk := (hb k).1
      have ht := (hb t).1
      have heq : k = t := hf (by omega)
      exact Fin.ext (congrArg (fun z : Fin n.primeFactorsList.length => z.val) heq)
    simpa using Fintype.card_le_of_injective g hg
  · intro h
    refine ⟨fun i => i.val + 1, ?_, fun i => ⟨Nat.succ_le_succ (Nat.zero_le _), h i⟩⟩
    intro i j hij
    exact Fin.ext (Nat.add_right_cancel hij)
