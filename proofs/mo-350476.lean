import OMAStatements.S_mo_350476

/-!
David E. Speyer's counterexample at https://mathoverflow.net/a/350489
uses the order ideals of a poset consisting of an antichain underneath a chain.
Take an antichain of size three and a chain of size one. The order ideals
form a Boolean cube with one additional top element.
-/

open OMA.S_mo_350476

private abbrev CubeWithTop := WithTop (Bool × Bool × Bool)

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_350476.main) := by
  intro h
  have hcount : (joinIrreducibles CubeWithTop).card = 4 := by decide +kernel
  have hupper : upperSum CubeWithTop = 16 := by decide +kernel
  have hlower : lowerSum CubeWithTop = 20 := by decide +kernel
  have hstrict := h CubeWithTop
  rw [hupper, hlower, hcount] at hstrict
  exact (by decide : ¬ Nat.dist 16 20 < 4) hstrict

