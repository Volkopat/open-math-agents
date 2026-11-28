import OMAStatements.S_oeis_a066223

open OMA.S_oeis_a066223 in
theorem OMA.solution : type_of% @OMA.S_oeis_a066223.main := by
  rintro (_ | _ | m) hn
  · omega
  · omega
  rw [show m + 1 + 1 - 2 = m by omega, a, a, a,
    show 2 * (m + 1 + 1) = 2 * m + 2 + 2 by ring, show 2 * (m + 1 + 1 - 1) = 2 * m + 2 by omega, t, t, t]
  push_cast
  ring
