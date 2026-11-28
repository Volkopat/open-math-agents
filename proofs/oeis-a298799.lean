import OMAStatements.S_oeis_a298799

open OMA.S_oeis_a298799

set_option maxRecDepth 60000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a298799.main) := by
  intro h
  have hex : ¬ excluded 19 362 := by
    rintro ⟨m, k, hm, _, hk, hn⟩
    norm_num at hm hk
    omega
  have hc := h 19 362 (by decide) (by decide) (by decide) hex
  change a 6878 % 361 = a 362 % 361 at hc
  have h6878 : a 6878 % 361 = 218 := by decide +kernel
  have h362 : a 362 % 361 = 294 := by decide +kernel
  omega
