import OMAStatements.S_mo_363564
import Mathlib

open Cardinal in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_363564.main) := fun h => by
  have := noMaxOrder (aleph0_lt_aleph_one).le
  have hh := h _ _ ℕ (fun i : (aleph 1).ord.ToType => Set.Iio i) (fun _ => Set.univ)
    (fun a b h x hx => hx.trans_le h) (fun _ _ _ => le_rfl)
    (fun i => by simpa using lt_aleph_one_iff.1 (mk_Iio_toType_ord_lt i))
  rw [Set.iUnion_Iio, mk_univ, mk_ord_toType] at hh
  exact (hh.trans ((mk_set_le _).trans mk_nat.le)).not_gt aleph0_lt_aleph_one
