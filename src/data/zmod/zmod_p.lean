/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johan Commelin
-/

import data.zmod.basic

namespace zmod

variables (p : ℕ) [fact p.prime]

-- move this
instance prime.fact_one_lt : fact (1 < p) := nat.prime.one_lt ‹p.prime›

private lemma mul_inv_cancel_aux (a : zmod p) (h : a ≠ 0) : a * a⁻¹ = 1 :=
begin
  obtain ⟨k, rfl⟩ := nat_cast_surjective a,
  apply coe_mul_inv_eq_one,
  apply nat.coprime.symm,
  rwa [nat.prime.coprime_iff_not_dvd ‹p.prime›, ← char_p.cast_eq_zero_iff (zmod p)]
end

instance : field (zmod p) :=
{ mul_inv_cancel := mul_inv_cancel_aux p,
  inv_zero := inv_zero p,
  .. zmod.nonzero_comm_ring p,
  .. zmod.has_inv p }

end zmod
