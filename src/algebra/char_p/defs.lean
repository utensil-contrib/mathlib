/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kenny Lau, Joey van Langen, Casper Putz

Characteristic of semirings.
-/

import data.fintype.basic

universes u v

/-- The generator of the kernel of the unique homomorphism ℕ → α for a semiring α -/
class char_p (R : Type u) [semiring R] (p : ℕ) : Prop :=
(cast_eq_zero_iff [] : ∀ x:ℕ, (x:R) = 0 ↔ p ∣ x)

variables (R : Type u) [semiring R]

theorem char_p.cast_eq_zero (p : ℕ) [char_p R p] : (p:R) = 0 :=
(char_p.cast_eq_zero_iff R p p).2 (dvd_refl p)

lemma char_p.int_cast_eq_zero_iff (R : Type u) [ring R] (p : ℕ) [char_p R p] (a : ℤ) :
  (a : R) = 0 ↔ (p:ℤ) ∣ a :=
begin
  rcases lt_trichotomy a 0 with h|rfl|h,
  { rw [← neg_eq_zero, ← int.cast_neg, ← dvd_neg],
    lift -a to ℕ using neg_nonneg.mpr (le_of_lt h) with b,
    rw [int.cast_coe_nat, char_p.cast_eq_zero_iff R p, int.coe_nat_dvd] },
  { simp only [int.cast_zero, eq_self_iff_true, dvd_zero] },
  { lift a to ℕ using (le_of_lt h) with b,
    rw [int.cast_coe_nat, char_p.cast_eq_zero_iff R p, int.coe_nat_dvd] }
end

theorem char_p.eq {p q : ℕ} (c1 : char_p R p) (c2 : char_p R q) : p = q :=
nat.dvd_antisymm
  ((char_p.cast_eq_zero_iff R p q).1 (char_p.cast_eq_zero _ _))
  ((char_p.cast_eq_zero_iff R q p).1 (char_p.cast_eq_zero _ _))

instance char_p.of_char_zero [char_zero R] : char_p R 0 :=
⟨λ x, by rw [zero_dvd_iff, ← nat.cast_zero, nat.cast_inj]⟩
