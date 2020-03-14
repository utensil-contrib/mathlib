/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group.basic
import category_theory.limits.limits

/-!
# The category of additive commutative groups has all colimits.

This file uses a "pre-automated" approach, just as for `Mon/colimits.lean`.
It is a very uniform approach, that conceivably could be synthesised directly
by a tactic that analyses the shape of `add_comm_group` and `monoid_hom`.
-/

universes u v

open category_theory
open category_theory.limits

-- [ROBOT VOICE]:
-- You should pretend for now that this file was automatically generated.
-- It follows the same template as colimits in Mon.
-- Note that this means this file does not meet documentation standards.

namespace AddCommGroup.colimits

variables {J : Type v} [small_category J] (F : J ⥤ AddCommGroup.{v})

inductive prequotient
-- There's always `of`
| of : Π (j : J) (x : F.obj j), prequotient
-- Then one generator for each operation
| zero {} : prequotient
| neg : prequotient → prequotient
| add : prequotient → prequotient → prequotient

open prequotient

inductive relation : prequotient F → prequotient F → Prop
-- Make it an equivalence relation:
| refl : Π (x), relation x x
| symm : Π (x y) (h : relation x y), relation y x
| trans : Π (x y z) (h : relation x y) (k : relation y z), relation x z
-- There's always a `map` relation
| map : Π (j j' : J) (f : j ⟶ j') (x : F.obj j), relation (of j' (F.map f x)) (of j x)
-- Then one relation per operation, describing the interaction with `of`
| zero : Π (j), relation (of j 0) zero
| neg : Π (j) (x : F.obj j), relation (of j (-x)) (neg (of j x))
| add : Π (j) (x y : F.obj j), relation (of j (x + y)) (add (of j x) (of j y))
-- Then one relation per argument of each operation
| neg_1 : Π (x x') (r : relation x x'), relation (neg x) (neg x')
| add_1 : Π (x x' y) (r : relation x x'), relation (add x y) (add x' y)
| add_2 : Π (x y y') (r : relation y y'), relation (add x y) (add x y')
-- And one relation per axiom
| zero_add      : Π (x), relation (add zero x) x
| add_zero      : Π (x), relation (add x zero) x
| add_left_neg  : Π (x), relation (add (neg x) x) zero
| add_comm      : Π (x y), relation (add x y) (add y x)
| add_assoc     : Π (x y z), relation (add (add x y) z) (add x (add y z))

def colimit_setoid : setoid (prequotient F) :=
{ r := relation F, iseqv := ⟨relation.refl, relation.symm, relation.trans⟩ }
attribute [instance] colimit_setoid

def colimit_type : Type v := quotient (colimit_setoid F)

instance : add_comm_group (colimit_type F) :=
{ zero :=
  begin
    exact quot.mk _ zero
  end,
  neg :=
  begin
    fapply @quot.lift,
    { intro x,
      exact quot.mk _ (neg x) },
    { intros x x' r,
      apply quot.sound,
      exact relation.neg_1 _ _ r },
  end,
  add :=
  begin
    fapply @quot.lift _ _ ((colimit_type F) → (colimit_type F)),
    { intro x,
      fapply @quot.lift,
      { intro y,
        exact quot.mk _ (add x y) },
      { intros y y' r,
        apply quot.sound,
        exact relation.add_2 _ _ _ r } },
    { intros x x' r,
      funext y,
      induction y,
      dsimp,
      apply quot.sound,
      { exact relation.add_1 _ _ _ r },
      { refl } },
  end,
  zero_add := λ x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.zero_add,
    refl,
  end,
  add_zero := λ x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.add_zero,
    refl,
  end,
  add_left_neg := λ x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.add_left_neg,
    refl,
  end,
  add_comm := λ x y,
  begin
    induction x,
    induction y,
    dsimp,
    apply quot.sound,
    apply relation.add_comm,
    refl,
    refl,
  end,
  add_assoc := λ x y z,
  begin
    induction x,
    induction y,
    induction z,
    dsimp,
    apply quot.sound,
    apply relation.add_assoc,
    refl,
    refl,
    refl,
  end, }

@[simp] lemma quot_zero : quot.mk setoid.r zero = (0 : colimit_type F) := rfl
@[simp] lemma quot_neg (x) : quot.mk setoid.r (neg x) = (-(quot.mk setoid.r x) : colimit_type F) := rfl
@[simp] lemma quot_add (x y) : quot.mk setoid.r (add x y) = ((quot.mk setoid.r x) + (quot.mk setoid.r y) : colimit_type F) := rfl

def colimit : AddCommGroup := AddCommGroup.of (colimit_type F)

def cocone_fun (j : J) (x : F.obj j) : colimit_type F :=
quot.mk _ (of j x)

def cocone_morphism (j : J) : F.obj j ⟶ colimit F :=
{ to_fun := cocone_fun F j,
  map_zero' := by apply quot.sound; apply relation.zero,
  map_add' := by intros; apply quot.sound; apply relation.add }

@[simp] lemma cocone_naturality {j j' : J} (f : j ⟶ j') :
  F.map f ≫ (cocone_morphism F j') = cocone_morphism F j :=
begin
  ext,
  apply quot.sound,
  apply relation.map,
end

@[simp] lemma cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j):
  (cocone_morphism F j') (F.map f x) = (cocone_morphism F j) x :=
by { rw ←cocone_naturality F f, refl }

def colimit_cocone : cocone F :=
{ X := colimit F,
  ι :=
  { app := cocone_morphism F } }.

@[simp] def desc_fun_lift (s : cocone F) : prequotient F → s.X
| (of j x)  := (s.ι.app j) x
| zero      := 0
| (neg x)   := -(desc_fun_lift x)
| (add x y) := desc_fun_lift x + desc_fun_lift y

def desc_fun (s : cocone F) : colimit_type F → s.X :=
begin
  fapply quot.lift,
  { exact desc_fun_lift F s },
  { intros x y r,
    induction r; try { dsimp },
    -- refl
    { refl },
    -- symm
    { exact r_ih.symm },
    -- trans
    { exact eq.trans r_ih_h r_ih_k },
    -- map
    { rw cocone.naturality_concrete, },
    -- zero
    { erw ((s.ι).app r).map_zero, refl },
    -- neg
    { rw ((s.ι).app r_j).map_neg },
    -- add
    { rw ((s.ι).app r_j).map_add },
    -- neg_1
    { rw r_ih, },
    -- add_1
    { rw r_ih, },
    -- add_2
    { rw r_ih, },
    -- zero_add
    { rw zero_add, },
    -- add_zero
    { rw add_zero, },
    -- add_left_neg
    { rw add_left_neg, },
    -- add_comm
    { rw add_comm, },
    -- add_assoc
    { rw add_assoc, },
  }
end

@[simp] def desc_morphism (s : cocone F) : colimit F ⟶ s.X :=
{ to_fun := desc_fun F s,
  map_zero' := rfl,
  map_add' := λ x y, by { induction x; induction y; refl }, }

def colimit_is_colimit : is_colimit (colimit_cocone F) :=
{ desc := λ s, desc_morphism F s,
  uniq' := λ s m w,
  begin
    ext,
    induction x,
    induction x,
    { have w' := congr_fun (congr_arg (λ f : F.obj x_j ⟶ s.X, (f : F.obj x_j → s.X)) (w x_j)) x_x,
      erw w',
      refl, },
    { simp only [desc_morphism, quot_zero],
      erw m.map_zero,
      refl, },
    { simp only [desc_morphism, quot_neg],
      erw m.map_neg,
      rw [x_ih],
      refl, },
    { simp only [desc_morphism, quot_add],
      erw m.map_add,
      rw [x_ih_a, x_ih_a_1],
      refl, },
    refl
  end }.

instance has_colimits_AddCommGroup : has_colimits.{v} AddCommGroup.{v} :=
{ has_colimits_of_shape := λ J 𝒥,
  { has_colimit := λ F, by exactI
    { cocone := colimit_cocone F,
      is_colimit := colimit_is_colimit F } } }

end AddCommGroup.colimits