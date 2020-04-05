/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov, Johannes Hölzl, Mario Carneiro, Patrick Massot
-/

import order.filter.basic data.set.countable

/-! # Filter bases

In this file we define `filter.has_basis l p s`, where `l` is a filter on `α`, `p` is a predicate
on some index set `ι`, and `s : ι → set α`.

## Main statements

* `has_basis.mem_iff`, `has_basis.mem_of_superset`, `has_basis.mem_of_mem` : restate `t ∈ f` in terms
  of a basis;
* `basis_sets` : all sets of a filter form a basis;
* `has_basis.inf`, `has_basis.inf_principal`, `has_basis.prod`, `has_basis.prod_self`,
  `has_basis.map`, `has_basis.comap` : combinators to construct filters of `l ⊓ l'`,
  `l ⊓ principal t`, `l.prod l'`, `l.prod l`, `l.map f`, `l.comap f` respectively;
* `has_basis.le_iff`, `has_basis.ge_iff`, has_basis.le_basis_iff` : restate `l ≤ l'` in terms
  of bases.
* `has_basis.tendsto_right_iff`, `has_basis.tendsto_left_iff`, `has_basis.tendsto_iff` : restate
  `tendsto f l l'` in terms of bases.

## Implementation notes

As with `Union`/`bUnion`/`sUnion`, there are three different approaches to filter bases:

* `has_basis l s`, `s : set (set α)`;
* `has_basis l s`, `s : ι → set α`;
* `has_basis l p s`, `p : ι → Prop`, `s : ι → set α`.

We use the latter one because, e.g., `𝓝 x` in an `emetric_space` or in a `metric_space` has a basis
of this form. The other two can be emulated using `s = id` or `p = λ _, true`.

With this approach sometimes one needs to `simp` the statement provided by the `has_basis`
machinery, e.g., `simp only [exists_prop, true_and]` or `simp only [forall_const]` can help
with the case `p = λ _, true`.
-/

namespace filter
variables {α : Type*} {β : Type*} {γ : Type*} {ι : Type*} {ι' : Type*}

open set

/-- We say that a filter `l` has a basis `s : ι → set α` bounded by `p : ι → Prop`,
if `t ∈ l` if and only if `t` includes `s i` for some `i` such that `p i`. -/
protected def has_basis (l : filter α) (p : ι → Prop) (s : ι → set α) : Prop :=
∀ t : set α, t ∈ l ↔ ∃ i (hi : p i), s i ⊆ t

section same_type

variables {l l' : filter α} {p : ι → Prop} {s : ι → set α} {t : set α} {i : ι}
  {p' : ι' → Prop} {s' : ι' → set α} {i' : ι'}

/-- Definition of `has_basis` unfolded to make it useful for `rw` and `simp`. -/
lemma has_basis.mem_iff (hl : l.has_basis p s) : t ∈ l ↔ ∃ i (hi : p i), s i ⊆ t :=
hl t

lemma has_basis.eventually_iff (hl : l.has_basis p s) {q : α → Prop} :
  (∀ᶠ x in l, q x) ↔ ∃ i (hi : p i), ∀ ⦃x⦄, x ∈ s i → q x :=
hl _

lemma has_basis.mem_of_superset (hl : l.has_basis p s) (hi : p i) (ht : s i ⊆ t) : t ∈ l :=
(hl t).2 ⟨i, hi, ht⟩

lemma has_basis.mem_of_mem (hl : l.has_basis p s) (hi : p i) : s i ∈ l :=
hl.mem_of_superset hi $ subset.refl _

lemma has_basis.forall_nonempty_iff_ne_bot (hl : l.has_basis p s) :
  (∀ {i}, p i → (s i).nonempty) ↔ l ≠ ⊥ :=
⟨λ H, forall_sets_nonempty_iff_ne_bot.1 $
  λ s hs, let ⟨i, hi, his⟩ := (hl s).1 hs in (H hi).mono his,
  λ H i hi, nonempty_of_mem_sets H (hl.mem_of_mem hi)⟩

lemma basis_sets (l : filter α) : l.has_basis (λ s : set α, s ∈ l) id :=
λ t, exists_sets_subset_iff.symm

lemma at_top_basis [nonempty α] [semilattice_sup α] :
  (@at_top α _).has_basis (λ _, true) Ici :=
λ t, by simpa only [exists_prop, true_and] using @mem_at_top_sets α _ _ t

lemma at_top_basis' [semilattice_sup α] (a : α) :
  (@at_top α _).has_basis (λ x, a ≤ x) Ici :=
λ t, (@at_top_basis α ⟨a⟩ _ t).trans
  ⟨λ ⟨x, _, hx⟩, ⟨x ⊔ a, le_sup_right, λ y hy, hx (le_trans le_sup_left hy)⟩,
    λ ⟨x, _, hx⟩, ⟨x, trivial, hx⟩⟩

theorem has_basis.ge_iff (hl' : l'.has_basis p' s')  : l ≤ l' ↔ ∀ i', p' i' → s' i' ∈ l :=
⟨λ h i' hi', h $ hl'.mem_of_mem hi',
  λ h s hs, let ⟨i', hi', hs⟩ := (hl' s).1 hs in mem_sets_of_superset (h _ hi') hs⟩

theorem has_basis.le_iff (hl : l.has_basis p s) : l ≤ l' ↔ ∀ t ∈ l', ∃ i (hi : p i), s i ⊆ t :=
by simp only [le_def, hl.mem_iff]

theorem has_basis.le_basis_iff (hl : l.has_basis p s) (hl' : l'.has_basis p' s') :
  l ≤ l' ↔ ∀ i', p' i' → ∃ i (hi : p i), s i ⊆ s' i' :=
by simp only [hl'.ge_iff, hl.mem_iff]

lemma has_basis.inf (hl : l.has_basis p s) (hl' : l'.has_basis p' s') :
  (l ⊓ l').has_basis (λ i : ι × ι', p i.1 ∧ p' i.2) (λ i, s i.1 ∩ s' i.2) :=
begin
  intro t,
  simp only [mem_inf_sets, exists_prop, hl.mem_iff, hl'.mem_iff],
  split,
  { rintros ⟨t, ⟨i, hi, ht⟩, t', ⟨i', hi', ht'⟩, H⟩,
    use [(i, i'), ⟨hi, hi'⟩, subset.trans (inter_subset_inter ht ht') H] },
  { rintros ⟨⟨i, i'⟩, ⟨hi, hi'⟩, H⟩,
    use [s i, i, hi, subset.refl _, s' i', i', hi', subset.refl _, H] }
end

lemma has_basis.inf_principal (hl : l.has_basis p s) (s' : set α) :
  (l ⊓ principal s').has_basis p (λ i, s i ∩ s') :=
λ t, by simp only [mem_inf_principal, hl.mem_iff, subset_def, mem_set_of_eq,
  mem_inter_iff, and_imp]

lemma has_basis.eq_binfi (h : l.has_basis p s) :
  l = ⨅ i (_ : p i), principal (s i) :=
eq_binfi_of_mem_sets_iff_exists_mem $ λ t, by simp only [h.mem_iff, mem_principal_sets]

lemma has_basis.eq_infi (h : l.has_basis (λ _, true) s) :
  l = ⨅ i, principal (s i) :=
by simpa only [infi_true] using h.eq_binfi

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma has_basis_infi_principal {s : ι → set α} (h : directed (≥) s) (ne : nonempty ι) :
  (⨅ i, principal (s i)).has_basis (λ _, true) s :=
begin
  refine λ t, (mem_infi (h.mono_comp _ _) ne t).trans $
    by simp only [exists_prop, true_and, mem_principal_sets],
  exact λ _ _, principal_mono.2
end

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma has_basis_binfi_principal {s : β → set α} {S : set β} (h : directed_on (s ⁻¹'o (≥)) S)
  (ne : S.nonempty) :
  (⨅ i ∈ S, principal (s i)).has_basis (λ i, i ∈ S) s :=
begin
  refine λ t, (mem_binfi _ ne).trans $ by simp only [mem_principal_sets],
  rw [directed_on_iff_directed, ← directed_comp, (∘)] at h ⊢,
  apply h.mono_comp _ _,
  exact λ _ _, principal_mono.2
end

lemma has_basis.map (f : α → β) (hl : l.has_basis p s) :
  (l.map f).has_basis p (λ i, f '' (s i)) :=
λ t, by simp only [mem_map, image_subset_iff, hl.mem_iff, preimage]

lemma has_basis.comap (f : β → α) (hl : l.has_basis p s) :
  (l.comap f).has_basis p (λ i, f ⁻¹' (s i)) :=
begin
  intro t,
  simp only [mem_comap_sets, exists_prop, hl.mem_iff],
  split,
  { rintros ⟨t', ⟨i, hi, ht'⟩, H⟩,
    exact ⟨i, hi, subset.trans (preimage_mono ht') H⟩ },
  { rintros ⟨i, hi, H⟩,
    exact ⟨s i, ⟨i, hi, subset.refl _⟩, H⟩ }
end

lemma has_basis.prod_self (hl : l.has_basis p s) :
  (l.prod l).has_basis p (λ i, (s i).prod (s i)) :=
begin
  intro t,
  apply mem_prod_iff.trans,
  split,
  { rintros ⟨t₁, ht₁, t₂, ht₂, H⟩,
    rcases hl.mem_iff.1 (inter_mem_sets ht₁ ht₂) with ⟨i, hi, ht⟩,
    exact ⟨i, hi, λ p ⟨hp₁, hp₂⟩, H ⟨(ht hp₁).1, (ht hp₂).2⟩⟩ },
  { rintros ⟨i, hi, H⟩,
    exact ⟨s i, hl.mem_of_mem hi, s i, hl.mem_of_mem hi, H⟩ }
end

@[nolint has_inhabited_instance]
structure decreasing_enumerated_basis (f : filter α)  :=
(V : ℕ → set α)
(decreasing : ∀ {n m}, n ≤ m → V m ⊆ V n)
(has_basis : filter.has_basis f (λ _, true) V)

instance  {α : Type*} {f : filter α} : has_coe_to_fun (decreasing_enumerated_basis f) :=
⟨_, decreasing_enumerated_basis.V⟩

lemma decreasing_enumerated_basis.basis {f : filter α} (B : decreasing_enumerated_basis f) :
  ∀ s, s ∈ f ↔ ∃ n, B n ⊆ s :=
λ s, by simpa [B.has_basis.mem_iff]

lemma decreasing_enumerated_basis.basis_mem {f : filter α} (B : decreasing_enumerated_basis f) :
  ∀ n, B n ∈ f :=
λ n, B.has_basis.mem_of_mem trivial
end same_type

section two_types

variables {la : filter α} {pa : ι → Prop} {sa : ι → set α}
  {lb : filter β} {pb : ι' → Prop} {sb : ι' → set β} {f : α → β}

lemma has_basis.tendsto_left_iff (hla : la.has_basis pa sa) :
  tendsto f la lb ↔ ∀ t ∈ lb, ∃ i (hi : pa i), ∀ x ∈ sa i, f x ∈ t :=
by { simp only [tendsto, (hla.map f).le_iff, image_subset_iff], refl }

lemma has_basis.tendsto_right_iff (hlb : lb.has_basis pb sb) :
  tendsto f la lb ↔ ∀ i (hi : pb i), ∀ᶠ x in la, f x ∈ sb i :=
by simp only [tendsto, hlb.ge_iff, mem_map, filter.eventually]

lemma has_basis.tendsto_iff (hla : la.has_basis pa sa) (hlb : lb.has_basis pb sb) :
  tendsto f la lb ↔ ∀ ib (hib : pb ib), ∃ ia (hia : pa ia), ∀ x ∈ sa ia, f x ∈ sb ib :=
by simp only [hlb.tendsto_right_iff, hla.eventually_iff, subset_def, mem_set_of_eq]

lemma tendsto.basis_left (H : tendsto f la lb) (hla : la.has_basis pa sa) :
  ∀ t ∈ lb, ∃ i (hi : pa i), ∀ x ∈ sa i, f x ∈ t :=
hla.tendsto_left_iff.1 H

lemma tendsto.basis_right (H : tendsto f la lb) (hlb : lb.has_basis pb sb) :
  ∀ i (hi : pb i), ∀ᶠ x in la, f x ∈ sb i :=
hlb.tendsto_right_iff.1 H

lemma tendsto.basis_both (H : tendsto f la lb) (hla : la.has_basis pa sa)
  (hlb : lb.has_basis pb sb) :
  ∀ ib (hib : pb ib), ∃ ia (hia : pa ia), ∀ x ∈ sa ia, f x ∈ sb ib :=
(hla.tendsto_iff hlb).1 H

lemma has_basis.prod (hla : la.has_basis pa sa) (hlb : lb.has_basis pb sb) :
  (la.prod lb).has_basis (λ i : ι × ι', pa i.1 ∧ pb i.2) (λ i, (sa i.1).prod (sb i.2)) :=
(hla.comap prod.fst).inf (hlb.comap prod.snd)

lemma decreasing_enumerated_basis.tendsto {f : filter α} {g : filter β}
(B : decreasing_enumerated_basis g) (φ : α → β) : tendsto φ f g ↔ ∀ n, ∀ᶠ x in f, φ x ∈ B n :=
by simpa [B.has_basis.tendsto_right_iff]

lemma decreasing_enumerated_basis.tendsto' {g : filter β}
(B : decreasing_enumerated_basis g) {φ : ℕ → β} (h : ∀ n, φ n ∈ B n) : tendsto φ at_top g :=
begin
  rw B.tendsto,
  intro n,
  rw eventually_at_top,
  use n,
  intros m hm,
  exact B.decreasing hm (h m),
end

end two_types

/--
A filter has a countable basis iff it is generated by a countable collection
of subsets of α. (A filter is a generated by a collection of sets iff it is
the infimum of the principal filters.)

Note: we do not require the collection to be closed under finite intersections.
-/
def has_countable_basis (f : filter α) : Prop :=
∃ s : set (set α), countable s ∧ f = ⨅ t ∈ s, principal t

lemma has_countable_basis_of_seq (f : filter α) (x : ℕ → set α) (h : f = ⨅ i, principal (x i)) :
  f.has_countable_basis :=
⟨range x, countable_range _, by rwa infi_range⟩

lemma seq_of_has_countable_basis (f : filter α) (cblb : f.has_countable_basis) :
    ∃ x : ℕ → set α, f = ⨅ i, principal (x i) :=
begin
  rcases cblb with ⟨B, Bcbl, gen⟩, subst gen,
  cases B.eq_empty_or_nonempty with hB Bnonempty, { use λ n, set.univ, simp [principal_univ, *] },
  rw countable_iff_exists_surjective_to_subtype Bnonempty at Bcbl,
  rcases Bcbl with ⟨g, gsurj⟩,
  rw infi_subtype',
  use (λ n, g n), apply le_antisymm; rw le_infi_iff,
  { intro i, apply infi_le_of_le (g i) _, apply le_refl _ },
  { intros a, rcases gsurj a with i, apply infi_le_of_le i _, subst h, apply le_refl _ }
end

/--
Different characterization of countable basis. A filter has a countable basis
iff it is generated by a sequence of sets.
-/
lemma has_countable_basis_iff_seq (f : filter α) :
  f.has_countable_basis ↔
    ∃ x : ℕ → set α, f = ⨅ i, principal (x i) :=
⟨seq_of_has_countable_basis _, λ ⟨x, xgen⟩, has_countable_basis_of_seq _ x xgen⟩

lemma mono_seq_of_has_countable_basis (f : filter α) (cblb : f.has_countable_basis) :
  ∃ x : ℕ → set α, (∀ i j, i ≤ j → x j ⊆ x i) ∧ f = ⨅ i, principal (x i) :=
begin
  rcases (seq_of_has_countable_basis f cblb) with ⟨x', hx'⟩,
  let x := λ n, ⋂ m ≤ n, x' m,
  use x, split,
  { intros i j hij a, simp [x], intros h i' hi'i, apply h, transitivity; assumption },
  subst hx', apply le_antisymm; rw le_infi_iff; intro i,
  { rw le_principal_iff, apply Inter_mem_sets (finite_le_nat _),
    intros j hji, rw ← le_principal_iff, apply infi_le_of_le j _, apply le_refl _ },
  { apply infi_le_of_le i _, rw principal_mono, intro a, simp [x], intro h, apply h, refl },
end

/--
Different characterization of countable basis. A filter has a countable basis
iff it is generated by a monotonically decreasing sequence of sets.
-/
lemma has_countable_basis_iff_mono_seq (f : filter α) :
  f.has_countable_basis ↔
    ∃ x : ℕ → set α, (∀ i j, i ≤ j → x j ⊆ x i) ∧ f = ⨅ i, principal (x i) :=
⟨mono_seq_of_has_countable_basis _, λ ⟨x, _, xgen⟩, has_countable_basis_of_seq _ x xgen⟩

/--
Different characterization of countable basis. A filter has a countable basis
iff there exists a monotonically decreasing sequence of sets `x i`
such that `s ∈ f ↔ ∃ i, x i ⊆ s`. -/
lemma has_countable_basis_iff_mono_seq' (f : filter α) :
  f.has_countable_basis ↔
    ∃ x : ℕ → set α, (∀ i j, i ≤ j → x j ⊆ x i) ∧ (∀ {s}, s ∈ f ↔ ∃ i, x i ⊆ s) :=
begin
  refine (has_countable_basis_iff_mono_seq f).trans (exists_congr $ λ x, and_congr_right _),
  intro hmono,
  have : directed (≥) (λ i, principal (x i)),
    from directed_of_mono _ (λ i j hij, principal_mono.2 (hmono _ _ hij)),
  simp only [filter.ext_iff, mem_infi this ⟨0⟩, mem_Union, mem_principal_sets]
end

lemma has_countable_basis.comap {l : filter β} (h : has_countable_basis l) (f : α → β) :
  has_countable_basis (l.comap f) :=
begin
  rcases h with ⟨S, h₁, h₂⟩,
  refine ⟨preimage f '' S, countable_image _ h₁, _⟩,
  calc comap f l = ⨅ s ∈ S, principal (f ⁻¹' s) : by simp [h₂]
  ... = ⨅ s ∈ S, ⨅ (t : set α) (H : f ⁻¹' s = t), principal t : by simp
  ... = ⨅ (t : set α) (s ∈ S) (h₂ : f ⁻¹' s = t), principal t :
    by { rw [infi_comm], congr' 1, ext t, rw [infi_comm] }
  ... = _ : by simp [-infi_infi_eq_right, infi_and]
end

-- TODO : prove this for a encodable type
lemma has_countable_basis_at_top_finset_nat : has_countable_basis (@at_top (finset ℕ) _) :=
begin
  refine has_countable_basis_of_seq _ (λN, Ici (finset.range N)) (eq_infi_of_mem_sets_iff_exists_mem _),
  assume s,
  rw mem_at_top_sets,
  refine ⟨_, λ ⟨N, hN⟩, ⟨finset.range N, hN⟩⟩,
  rintros ⟨t, ht⟩,
  rcases mem_at_top_sets.1 (tendsto_finset_range (mem_at_top t)) with ⟨N, hN⟩,
  simp only [preimage, mem_set_of_eq] at hN,
  exact ⟨N, mem_principal_sets.2 $ λ t' ht', ht t' $ le_trans (hN _ $ le_refl N) ht'⟩
end

lemma has_countable_basis.tendsto_iff_seq_tendsto {f : α → β} {k : filter α} {l : filter β}
  (hcb : k.has_countable_basis) :
  tendsto f k l ↔ (∀ x : ℕ → α, tendsto x at_top k → tendsto (f ∘ x) at_top l) :=
suffices (∀ x : ℕ → α, tendsto x at_top k → tendsto (f ∘ x) at_top l) → tendsto f k l,
  from ⟨by intros; apply tendsto.comp; assumption, by assumption⟩,
begin
  rw filter.has_countable_basis_iff_mono_seq at hcb,
  rcases hcb with ⟨g, gmon, gbasis⟩,
  have gbasis : ∀ A, A ∈ k ↔ ∃ i, g i ⊆ A,
  { intro A,
    subst gbasis,
    rw mem_infi,
    { simp only [set.mem_Union, iff_self, filter.mem_principal_sets] },
    { exact directed_of_mono _ (λ i j h, principal_mono.mpr $ gmon _ _ h) },
    { apply_instance } },
  classical, contrapose,
  simp only [not_forall, not_imp, not_exists, subset_def, @tendsto_def _ _ f, gbasis],
  rintro ⟨B, hBl, hfBk⟩,
  choose x h using hfBk,
  use x, split,
  { simp only [tendsto_at_top', gbasis],
    rintros A ⟨i, hgiA⟩,
    use i,
    refine (λ j hj, hgiA $ gmon _ _ hj _),
    simp only [h] },
  { simp only [tendsto_at_top', (∘), not_forall, not_exists],
    use [B, hBl],
    intro i, use [i, (le_refl _)],
    apply (h i).right },
end

lemma has_countable_basis.tendsto_of_seq_tendsto {f : α → β} {k : filter α} {l : filter β}
  (hcb : k.has_countable_basis) :
  (∀ x : ℕ → α, tendsto x at_top k → tendsto (f ∘ x) at_top l) → tendsto f k l :=
hcb.tendsto_iff_seq_tendsto.2

def decreasing_enumerated_basis.of_has_countable_basis {f : filter α}
  (hf : has_countable_basis f) : decreasing_enumerated_basis f :=
begin
  choose V hV using mono_seq_of_has_countable_basis f hf,
  cases hV with dec basis,
  refine { V := V, decreasing := dec, ..},
  have dir : directed ge (λ (i : ℕ), principal (V i)),
  { intros i j,
    use max i j,
    simp only [mem_principal_sets, ge_iff_le, le_principal_iff],
    split ; apply dec ; [exact le_max_left _ _, exact le_max_right _ _] },
  intros S,
  simp [basis, mem_infi dir],
end
end filter

