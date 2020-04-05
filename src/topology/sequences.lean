/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot
-/

import topology.basic
import topology.bases
import topology.subset_properties

/-!
# Sequences in topological spaces

In this file we define sequences in topological spaces and show how they are related to
filters and the topology. In particular, we
* associate a filter with a sequence and prove equivalence of convergence of the two,
* define the sequential closure of a set and prove that it's contained in the closure,
* define a type class "sequential_space" in which closure and sequential closure agree,
* define sequential continuity and show that it coincides with continuity in sequential spaces,
* provide an instance that shows that every first-countable (and in particular metric) space is a sequential space.

# TODO
* Sequential compactness should be handled here.
-/

open set filter
open_locale topological_space

variables {α : Type*} {β : Type*}

local notation f ` ⟶ ` limit := tendsto f at_top (𝓝 limit)

/-! ### Statements about sequences in general topological spaces. -/
section topological_space
variables [topological_space α] [topological_space β]

/-- A sequence converges in the sence of topological spaces iff the associated statement for filter
holds. -/
@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma topological_space.seq_tendsto_iff {x : ℕ → α} {limit : α} :
  tendsto x at_top (𝓝 limit) ↔
    ∀ U : set α, limit ∈ U → is_open U → ∃ n0 : ℕ, ∀ n ≥ n0, (x n) ∈ U :=
(at_top_basis.tendsto_iff (nhds_basis_opens limit)).trans $
  by simp only [and_imp, exists_prop, true_and, set.mem_Ici, ge_iff_le, id]

/-- The sequential closure of a subset M ⊆ α of a topological space α is
the set of all p ∈ α which arise as limit of sequences in M. -/
def sequential_closure (M : set α) : set α :=
{p | ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ M) ∧ (x ⟶ p)}

lemma subset_sequential_closure (M : set α) : M ⊆ sequential_closure M :=
assume p (_ : p ∈ M), show p ∈ sequential_closure M, from
  ⟨λ n, p, assume n, ‹p ∈ M›, tendsto_const_nhds⟩

/-- A set `s` is sequentially closed if for any converging sequence `x n` of elements of `s`,
the limit belongs to `s` as well. -/
def is_seq_closed (s : set α) : Prop := s = sequential_closure s

/-- A convenience lemma for showing that a set is sequentially closed. -/
lemma is_seq_closed_of_def {A : set α}
  (h : ∀(x : ℕ → α) (p : α), (∀ n : ℕ, x n ∈ A) → (x ⟶ p) → p ∈ A) : is_seq_closed A :=
show A = sequential_closure A, from subset.antisymm
  (subset_sequential_closure A)
  (show ∀ p, p ∈ sequential_closure A → p ∈ A, from
    (assume p ⟨x, _, _⟩, show p ∈ A, from h x p ‹∀ n : ℕ, ((x n) ∈ A)› ‹(x ⟶ p)›))

/-- The sequential closure of a set is contained in the closure of that set.
The converse is not true. -/
lemma sequential_closure_subset_closure (M : set α) : sequential_closure M ⊆ closure M :=
assume p ⟨x, xM, xp⟩,
mem_closure_of_tendsto at_top_ne_bot xp (univ_mem_sets' xM)

/-- A set is sequentially closed if it is closed. -/
lemma is_seq_closed_of_is_closed (M : set α) (_ : is_closed M) : is_seq_closed M :=
suffices sequential_closure M ⊆ M, from
  set.eq_of_subset_of_subset (subset_sequential_closure M) this,
calc sequential_closure M ⊆ closure M : sequential_closure_subset_closure M
  ... = M : closure_eq_of_is_closed ‹is_closed M›

/-- The limit of a convergent sequence in a sequentially closed set is in that set.-/
lemma mem_of_is_seq_closed {A : set α} (_ : is_seq_closed A) {x : ℕ → α}
  (_ : ∀ n, x n ∈ A) {limit : α} (_ : (x ⟶ limit)) : limit ∈ A :=
have limit ∈ sequential_closure A, from
  show ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ A) ∧ (x ⟶ limit), from ⟨x, ‹∀ n, x n ∈ A›, ‹(x ⟶ limit)›⟩,
eq.subst (eq.symm ‹is_seq_closed A›) ‹limit ∈ sequential_closure A›

/-- The limit of a convergent sequence in a closed set is in that set.-/
lemma mem_of_is_closed_sequential {A : set α} (_ : is_closed A) {x : ℕ → α}
  (_ : ∀ n, x n ∈ A) {limit : α} (_ : x ⟶ limit) : limit ∈ A :=
mem_of_is_seq_closed (is_seq_closed_of_is_closed A ‹is_closed A›) ‹∀ n, x n ∈ A› ‹(x ⟶ limit)›

/-- A sequential space is a space in which 'sequences are enough to probe the topology'. This can be
 formalised by demanding that the sequential closure and the closure coincide. The following
 statements show that other topological properties can be deduced from sequences in sequential
 spaces. -/
class sequential_space (α : Type*) [topological_space α] : Prop :=
(sequential_closure_eq_closure : ∀ M : set α, sequential_closure M = closure M)

/-- In a sequential space, a set is closed iff it's sequentially closed. -/
lemma is_seq_closed_iff_is_closed [sequential_space α] {M : set α} :
  is_seq_closed M ↔ is_closed M :=
iff.intro
  (assume _, closure_eq_iff_is_closed.mp (eq.symm
    (calc M = sequential_closure M : by assumption
        ... = closure M            : sequential_space.sequential_closure_eq_closure M)))
  (is_seq_closed_of_is_closed M)

/-- In a sequential space, a point belongs to the closure of a set iff it is a limit of a sequence
taking values in this set. -/
lemma mem_closure_iff_seq_limit [sequential_space α] {s : set α} {a : α} :
  a ∈ closure s ↔ ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ s) ∧ (x ⟶ a) :=
by { rw ← sequential_space.sequential_closure_eq_closure, exact iff.rfl }

/-- A function between topological spaces is sequentially continuous if it commutes with limit of
 convergent sequences. -/
def sequentially_continuous (f : α → β) : Prop :=
∀ (x : ℕ → α), ∀ {limit : α}, (x ⟶ limit) → (f∘x ⟶ f limit)

/- A continuous function is sequentially continuous. -/
lemma continuous.to_sequentially_continuous {f : α → β} (_ : continuous f) :
  sequentially_continuous f :=
assume x limit (_ : x ⟶ limit),
have tendsto f (𝓝 limit) (𝓝 (f limit)), from continuous.tendsto ‹continuous f› limit,
show (f ∘ x) ⟶ (f limit), from tendsto.comp this ‹(x ⟶ limit)›

/-- In a sequential space, continuity and sequential continuity coincide. -/
lemma continuous_iff_sequentially_continuous {f : α → β} [sequential_space α] :
  continuous f ↔ sequentially_continuous f :=
iff.intro
  (assume _, ‹continuous f›.to_sequentially_continuous)
  (assume : sequentially_continuous f, show continuous f, from
    suffices h : ∀ {A : set β}, is_closed A → is_seq_closed (f ⁻¹' A), from
      continuous_iff_is_closed.mpr (assume A _, is_seq_closed_iff_is_closed.mp $ h ‹is_closed A›),
    assume A (_ : is_closed A),
      is_seq_closed_of_def $
        assume (x : ℕ → α) p (_ : ∀ n, f (x n) ∈ A) (_ : x ⟶ p),
        have (f ∘ x) ⟶ (f p), from ‹sequentially_continuous f› x ‹(x ⟶ p)›,
        show f p ∈ A, from
          mem_of_is_closed_sequential ‹is_closed A› ‹∀ n, f (x n) ∈ A› ‹(f∘x ⟶ f p)›)

end topological_space

namespace topological_space

namespace first_countable_topology

/-- Every first-countable space is sequential. -/
@[priority 100] -- see Note [lower instance priority]
instance [topological_space α] [first_countable_topology α] : sequential_space α :=
⟨show ∀ M, sequential_closure M = closure M, from assume M,
  suffices closure M ⊆ sequential_closure M,
    from set.subset.antisymm (sequential_closure_subset_closure M) this,
  -- For every p ∈ closure M, we need to construct a sequence x in M that converges to p:
  assume (p : α) (hp : p ∈ closure M),
  -- Since we are in a first-countable space, there exists a monotonically decreasing
  -- sequence g of sets generating the neighborhood filter around p:
  exists.elim (mono_seq_of_has_countable_basis _
    (nhds_generated_countable p)) $ assume g ⟨gmon, gbasis⟩,
  -- (g i) is a neighborhood of p and hence intersects M.
  -- Via choice we obtain the sequence x such that (x i).val ∈ g i ∩ M:
  have x : Π i, g i ∩ M,
  { rw mem_closure_iff_nhds at hp,
    intro i, apply classical.indefinite_description,
    apply hp, rw gbasis, rw ← le_principal_iff, apply infi_le_of_le i _, apply le_refl _ },
  -- It remains to show that x converges to p. Intuitively this is the case
  -- because x i ∈ g i, and the g i get "arbitrarily small" around p. Formally:
  have gssnhds : ∀ s ∈ 𝓝 p, ∃ i, g i ⊆ s,
  { intro s, rw gbasis, rw mem_infi,
    { simp, intros i hi, use i, assumption },
    { apply directed_of_mono, intros, apply principal_mono.mpr, apply gmon, assumption },
    { apply_instance } },
  -- For the sequence (x i) we can now show that a) it lies in M, and b) converges to p.
  ⟨λ i, (x i).val, by intro i; simp [(x i).property.right],
    begin
      rw tendsto_at_top', intros s nhdss,
      rcases gssnhds s nhdss with ⟨i, hi⟩,
      use i, intros j hij, apply hi, apply gmon _ _ hij,
      simp [(x j).property.left]
    end⟩⟩

end first_countable_topology

end topological_space

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma filter.map_at_top_inf_ne_bot_iff {α : Type*} [semilattice_sup α] [nonempty α] {β : Type*} {F : filter β} {u : α → β} :
  (map u at_top) ⊓ F ≠ ⊥ ↔ ∀ U ∈ F, ∀ N, ∃ n ≥ N, u n ∈ U :=
by simp_rw [inf_ne_bot_iff_frequently_right, frequently_map, frequently_at_top] ; trivial

lemma extraction_of_frequently_at_top' {P : ℕ → Prop} (h : ∀ N, ∃ n > N, P n) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, P (φ n) :=
begin
  choose u hu using h,
  cases forall_and_distrib.mp hu with hu hu',
  exact ⟨u ∘ (nat.rec 0 (λ n v, u v)), strict_mono.nat (λ n, hu _), λ n, hu' _⟩,
end

lemma extraction_of_frequently_at_top {P : ℕ → Prop} (h : ∃ᶠ n in at_top, P n) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, P (φ n) :=
begin
  rw frequently_at_top' at h,
  exact extraction_of_frequently_at_top' h,
end

--- High scores

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma exists_le_of_tendsto_at_top {α : Type*} [decidable_linear_order α]
  {β : Type*} [preorder β] {u : α → β} (h : tendsto u at_top at_top) :
∀ a b, ∃ a' ≥ a, b ≤ u a' :=
begin
  intros a b,
  rw tendsto_at_top at h,
  haveI : nonempty α := ⟨a⟩,
  cases mem_at_top_sets.mp (h b) with a' ha',
  exact ⟨max a a', le_max_left _ _, ha' _ $ le_max_right _ _⟩,
end

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma exists_lt_of_tendsto_at_top {α : Type*} [decidable_linear_order α]
  {β : Type*} [preorder β] [no_top_order β] {u : α → β} (h : tendsto u at_top at_top) :
∀ a b, ∃ a' ≥ a, b < u a' :=
begin
  intros a b,
  cases no_top b with b' hb',
  rcases exists_le_of_tendsto_at_top h a b' with ⟨a', ha', ha''⟩,
  exact ⟨a', ha', lt_of_lt_of_le hb' ha''⟩
end

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma high_scores {β : Type*} [decidable_linear_order β] [no_top_order β] {u : ℕ → β}
  (hu : tendsto u at_top at_top) : ∀ N, ∃ n ≥ N, ∀ k < n, u k < u n :=
begin
  intros N,
  let A := finset.image u (finset.range $ N+1), -- A = {u 0, ..., u N}
  have Ane : A.nonempty,
    from ⟨u 0, finset.mem_image_of_mem _ (finset.mem_range.mpr $ nat.zero_lt_succ _)⟩,
  let M := finset.max' A Ane,
  have ex : ∃ n ≥ N, M < u n,
    from exists_lt_of_tendsto_at_top hu _ _,
  obtain ⟨n, hnN, hnM, hn_min⟩ : ∃ n, N ≤ n ∧ M < u n ∧ ∀ k, N ≤ k → k < n → u k ≤ M,
  { use nat.find ex,
    rw ← and_assoc,
    split,
    { simpa using nat.find_spec ex },
    { intros k hk hk',
      simpa [hk] using nat.find_min ex hk' } },
  use [n, hnN],
  intros k hk,
  by_cases H : k ≤ N,
  { have : u k ∈ A,
      from finset.mem_image_of_mem _ (finset.mem_range.mpr $ nat.lt_succ_of_le H),
    have : u k ≤ M,
      from finset.le_max' A Ane (u k) this,
    exact lt_of_le_of_lt this hnM },
  { push_neg at H,
    calc u k ≤ M   : hn_min k (le_of_lt H) hk
         ... < u n : hnM },
end

lemma frequently_high_scores {β : Type*} [decidable_linear_order β] [no_top_order β] {u : ℕ → β}
  (hu : tendsto u at_top at_top) : ∃ᶠ n in at_top, ∀ k < n, u k < u n :=
by simpa [frequently_at_top] using high_scores hu

lemma strict_mono_subseq_of_tendsto_at_top
  {β : Type*} [decidable_linear_order β] [no_top_order β]
  {u : ℕ → β} (hu : tendsto u at_top at_top) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ strict_mono (u ∘ φ) :=
let ⟨φ, h, h'⟩ := extraction_of_frequently_at_top (frequently_high_scores hu) in
⟨φ, h, λ n m hnm, h' m _ (h hnm)⟩

lemma strict_mono_subseq_of_id_le {u : ℕ → ℕ} (hu : ∀ n, n ≤ u n) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ strict_mono (u ∘ φ) :=
strict_mono_subseq_of_tendsto_at_top (tendsto_at_top_mono _ hu tendsto_id)

lemma nat.id_le_of_strict_mono {φ : ℕ → ℕ} (h : strict_mono φ) : ∀ n, n ≤ φ n :=
λ n, nat.rec_on n (nat.zero_le _) (λ n hn, nat.succ_le_of_lt (lt_of_le_of_lt hn $ h $ nat.lt_succ_self n))

lemma strict_mono.tendsto_at_top {φ : ℕ → ℕ} (h : strict_mono φ) :
  tendsto φ at_top at_top :=
tendsto_at_top_mono _ (nat.id_le_of_strict_mono h) tendsto_id

lemma subseq_tendsto_of_countable_basis {X : Type*} {f : filter X} (hf : has_countable_basis f)
  {u : ℕ → X}
  (hx : map u at_top ⊓ f ≠ ⊥) :
  ∃ (θ : ℕ → ℕ), (strict_mono θ) ∧ (tendsto (u ∘ θ) at_top f) :=
begin
  let B := decreasing_enumerated_basis.of_has_countable_basis hf,
  have : ∀ N, ∃ n ≥ N, u n ∈ B N,
    from λ N, filter.map_at_top_inf_ne_bot_iff.mp hx _ (B.basis_mem N) N,
  choose φ hφ using this,
  cases forall_and_distrib.mp hφ with φ_ge φ_in,
  have lim_uφ : tendsto (u ∘ φ) at_top f,
    from B.tendsto' φ_in,
  have lim_φ : tendsto φ at_top at_top,
    from (tendsto_at_top_mono _ φ_ge tendsto_id),
  obtain ⟨ψ, hψ, hψφ⟩ : ∃ ψ : ℕ → ℕ, strict_mono ψ ∧ strict_mono (φ ∘ ψ),
    from strict_mono_subseq_of_tendsto_at_top lim_φ,
  exact ⟨φ ∘ ψ, hψφ, lim_uφ.comp hψ.tendsto_at_top⟩,
end

open topological_space

variables {X : Type*} [topological_space X] [first_countable_topology X]

lemma first_countable_topology.tendsto_subseq
  {u : ℕ → X} {x : X} (hx : map u at_top ⊓ 𝓝 x ≠ ⊥) :
  ∃ (ψ : ℕ → ℕ), (strict_mono ψ) ∧ (u ∘ ψ ⟶ x) :=
subseq_tendsto_of_countable_basis (first_countable_topology.nhds_generated_countable x) hx

lemma compact.tendsto_subseq' {s : set X} {u : ℕ → X} (hs : compact s) (hu : ∀ᶠ n in at_top, u n ∈ s) :
∃ (x ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) :=
begin
  rcases hs (map u at_top) (map_ne_bot $ at_top_ne_bot) (le_principal_iff.mpr hu) with ⟨x, x_in, hx⟩,
  exact ⟨x, x_in, first_countable_topology.tendsto_subseq hx⟩,
end

lemma compact.tendsto_subseq {s : set X} {u : ℕ → X} (hs : compact s) (hu : ∀ n, u n ∈ s) :
∃ (x ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) :=
hs.tendsto_subseq' (univ_mem_sets' hu)
