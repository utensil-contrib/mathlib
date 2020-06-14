import data.finset
import data.fintype.basic

variables {α : Type*} [linear_order α] {β : Type*}

open function finset

def mono_inc_on [linear_order β] (f : α → β) (t : set α) := ∀ (x ∈ t) (y ∈ t), x < y → f x < f y
def mono_dec_on [linear_order β] (f : α → β) (t : set α) := ∀ (x ∈ t) (y ∈ t), x < y → f x > f y

lemma injective_of_lt_imp_ne (f : α → β) (h : ∀ x y, x < y → f x ≠ f y) : injective f :=
begin
  intros x y k,
  contrapose k,
  rw [←ne.def, ne_iff_lt_or_gt] at k,
  cases k,
  apply h _ _ k,
  rw eq_comm,
  apply h _ _ k,
end

lemma erdos_szekeres {r s n : ℕ} (f : fin n → α) (hn : r * s < n) (hf : injective f) :
  (∃ (t : finset (fin n)), r < t.card ∧ mono_inc_on f ↑t) ∨
  (∃ (t : finset (fin n)), s < t.card ∧ mono_dec_on f ↑t) :=
begin
  classical,
  let sequences : finset (finset (fin n)) := univ.powerset,
  let inc_sequences_ending_in : fin n → finset (finset (fin n)),
  { intro i,
    apply sequences.filter (λ t, finset.max t = some i ∧ mono_inc_on f ↑t) },
  let dec_sequences_ending_in : fin n → finset (finset (fin n)),
  { intro i,
    apply sequences.filter (λ t, finset.max t = some i ∧ mono_dec_on f ↑t) },
  let ab : fin n → ℕ × ℕ,
  { intro i,
    apply (max' ((inc_sequences_ending_in i).image card) _, max' ((dec_sequences_ending_in i).image card) _);
    { apply nonempty.image,
      refine ⟨{i}, by simp [mono_inc_on, mono_dec_on]⟩ } },
  have : injective ab,
  { apply injective_of_lt_imp_ne,
    intros i j k,
    cases lt_or_gt_of_ne (λ _, ne_of_lt ‹i < j› (hf ‹f i = f j›)),
    { intro q,
      injection q with q,
      apply ne_of_lt _ q,
      rw nat.lt_iff_add_one_le,
      apply le_max',
      have : (ab i).1 ∈ _ := max'_mem _ _,
      rw mem_image at this,
      rcases this with ⟨t, ht₁, ht₂⟩,
      rw mem_image,
      rw mem_filter at ht₁,
      refine ⟨insert j t, _, _⟩,
      { rw mem_filter,
        refine ⟨_, _, _⟩,
        { rw mem_powerset, apply subset_univ },
        { convert max_insert,
          rw [ht₁.2.1, option.lift_or_get_some_some, max_eq_left],
          refl,
          apply le_of_lt ‹i < j› },
        { rw mono_inc_on,
          simp only [coe_insert, set.mem_insert_iff, mem_coe],
          rintros x ⟨rfl | v⟩ y ⟨rfl | w⟩ z,
          { exfalso, apply irrefl _ z },
          { exfalso,
            apply not_le_of_lt (trans k z),
            apply le_max_of_mem ‹y ∈ t›,
            simp [ht₁.2.1] },
          { apply lt_of_le_of_lt _ h,
            have : x ≤ i := le_max_of_mem ‹x ∈ t› _,
            { rw le_iff_lt_or_eq at this,
              rcases this with _ | rfl,
              { apply le_of_lt,
                apply ht₁.right.right x ‹x ∈ t› i (mem_of_max _) ‹x < i›,
                simp [ht₁.2.1] },
              { refl } },
            { simp [ht₁.2.1] } },
          { apply ht₁.2.2 _ ‹x ∈ t› _ ‹y ∈ t› ‹x < y› } } },
      { rw [card_insert_of_not_mem, ht₂],
        intro q,
        apply not_le_of_lt k,
        apply le_max_of_mem q _,
        simp [ht₁.2.1] } },
    { intro q,
      injection q with _ q,
      apply ne_of_lt _ q,
      rw nat.lt_iff_add_one_le,
      apply le_max',
      have : (ab i).2 ∈ _ := max'_mem _ _,
      rw mem_image at this,
      rcases this with ⟨t, ht₁, ht₂⟩,
      rw mem_image,
      rw mem_filter at ht₁,
      refine ⟨insert j t, _, _⟩,
      { rw mem_filter,
        refine ⟨_, _, _⟩,
        { rw mem_powerset, apply subset_univ },
        { convert max_insert,
          rw [ht₁.2.1, option.lift_or_get_some_some, max_eq_left],
          refl,
          apply le_of_lt ‹i < j› },
        { rw mono_dec_on,
          simp only [coe_insert, set.mem_insert_iff, mem_coe],
          rintros x ⟨rfl | v⟩ y ⟨rfl | w⟩ z,
          { exfalso, apply irrefl _ z },
          { exfalso,
            apply not_le_of_lt (trans k z),
            apply le_max_of_mem ‹y ∈ t›,
            simp [ht₁.2.1] },
          { apply lt_of_lt_of_le h _,
            have : x ≤ i := le_max_of_mem ‹x ∈ t› _,
            { rw le_iff_lt_or_eq at this,
              rcases this with _ | rfl,
              { apply le_of_lt,
                apply ht₁.2.2 _ ‹x ∈ t› i (mem_of_max _) ‹x < i›,
                simp [ht₁.2.1] },
              { refl } },
            { simp [ht₁.2.1] } },
          { apply ht₁.2.2 _ ‹x ∈ t› _ ‹y ∈ t› ‹x < y› } } },
      { rw [card_insert_of_not_mem, ht₂],
        intro q,
        apply not_le_of_lt k,
        apply le_max_of_mem q _,
        simp [ht₁.2.1] } } },
  suffices : (∃ i, r+1 ≤ (ab i).1) ∨ (∃ i, s+1 ≤ (ab i).2),
  { apply or.imp _ _ this,
    { rintro ⟨i, hi⟩,
      have : (ab i).1 ∈ _ := max'_mem _ _,
      rw mem_image at this,
      obtain ⟨t, ht₁, ht₂⟩ := this,
      refine ⟨t, by rwa ht₂, _⟩,
      rw mem_filter at ht₁,
      apply ht₁.2.2 },
    { rintro ⟨i, hi⟩,
      have : (ab i).2 ∈ _ := max'_mem _ _,
      rw mem_image at this,
      obtain ⟨t, ht₁, ht₂⟩ := this,
      refine ⟨t, by rwa ht₂, _⟩,
      rw mem_filter at ht₁,
      apply ht₁.2.2 } },
  by_contra,
  push_neg at a,
  have := card_image_of_injective univ this,
  rw [card_fin] at this,
  let ran : finset (ℕ × ℕ),
    apply ((range r).image nat.succ).product ((range s).image nat.succ),
  have : ran.card = r * s,
    rw [card_product, card_image_of_injective _ (λ x y, nat.succ_inj)],
    rw card_image_of_injective _ (λ x y, nat.succ_inj),
    rw card_range,
    rw card_range,
  have : image ab univ ⊆ ran,
  { rintro ⟨x₁, x₂⟩,
    simp only [mem_image, and_imp, exists_prop, mem_filter, gt_iff_lt, forall_prop_of_false,
               set.mem_singleton_iff, mem_range, not_lt, mem_univ, prod.mk.inj_iff, forall_eq,
               eq_self_iff_true, singleton_subset_iff, coe_singleton, exists_prop_of_true,
               and_self, exists_imp_distrib, max_singleton, mem_product],
    rintros i rfl rfl,
    refine ⟨_, _⟩,
    { have : 1 ≤ (ab i).1,
      { apply le_max',
        rw mem_image,
        refine ⟨{i}, _, card_singleton i⟩,
        simp [mono_inc_on] },
      { refine ⟨(ab i).1 - 1, _, _⟩,
        { rw nat.sub_lt_right_iff_lt_add this,
          apply a.1 },
        { apply nat.succ_pred_eq_of_pos this } } },
    { have : 1 ≤ (ab i).2,
      { apply le_max',
        rw mem_image,
        refine ⟨{i}, _, card_singleton i⟩,
        simp [mono_dec_on] },
      { refine ⟨(ab i).2 - 1, _, _⟩,
        { rw nat.sub_lt_right_iff_lt_add this,
          apply a.2 },
        { apply nat.succ_pred_eq_of_pos this } } } },
  have := card_le_of_subset this,
  rw [‹ran.card = _›, ‹(image ab univ).card = n›] at this,
  apply not_lt_of_le this hn,
end
