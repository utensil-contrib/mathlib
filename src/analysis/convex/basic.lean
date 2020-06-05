/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov
-/
import data.set.intervals
import data.complex.module
import algebra.pointwise
import linear_algebra.affine_space

/-!
# Convex sets and functions on real vector spaces

In a real vector space, we define the following objects and properties.

* `segment x y` is the closed segment joining `x` and `y`.
* A set `s` is `convex` if for any two points `x y ∈ s` it includes `segment x y`;
* A function `f` is `convex_on` a set `s` if `s` is itself a convex set, and for any two points
  `x y ∈ s` the segment joining `(x, f x)` to `(y, f y)` is (non-strictly) above the graph of `f`;
  equivalently, `convex_on f s` means that the epigraph `{p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2}`
  is a convex set;
* Center mass of a finite set of points with prescribed weights.
* Convex hull of a set `s` is the minimal convex set that includes `s`.
* Standard simplex `std_simplex ι [fintype ι]` is the intersection of the positive quadrant with
  the hyperplane `s.sum = 1` in the space `ι → ℝ`.

We also provide various equivalent versions of the definitions above, prove that some specific sets
are convex, and prove Jensen's inequality.

## Notations

We use the following local notations:

* `I = Icc (0:ℝ) 1`;
* `[x, y] = segment x y`.

They are defined using `local notation`, so they are not available outside of this file.
-/

universes u' u v ua va w x

variables {E : Type u} {F : Type v} {PE : Type ua} {PF : Type va}  {ι : Type w} {ι' : Type x}
  [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F]
  [affine_space ℝ E PE] [affine_space ℝ F PF]
  {s : set PE}

open set
open_locale classical
noncomputable theory

local notation `I` := (Icc 0 1 : set ℝ)

local attribute [instance] set.pointwise_add set.smul_set

section sets

/-! ### Segment -/

variable (E)

/-- The affine map from `ℝ` to `PE` sending `0` to `x` and `1` to `y`. -/
noncomputable def line_map (x y : PE) : affine_map ℝ ℝ ℝ E PE :=
{ to_fun := λ θ, θ • (y -ᵥ x : E) +ᵥ x,
  linear := linear_map.id.smul_right (y -ᵥ x),
  map_vadd' := λ p v, by simp [add_smul, add_action.vadd_assoc] }

@[simp] lemma line_map_apply (x y : PE) (θ : ℝ) : line_map E x y θ = θ • (y -ᵥ x : E) +ᵥ x := rfl

lemma line_map_swap (x y : PE) : ⇑(line_map E y x) = line_map E x y ∘ (λ θ, 1 - θ) :=
begin
  ext θ,
  simp only [function.comp_app, line_map_apply, sub_smul, ← add_torsor.neg_vsub_eq_vsub_rev E y x,
    one_smul, smul_neg, neg_sub],
  rw [sub_eq_neg_add, ← add_action.vadd_assoc, add_torsor.vsub_vadd]
end

/-- Segments in an affine space -/
def segment (x y : PE) : set PE := line_map E x y '' I

local notation `[`x `, ` y `][` E `]` := segment E x y

lemma segment_def (x y : PE) : [x, y][E] = (λ t : ℝ, t • (y -ᵥ x : E) +ᵥ x) '' I := rfl

lemma mem_segment_iff {x y z : PE} : z ∈ [x, y][E] ↔ ∃ t ∈ I, t • (y -ᵥ x : E) +ᵥ x = z :=
mem_image_iff_bex


lemma segment_symm (x y : PE) : [x, y][E] = [y, x][E] :=
by rw [segment, segment, line_map_swap, image_comp]

lemma left_mem_segment (x y : PE) : x ∈ [x, y][E] :=
⟨0, left_mem_Icc.2 zero_le_one, by simp⟩

lemma right_mem_segment (x y : PE) : y ∈ [x, y][E] :=
segment_symm E y x ▸ left_mem_segment E y x

lemma segment_same (x : PE) : [x, x][E] = {x} :=
set.ext $ λ z, ⟨λ ⟨t, ht, htx⟩,
  by simpa only [add_torsor.vsub_self, smul_zero, add_action.zero_vadd, mem_singleton_iff, eq_comm]
    using htx,
  λ h, mem_singleton_iff.1 h ▸ left_mem_segment E z z⟩

lemma segment_eq_Icc {a b : ℝ} (h : a ≤ b) : [a, b][ℝ] = Icc a b :=
begin
  simp only [segment_def, vsub_eq_sub, vadd_eq_add, smul_eq_mul],
  show ((λ x, x + a) ∘ (λ t, t * (b - a))) '' I = Icc a b,
  rw [image_comp, image_mul_right_Icc (@zero_le_one ℝ _) (sub_nonneg.2 h), image_add_right_Icc],
  simp
end

lemma segment_eq_Icc' (a b : ℝ) : [a, b][ℝ] = Icc (min a b) (max a b) :=
by cases le_total a b; [skip, rw segment_symm]; simp [segment_eq_Icc, *]

lemma segment_eq_interval (a b : ℝ) : segment ℝ a b = interval a b :=
segment_eq_Icc' _ _

variable {E}

lemma mem_segment_translate (a : E) {x b c : PE} :
  a +ᵥ x ∈ [a +ᵥ b, a +ᵥ c][E] ↔ x ∈ [b, c][E] :=
begin
  simp only [segment_def],
  refine exists_congr (λ θ, and_congr iff.rfl _),
  simp [add_action.vadd_comm _ _ _ a],
end

lemma segment_translate_preimage (a : E) (b c : PE) :
  (λ x, a +ᵥ x) ⁻¹' [a +ᵥ b, a +ᵥ c][E] = [b, c][E] :=
set.ext $ λ x, mem_segment_translate a

lemma segment_translate_image (a : E) (b c : PE) :
  (λx, a +ᵥ x) '' [b, c][E] = [a +ᵥ b, a +ᵥ c][E] :=
segment_translate_preimage a b c ▸ image_preimage_eq $ (equiv.const_vadd PE a).surjective

variable (E)

/-! ### Convexity of sets -/
/-- A set in an affine space is convex if `∀ x y ∈ s, [x, y] ⊆ s`. We give a longer definition
to be able to apply `(hs : convex E s)` to `(hx : x ∈ s) (hy : y ∈ s) (h0 : 0 ≤ θ) (h1 : θ ≤ 1). -/
def convex (s : set PE) :=
∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) ⦃θ : ℝ⦄ (h0 : 0 ≤ θ) (h1 : θ ≤ 1), θ • (y -ᵥ x : E) +ᵥ x ∈ s

variable {E}

lemma convex_iff_forall_pos :
  convex E s ↔ ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) ⦃θ : ℝ⦄ (h0 : 0 < θ) (h1 : θ < 1),
    θ • (y -ᵥ x : E) +ᵥ x ∈ s :=
begin
  refine ⟨λ h x hx y hy θ h0 h1, h hx hy (le_of_lt h0) (le_of_lt h1), λ h x hx y hy θ h0 h1, _⟩,
  rcases eq_or_lt_of_le h0 with rfl|h0, { simpa using hx },
  rcases eq_or_lt_of_le h1 with rfl|h1, { simpa using hy },
  exact h hx hy h0 h1
end

lemma convex_iff_segment_subset :
  convex E s ↔ ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), [x, y][E] ⊆ s :=
by simp only [convex, segment_def, subset_def, ball_image_iff, mem_Icc, and_imp]

lemma convex.segment_subset (h : convex E s) {x y : PE} (hx : x ∈ s) (hy : y ∈ s) :
  [x, y][E] ⊆ s :=
convex_iff_segment_subset.1 h hx hy

/-! ### Examples of convex sets -/

variables (E PE)

lemma convex_empty : convex E (∅ : set PE) :=  by finish

variables {PE}

lemma convex_singleton (c : PE) : convex E ({c} : set PE) :=
begin
  intros x y hx hy a b ha hb hab,
  rw [set.eq_of_mem_singleton hx, set.eq_of_mem_singleton hy, ←add_smul, hab, one_smul],
  exact mem_singleton c
end

lemma convex_univ : convex (set.univ : set E) := λ _ _ _ _ _ _ _ _ _, trivial

lemma convex.inter {t : set E} (hs: convex s) (ht: convex t) : convex (s ∩ t) :=
λ x y (hx : x ∈ s ∩ t) (hy : y ∈ s ∩ t) a b (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
  ⟨hs hx.left hy.left ha hb hab, ht hx.right hy.right ha hb hab⟩

lemma convex_sInter {S : set (set E)} (h : ∀ s ∈ S, convex s) : convex (⋂₀ S) :=
assume x y hx hy a b ha hb hab s hs,
h s hs (hx s hs) (hy s hs) ha hb hab

lemma convex_Inter {ι : Sort*} {s: ι → set E} (h: ∀ i : ι, convex (s i)) : convex (⋂ i, s i) :=
(sInter_range s) ▸ convex_sInter $ forall_range_iff.2 h

lemma convex.prod {s : set E} {t : set F} (hs : convex s) (ht : convex t) :
  convex (s.prod t) :=
begin
  intros x y hx hy a b ha hb hab,
  apply mem_prod.2,
  exact ⟨hs (mem_prod.1 hx).1 (mem_prod.1 hy).1 ha hb hab,
        ht (mem_prod.1 hx).2 (mem_prod.1 hy).2 ha hb hab⟩
end

lemma convex.is_linear_image (hs : convex s) {f : E → F} (hf : is_linear_map ℝ f) :
  convex (f '' s) :=
begin
  rintros _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ a b ha hb hab,
  exact ⟨a • x + b • y, hs hx hy ha hb hab, by simp only [hf.add,hf.smul]⟩
end

lemma convex.linear_image (hs : convex s) (f : E →ₗ[ℝ] F) : convex (image f s) :=
hs.is_linear_image f.is_linear

lemma convex.is_linear_preimage {s : set F} (hs : convex s) {f : E → F} (hf : is_linear_map ℝ f) :
  convex (preimage f s) :=
begin
  intros x y hx hy a b ha hb hab,
  convert hs hx hy ha hb hab,
  simp only [mem_preimage, hf.add, hf.smul]
end

lemma convex.linear_preimage {s : set F} (hs : convex s) (f : E →ₗ[ℝ] F) :
  convex (preimage f s) :=
hs.is_linear_preimage f.is_linear

lemma convex.neg (hs : convex s) : convex ((λ z, -z) '' s) :=
hs.is_linear_image is_linear_map.is_linear_map_neg

lemma convex.neg_preimage (hs : convex s) : convex ((λ z, -z) ⁻¹' s) :=
hs.is_linear_preimage is_linear_map.is_linear_map_neg

lemma convex.smul (c : ℝ) (hs : convex s) : convex (c • s) :=
begin
  rw smul_set_eq_image,
  exact hs.is_linear_image (is_linear_map.is_linear_map_smul c)
end

lemma convex.smul_preimage (c : ℝ) (hs : convex s) : convex ((λ z, c • z) ⁻¹' s) :=
hs.is_linear_preimage (is_linear_map.is_linear_map_smul c)

lemma convex.add {t : set E}  (hs : convex s) (ht : convex t) : convex (s + t) :=
by { rw pointwise_add_eq_image, exact (hs.prod ht).is_linear_image is_linear_map.is_linear_map_add }

lemma convex.sub {t : set E}  (hs : convex s) (ht : convex t) :
  convex ((λx : E × E, x.1 - x.2) '' (s.prod t)) :=
(hs.prod ht).is_linear_image is_linear_map.is_linear_map_sub

lemma convex.translate (hs : convex s) (z : E) : convex ((λx, z + x) '' s) :=
begin
  convert (convex_singleton z).add hs,
  ext x,
  simp [set.mem_image, mem_pointwise_add, eq_comm]
end

lemma convex.affinity (hs : convex s) (z : E) (c : ℝ) : convex ((λx, z + c • x) '' s) :=
begin
  convert (hs.smul c).translate z using 1,
  erw [smul_set_eq_image, ←image_comp]
end

lemma convex_real_iff {s : set ℝ} :
  convex s ↔ ∀ {x y}, x ∈ s → y ∈ s → Icc x y ⊆ s :=
begin
  simp only [convex_iff_segment_subset, segment_eq_Icc'],
  split; intros h x y hx hy,
  { cases le_or_lt x y with hxy hxy,
    { simpa [hxy] using h hx hy },
    { simp [hxy] } },
  { apply h; cases le_total x y; simp [*] }
end

lemma convex_Iio (r : ℝ) : convex (Iio r) :=
convex_real_iff.2 $ λ x y hx hy z hz, lt_of_le_of_lt hz.2 hy

lemma convex_Ioi (r : ℝ) : convex (Ioi r) :=
convex_real_iff.2 $ λ x y hx hy z hz, lt_of_lt_of_le hx hz.1

lemma convex_Iic (r : ℝ) : convex (Iic r) :=
convex_real_iff.2 $ λ x y hx hy z hz, le_trans hz.2 hy

lemma convex_Ici (r : ℝ) : convex (Ici r) :=
convex_real_iff.2 $ λ x y hx hy z hz, le_trans hx hz.1

lemma convex_Ioo (r : ℝ) (s : ℝ) : convex (Ioo r s) :=
(convex_Ioi _).inter (convex_Iio _)

lemma convex_Ico (r : ℝ) (s : ℝ) : convex (Ico r s) :=
(convex_Ici _).inter (convex_Iio _)

lemma convex_Ioc (r : ℝ) (s : ℝ) : convex (Ioc r s) :=
(convex_Ioi _).inter (convex_Iic _)

lemma convex_Icc (r : ℝ) (s : ℝ) : convex (Icc r s) :=
(convex_Ici _).inter (convex_Iic _)

lemma convex_segment (a b : E) : convex [a, b] :=
begin
  have : (λ (t : ℝ), a + t • (b - a)) = (λz : E, a + z) ∘ (λt:ℝ, t • (b - a)) := rfl,
  rw [segment_eq_image', this, image_comp],
  refine ((convex_Icc _ _).is_linear_image _).translate _,
  exact is_linear_map.is_linear_map_smul' _
end

lemma convex_halfspace_lt {f : E → ℝ} (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | f w < r} :=
(convex_Iio r).is_linear_preimage h

lemma convex_halfspace_le {f : E → ℝ} (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | f w ≤ r} :=
(convex_Iic r).is_linear_preimage h

lemma convex_halfspace_gt {f : E → ℝ} (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | r < f w} :=
(convex_Ioi r).is_linear_preimage h

lemma convex_halfspace_ge {f : E → ℝ} (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | r ≤ f w} :=
(convex_Ici r).is_linear_preimage h

lemma convex_hyperplane {f : E → ℝ} (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | f w = r} :=
begin
  show convex (f ⁻¹' {p | p = r}),
  rw set_of_eq_eq_singleton,
  exact (convex_singleton r).is_linear_preimage h
end

lemma convex_halfspace_re_lt (r : ℝ) : convex {c : ℂ | c.re < r} :=
convex_halfspace_lt (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_le (r : ℝ) : convex {c : ℂ | c.re ≤ r} :=
convex_halfspace_le (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_gt (r : ℝ) : convex {c : ℂ | r < c.re } :=
convex_halfspace_gt (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_lge (r : ℝ) : convex {c : ℂ | r ≤ c.re} :=
convex_halfspace_ge (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_im_lt (r : ℝ) : convex {c : ℂ | c.im < r} :=
convex_halfspace_lt (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_le (r : ℝ) : convex {c : ℂ | c.im ≤ r} :=
convex_halfspace_le (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_gt (r : ℝ) : convex {c : ℂ | r < c.im } :=
convex_halfspace_gt (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_lge (r : ℝ) : convex {c : ℂ | r ≤ c.im} :=
convex_halfspace_ge (is_linear_map.mk complex.add_im complex.smul_im) _

section submodule

open submodule

lemma submodule.convex (K : submodule ℝ E) : convex (↑K : set E) :=
by { repeat {intro}, refine add_mem _ (smul_mem _ _ _) (smul_mem _ _ _); assumption }

lemma subspace.convex (K : subspace ℝ E) : convex (↑K : set E) := K.convex

end submodule

end sets

section functions

local notation `[`x `, ` y `]` := segment x y

/-! ### Convex functions -/

/-- Convexity of functions -/
def convex_on (s : set E) (f : E → ℝ) : Prop :=
  convex s ∧
  ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ a * f x + b * f y

variables {t : set E} {f g : E → ℝ}

lemma convex_on_iff_div:
  convex_on s f ↔ convex s ∧ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀  ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → 0 < a + b →
    f ((a/(a+b)) • x + (b/(a+b)) • y) ≤ (a/(a+b)) * f x + (b/(a+b)) * f y :=
and_congr iff.rfl
⟨begin
  intros h x y hx hy a b ha hb hab,
  apply h hx hy (div_nonneg ha hab) (div_nonneg hb hab),
  rw [←add_div],
  exact div_self (ne_of_gt hab)
end,
begin
  intros h x y hx hy a b ha hb hab,
  simpa [hab, zero_lt_one] using h hx hy ha hb,
end⟩

/-- For a function on a convex set in a linear ordered space, in order to prove that it is convex
it suffices to verify the inequality `f (a • x + b • y) ≤ a * f x + b * f y` only for `x < y`
and positive `a`, `b`. The main use case is `E = ℝ` however one can apply it, e.g., to `ℝ^n` with
lexicographic order. -/
lemma linear_order.convex_on_of_lt [linear_order E] (hs : convex s)
  (hf : ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x < y → ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 →
    f (a • x + b • y) ≤ a * f x + b * f y) : convex_on s f :=
begin
  use hs,
  intros x y hx hy a b ha hb hab,
  wlog hxy : x<=y using [x y a b, y x b a],
  { exact le_total _ _ },
  { cases eq_or_lt_of_le hxy with hxy hxy,
      by { subst y, rw [← add_smul, ← add_mul, hab, one_smul, one_mul] },
    cases eq_or_lt_of_le ha with ha ha,
      by { subst a, rw [zero_add] at hab, subst b, simp },
    cases eq_or_lt_of_le hb with hb hb,
      by { subst b, rw [add_zero] at hab, subst a, simp },
    exact hf hx hy hxy ha hb hab }
end

/-- For a function `f` defined on a convex subset `D` of `ℝ`, if for any three points `x<y<z`
the slope of the secant line of `f` on `[x, y]` is less than or equal to the slope
of the secant line of `f` on `[x, z]`, then `f` is convex on `D`. This way of proving convexity
of a function is used in the proof of convexity of a function with a monotone derivative. -/
lemma convex_on_real_of_slope_mono_adjacent {s : set ℝ} (hs : convex s) {f : ℝ → ℝ}
  (hf : ∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
    (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :
  convex_on s f :=
linear_order.convex_on_of_lt hs
begin
  assume x z hx hz hxz a b ha hb hab,
  let y := a * x + b * z,
  have hxy : x < y,
  { rw [← one_mul x, ← hab, add_mul],
    exact add_lt_add_left ((mul_lt_mul_left hb).2 hxz) _ },
  have hyz : y < z,
  { rw [← one_mul z, ← hab, add_mul],
    exact add_lt_add_right ((mul_lt_mul_left ha).2 hxz) _ },
  have : (f y - f x) * (z - y) ≤ (f z - f y) * (y - x),
    from (div_le_div_iff (sub_pos.2 hxy) (sub_pos.2 hyz)).1 (hf hx hz hxy hyz),
  have A : z - y + (y - x) = z - x, by abel,
  have B : 0 < z - x, from sub_pos.2 (lt_trans hxy hyz),
  rw [sub_mul, sub_mul, sub_le_iff_le_add', ← add_sub_assoc, le_sub_iff_add_le, ← mul_add, A,
    ← le_div_iff B, add_div, mul_div_assoc, mul_div_assoc,
    mul_comm (f x), mul_comm (f z)] at this,
  rw [eq_comm, ← sub_eq_iff_eq_add] at hab; subst a,
  convert this; symmetry; simp only [div_eq_iff (ne_of_gt B), y]; ring
end

lemma convex_on.subset (h_convex_on : convex_on t f) (h_subset : s ⊆ t) (h_convex : convex s) :
  convex_on s f :=
begin
  apply and.intro h_convex,
  intros x y hx hy,
  exact h_convex_on.2 (h_subset hx) (h_subset hy),
end

lemma convex_on.add (hf : convex_on s f) (hg : convex_on s g) : convex_on s (λx, f x + g x) :=
begin
  apply and.intro hf.1,
  intros x y hx hy a b ha hb hab,
  calc
    f (a • x + b • y) + g (a • x + b • y) ≤ (a * f x + b * f y) + (a * g x + b * g y)
      : add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
    ... = a * f x + a * g x + b * f y + b * g y : by linarith
    ... = a * (f x + g x) + b * (f y + g y) : by simp [mul_add, add_assoc]
end

lemma convex_on.smul {c : ℝ} (hc : 0 ≤ c) (hf : convex_on s f) : convex_on s (λx, c * f x) :=
begin
  apply and.intro hf.1,
  intros x y hx hy a b ha hb hab,
  calc
    c * f (a • x + b • y) ≤ c * (a * f x + b * f y)
      : mul_le_mul_of_nonneg_left (hf.2 hx hy ha hb hab) hc
    ... = a * (c * f x) + b * (c * f y) : by rw mul_add; ac_refl
end

lemma convex_on.le_on_segment' {x y : E} {a b : ℝ}
  (hf : convex_on s f) (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  f (a • x + b • y) ≤ max (f x) (f y) :=
calc
  f (a • x + b • y) ≤ a * f x + b * f y : hf.2 hx hy ha hb hab
  ... ≤ a * max (f x) (f y) + b * max (f x) (f y) :
    add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha) (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
  ... ≤ max (f x) (f y) : by rw [←add_mul, hab, one_mul]

lemma convex_on.le_on_segment (hf : convex_on s f) {x y z : E}
  (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ [x, y]) :
  f z ≤ max (f x) (f y) :=
let ⟨a, b, ha, hb, hab, hz⟩ := hz in hz ▸ hf.le_on_segment' hx hy ha hb hab

lemma convex_on.convex_le (hf : convex_on s f) (r : ℝ) : convex {x ∈ s | f x ≤ r} :=
convex_iff_segment_subset.2 $ λ x y hx hy z hz,
  ⟨hf.1.segment_subset hx.1 hy.1 hz,
    le_trans (hf.le_on_segment hx.1 hy.1 hz) $ max_le hx.2 hy.2⟩

lemma convex_on.convex_lt (hf : convex_on s f) (r : ℝ) : convex {x ∈ s | f x < r} :=
convex_iff_segment_subset.2 $ λ x y hx hy z hz,
  ⟨hf.1.segment_subset hx.1 hy.1 hz,
    lt_of_le_of_lt (hf.le_on_segment hx.1 hy.1 hz) $ max_lt hx.2 hy.2⟩

lemma convex_on.convex_epigraph (hf : convex_on s f) :
  convex {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
begin
  rintros ⟨x, r⟩ ⟨y, t⟩ ⟨hx, hr⟩ ⟨hy, ht⟩ a b ha hb hab,
  refine ⟨hf.1 hx hy ha hb hab, _⟩,
  calc f (a • x + b • y) ≤ a * f x + b * f y : hf.2 hx hy ha hb hab
  ... ≤ a * r + b * t : add_le_add (mul_le_mul_of_nonneg_left hr ha)
    (mul_le_mul_of_nonneg_left ht hb)
end

lemma convex_on_iff_convex_epigraph : convex_on s f ↔ convex {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
begin
  refine ⟨convex_on.convex_epigraph, λ h, ⟨_, _⟩⟩,
  { assume x y hx hy a b ha hb hab,
    exact (@h (x, f x) (y, f y) ⟨hx, le_refl _⟩ ⟨hy, le_refl _⟩ a b ha hb hab).1 },
  { assume x y hx hy a b ha hb hab,
    exact (@h (x, f x) (y, f y) ⟨hx, le_refl _⟩ ⟨hy, le_refl _⟩ a b ha hb hab).2 }
end

end functions

section center_mass

/-- Center mass of a finite collection of points with prescribed weights.
Note that we require neither `0 ≤ w i` nor `∑ w = 1`. -/
noncomputable def finset.center_mass (t : finset ι) (w : ι → ℝ) (z : ι → E) : E :=
(t.sum w)⁻¹ • (t.sum (λ i, w i • z i))

variables (i j : ι) (c : ℝ) (t : finset ι) (w : ι → ℝ) (z : ι → E)

open finset

lemma finset.center_mass_empty : (∅ : finset ι).center_mass w z = 0 :=
by simp only [center_mass, sum_empty, smul_zero]

lemma finset.center_mass_pair (hne : i ≠ j) :
  ({i, j} : finset ι).center_mass w z = (w i / (w i + w j)) • z i + (w j / (w i + w j)) • z j :=
by simp only [center_mass, sum_pair hne, smul_add, (mul_smul _ _ _).symm, div_eq_inv_mul]

variable {w}

lemma finset.center_mass_insert (ha : i ∉ t) (hw : t.sum w ≠ 0) :
  (insert i t).center_mass w z = (w i / (w i + t.sum w)) • z i +
    (t.sum w / (w i + t.sum w)) • t.center_mass w z :=
begin
  simp only [center_mass, sum_insert ha, smul_add, (mul_smul _ _ _).symm],
  congr' 2,
  { apply mul_comm },
  { rw [div_mul_eq_mul_div, mul_inv_cancel hw, one_div_eq_inv] }
end

lemma finset.center_mass_singleton (hw : w i ≠ 0) : ({i} : finset ι).center_mass w z = z i :=
by rw [center_mass, sum_singleton, sum_singleton, ← mul_smul, inv_mul_cancel hw, one_smul]

lemma finset.center_mass_eq_of_sum_1 (hw : t.sum w = 1) :
  t.center_mass w z = t.sum (λ i, w i • z i) :=
by simp only [finset.center_mass, hw, inv_one, one_smul]

lemma finset.center_mass_smul : t.center_mass w (λ i, c • z i) = c • t.center_mass w z :=
by simp only [finset.center_mass, finset.smul_sum, (mul_smul _ _ _).symm, mul_comm c, mul_assoc]

/-- A convex combination of two centers of mass is a center of mass as well. This version
deals with two different index types. -/
lemma finset.center_mass_segment'
  (s : finset ι) (t : finset ι') (ws : ι → ℝ) (zs : ι → E) (wt : ι' → ℝ) (zt : ι' → E)
  (hws : s.sum ws = 1) (hwt : t.sum wt = 1) (a b : ℝ) (hab : a + b = 1):
  a • s.center_mass ws zs + b • t.center_mass wt zt =
    (s.image sum.inl ∪ t.image sum.inr).center_mass
      (sum.elim (λ i, a * ws i) (λ j, b * wt j))
      (sum.elim zs zt) :=
begin
  rw [s.center_mass_eq_of_sum_1 _ hws, t.center_mass_eq_of_sum_1 _ hwt,
    smul_sum, smul_sum, ← finset.sum_sum_elim, finset.center_mass_eq_of_sum_1],
  { congr, ext i, cases i; simp only [sum.elim_inl, sum.elim_inr, mul_smul] },
  { rw [sum_sum_elim, ← mul_sum, ← mul_sum, hws, hwt, mul_one, mul_one, hab] }
end

/-- A convex combination of two centers of mass is a center of mass as well. This version
works if two centers of mass share the set of original points. -/
lemma finset.center_mass_segment
  (s : finset ι) (w₁ w₂ : ι → ℝ) (z : ι → E)
  (hw₁ : s.sum w₁ = 1) (hw₂ : s.sum w₂ = 1) (a b : ℝ) (hab : a + b = 1):
  a • s.center_mass w₁ z + b • s.center_mass w₂ z =
    s.center_mass (λ i, a * w₁ i + b * w₂ i) z :=
have hw : s.sum (λ i, a * w₁ i + b * w₂ i) = 1,
  by simp only [mul_sum.symm, sum_add_distrib, mul_one, *],
by simp only [finset.center_mass_eq_of_sum_1, smul_sum, sum_add_distrib, add_smul, mul_smul, *]

lemma finset.center_mass_ite_eq (hi : i ∈ t) :
  t.center_mass (λ j, if (i = j) then 1 else 0) z = z i :=
begin
  rw [finset.center_mass_eq_of_sum_1],
  transitivity t.sum (λ j, if (i = j) then z i else 0),
  { congr, ext i, split_ifs, exacts [h ▸ one_smul _ _, zero_smul _ _] },
  { rw [sum_ite_eq, if_pos hi] },
  { rw [sum_ite_eq, if_pos hi] }
end

variables {t w}

lemma finset.center_mass_subset {t' : finset ι} (ht : t ⊆ t')
  (h : ∀ i ∈ t', i ∉ t → w i = 0) :
  t.center_mass w z = t'.center_mass w z :=
begin
  rw [center_mass, sum_subset ht h, smul_sum, center_mass, smul_sum],
  apply sum_subset ht,
  assume i hit' hit,
  rw [h i hit' hit, zero_smul, smul_zero]
end

lemma finset.center_mass_filter_ne_zero :
  (t.filter (λ i, w i ≠ 0)).center_mass w z = t.center_mass w z :=
finset.center_mass_subset z (filter_subset _) $ λ i hit hit',
by simpa only [hit, mem_filter, true_and, ne.def, not_not] using hit'

variable {z}

/-- Center mass of a finite subset of a convex set belongs to the set
provided that all weights are non-negative, and the total weight is positive. -/
lemma convex.center_mass_mem (hs : convex s) :
  (∀ i ∈ t, 0 ≤ w i) → (0 < t.sum w) → (∀ i ∈ t, z i ∈ s) → t.center_mass w z ∈ s :=
begin
  refine finset.induction (by simp [lt_irrefl]) (λ i t hi ht h₀ hpos hmem, _) t,
  have zi : z i ∈ s, from hmem _ (mem_insert_self _ _),
  have hs₀ : ∀ j ∈ t, 0 ≤ w j, from λ j hj, h₀ j $ mem_insert_of_mem hj,
  rw [sum_insert hi] at hpos,
  by_cases hsum_t : t.sum w = 0,
  { have ws : ∀ j ∈ t, w j = 0, from (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t,
    have wz : t.sum (λ j, w j • z j) = 0, from sum_eq_zero (λ i hi, by simp [ws i hi]),
    simp only [center_mass, sum_insert hi, wz, hsum_t, add_zero],
    simp only [hsum_t, add_zero] at hpos,
    rw [← mul_smul, inv_mul_cancel (ne_of_gt hpos), one_smul],
    exact zi },
  { rw [finset.center_mass_insert _ _ _ hi hsum_t],
    refine convex_iff_div.1 hs zi (ht hs₀ _ _) _ (sum_nonneg hs₀) hpos,
    { exact lt_of_le_of_ne (sum_nonneg hs₀) (ne.symm hsum_t) },
    { intros j hj, exact hmem j (mem_insert_of_mem hj) },
    { exact h₀ _ (mem_insert_self _ _) } }
end

lemma convex.sum_mem (hs : convex s) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : t.sum w = 1)
  (hz : ∀ i ∈ t, z i ∈ s) :
  t.sum (λ i, w i • z i) ∈ s :=
by simpa only [h₁, center_mass, inv_one, one_smul] using
  hs.center_mass_mem h₀ (h₁.symm ▸ zero_lt_one) hz

lemma convex_iff_sum_mem :
  convex s ↔
    (∀ (t : finset E) (w : E → ℝ),
      (∀ i ∈ t, 0 ≤ w i) → t.sum w = 1 → (∀ x ∈ t, x ∈ s) → t.sum (λx, w x • x) ∈ s ) :=
begin
  refine ⟨λ hs t w hw₀ hw₁ hts, hs.sum_mem hw₀ hw₁ hts, _⟩,
  intros h x y hx hy a b ha hb hab,
  by_cases h_cases: x = y,
  { rw [h_cases, ←add_smul, hab, one_smul], exact hy },
  { convert h {x, y} (λ z, if z = y then b else a) _ _ _,
    { simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl] },
    { simp_intros i hi,
      cases hi; subst i; simp [ha, hb, if_neg h_cases] },
    { simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl, hab] },
    { simp_intros i hi,
      cases hi; subst i; simp [hx, hy, if_neg h_cases] } }
end

/-- Jensen's inequality, `finset.center_mass` version. -/
lemma convex_on.map_center_mass_le {f : E → ℝ} (hf : convex_on s f)
  (h₀ : ∀ i ∈ t, 0 ≤ w i) (hpos : 0 < t.sum w)
  (hmem : ∀ i ∈ t, z i ∈ s) : f (t.center_mass w z) ≤ t.center_mass w (f ∘ z) :=
begin
  have hmem' : ∀ i ∈ t, (z i, (f ∘ z) i) ∈ {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2},
    from λ i hi, ⟨hmem i hi, le_refl _⟩,
  convert (hf.convex_epigraph.center_mass_mem h₀ hpos hmem').2;
    simp only [center_mass, function.comp, prod.smul_fst, prod.fst_sum, prod.smul_snd, prod.snd_sum]
end

/-- Jensen's inequality, `finset.sum` version. -/
lemma convex_on.map_sum_le {f : E → ℝ} (hf : convex_on s f)
  (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : t.sum w = 1)
  (hmem : ∀ i ∈ t, z i ∈ s) : f (t.sum (λ i, w i • z i)) ≤ t.sum (λ i, w i * (f (z i))) :=
by simpa only [center_mass, h₁, inv_one, one_smul]
  using hf.map_center_mass_le h₀ (h₁.symm ▸ zero_lt_one) hmem

/-- If a function `f` is convex on `s` takes value `y` at the center mass of some points
`z i ∈ s`, then for some `i` we have `y ≤ f (z i)`. -/
lemma convex_on.exists_ge_of_center_mass {f : E → ℝ} (h : convex_on s f)
  (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hws : 0 < t.sum w) (hz : ∀ i ∈ t, z i ∈ s) :
  ∃ i ∈ t, f (t.center_mass w z) ≤ f (z i) :=
begin
  set y := t.center_mass w z,
  have : f y ≤ t.center_mass w (f ∘ z) := h.map_center_mass_le hw₀ hws hz,
  rw ← sum_filter_ne_zero at hws,
  rw [← finset.center_mass_filter_ne_zero (f ∘ z), center_mass, smul_eq_mul,
    ← div_eq_inv_mul, le_div_iff hws, mul_sum] at this,
  replace : ∃ i ∈ t.filter (λ i, w i ≠ 0), f y * w i ≤ w i • (f ∘ z) i :=
    exists_le_of_sum_le (nonempty_of_sum_ne_zero (ne_of_gt hws)) this,
  rcases this with ⟨i, hi, H⟩,
  rw [mem_filter] at hi,
  use [i, hi.1],
  simp only [smul_eq_mul, mul_comm (w i)] at H,
  refine (mul_le_mul_right _).1 H,
  exact lt_of_le_of_ne (hw₀ i hi.1) hi.2.symm
end

end center_mass

section convex_hull

variable {t : set E}

/-- Convex hull of a set `s` is the minimal convex set that includes `s` -/
def convex_hull (s : set E) : set E :=
⋂ (t : set E) (hst : s ⊆ t) (ht : convex t), t

variable (s)

lemma subset_convex_hull : s ⊆ convex_hull s :=
set.subset_Inter $ λ t, set.subset_Inter $ λ hst, set.subset_Inter $ λ ht, hst

lemma convex_convex_hull : convex (convex_hull s) :=
convex_Inter $ λ t, convex_Inter $ λ ht, convex_Inter id

variable {s}

lemma convex_hull_min (hst : s ⊆ t) (ht : convex t) : convex_hull s ⊆ t :=
set.Inter_subset_of_subset t $ set.Inter_subset_of_subset hst $ set.Inter_subset _ ht

lemma convex_hull_mono (hst : s ⊆ t) : convex_hull s ⊆ convex_hull t :=
convex_hull_min (set.subset.trans hst $ subset_convex_hull t) (convex_convex_hull t)

lemma convex.convex_hull_eq {s : set E} (hs : convex s) : convex_hull s = s :=
set.subset.antisymm (convex_hull_min (set.subset.refl _) hs) (subset_convex_hull s)

@[simp]
lemma convex_hull_singleton {x : E} : convex_hull ({x} : set E) = {x} :=
(convex_singleton x).convex_hull_eq

lemma is_linear_map.image_convex_hull {f : E → F} (hf : is_linear_map ℝ f) :
  f '' (convex_hull s) = convex_hull (f '' s) :=
begin
  refine set.subset.antisymm _ _,
  { rw [set.image_subset_iff],
    exact convex_hull_min (set.image_subset_iff.1 $ subset_convex_hull $ f '' s)
      ((convex_convex_hull (f '' s)).is_linear_preimage hf) },
  { exact convex_hull_min (set.image_subset _ $ subset_convex_hull s)
     ((convex_convex_hull s).is_linear_image hf) }
end

lemma linear_map.image_convex_hull (f : E →ₗ[ℝ] F) :
  f '' (convex_hull s) = convex_hull (f '' s) :=
f.is_linear.image_convex_hull

lemma finset.center_mass_mem_convex_hull (t : finset ι) {w : ι → ℝ} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
  (hws : 0 < t.sum w) {z : ι → E} (hz : ∀ i ∈ t, z i ∈ s) :
  t.center_mass w z ∈ convex_hull s :=
(convex_convex_hull s).center_mass_mem hw₀ hws (λ i hi, subset_convex_hull s $ hz i hi)

-- TODO : Do we need other versions of the next lemma?

/-- Convex hull of `s` is equal to the set of all centers of masses of `finset`s `t`, `z '' t ⊆ s`.
This version allows finsets in any type in any universe. -/
lemma convex_hull_eq (s : set E) :
  convex_hull s = {x : E | ∃ (ι : Type u') (t : finset ι) (w : ι → ℝ) (z : ι → E)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : t.sum w = 1) (hz : ∀ i ∈ t, z i ∈ s) , t.center_mass w z = x} :=
begin
  refine subset.antisymm (convex_hull_min _ _) _,
  { intros x hx,
    use [punit, {punit.star}, λ _, 1, λ _, x, λ _ _, zero_le_one,
      finset.sum_singleton, λ _ _, hx],
    simp only [finset.center_mass, finset.sum_singleton, inv_one, one_smul] },
  { rintros x y ⟨ι, sx, wx, zx, hwx₀, hwx₁, hzx, rfl⟩ ⟨ι', sy, wy, zy, hwy₀, hwy₁, hzy, rfl⟩
      a b ha hb hab,
    rw [finset.center_mass_segment' _ _ _ _ _ _ hwx₁ hwy₁ _ _ hab],
    refine ⟨_, _, _, _, _, _, _, rfl⟩,
    { rintros i hi,
      rw [finset.mem_union, finset.mem_image, finset.mem_image] at hi,
      rcases hi with ⟨j, hj, rfl⟩|⟨j, hj, rfl⟩;
        simp only [sum.elim_inl, sum.elim_inr];
        apply_rules [mul_nonneg, hwx₀, hwy₀] },
    { simp [finset.sum_sum_elim, finset.mul_sum.symm, *] },
    { intros i hi,
      rw [finset.mem_union, finset.mem_image, finset.mem_image] at hi,
      rcases hi with ⟨j, hj, rfl⟩|⟨j, hj, rfl⟩;
        simp only [sum.elim_inl, sum.elim_inr]; apply_rules [hzx, hzy] } },
  { rintros _ ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩,
    exact t.center_mass_mem_convex_hull hw₀ (hw₁.symm ▸ zero_lt_one) hz }
end

/-- Maximum principle for convex functions. If a function `f` is convex on the convex hull of `s`,
then `f` can't have a maximum on `convex_hull s` outside of `s`. -/
lemma convex_on.exists_ge_of_mem_convex_hull {f : E → ℝ} (hf : convex_on (convex_hull s) f)
  {x} (hx : x ∈ convex_hull s) : ∃ y ∈ s, f x ≤ f y :=
begin
  rw convex_hull_eq at hx,
  rcases hx with ⟨α, t, w, z, hw₀, hw₁, hz, rfl⟩,
  rcases hf.exists_ge_of_center_mass hw₀ (hw₁.symm ▸ zero_lt_one)
    (λ i hi, subset_convex_hull s (hz i hi)) with ⟨i, hit, Hi⟩,
  exact ⟨z i, hz i hit, Hi⟩
end

lemma finset.convex_hull_eq (s : finset E) :
  convex_hull ↑s = {x : E | ∃ (w : E → ℝ) (hw₀ : ∀ y ∈ s, 0 ≤ w y) (hw₁ : s.sum w = 1),
    s.center_mass w id = x} :=
begin
  refine subset.antisymm (convex_hull_min _ _) _,
  { intros x hx,
    rw [finset.mem_coe] at hx,
    refine ⟨_, _, _, finset.center_mass_ite_eq _ _ _ hx⟩,
    { intros, split_ifs, exacts [zero_le_one, le_refl 0] },
    { rw [finset.sum_ite_eq, if_pos hx] } },
  { rintros x y ⟨wx, hwx₀, hwx₁, rfl⟩ ⟨wy, hwy₀, hwy₁, rfl⟩
      a b ha hb hab,
    rw [finset.center_mass_segment _ _ _ _ hwx₁ hwy₁ _ _ hab],
    refine ⟨_, _, _, rfl⟩,
    { rintros i hi,
      apply_rules [add_nonneg, mul_nonneg, hwx₀, hwy₀], },
    { simp only [finset.sum_add_distrib, finset.mul_sum.symm, mul_one, *] } },
  { rintros _ ⟨w, hw₀, hw₁, rfl⟩,
    exact s.center_mass_mem_convex_hull (λ x hx, hw₀ _  hx)
      (hw₁.symm ▸ zero_lt_one) (λ x hx, hx) }
end

lemma set.finite.convex_hull_eq {s : set E} (hs : finite s) :
  convex_hull s = {x : E | ∃ (w : E → ℝ) (hw₀ : ∀ y ∈ s, 0 ≤ w y) (hw₁ : hs.to_finset.sum w = 1),
    hs.to_finset.center_mass w id = x} :=
by simpa only [set.finite.coe_to_finset, set.finite.mem_to_finset, exists_prop]
  using hs.to_finset.convex_hull_eq

lemma convex_hull_eq_union_convex_hull_finite_subsets (s : set E) :
  convex_hull s = ⋃ (t : finset E) (w : ↑t ⊆ s), convex_hull ↑t :=
begin
  refine subset.antisymm _ _,
  { rw [convex_hull_eq.{u}],
    rintros x ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩,
    simp only [mem_Union],
    refine ⟨t.image z, _, _⟩,
    { rw [finset.coe_image, image_subset_iff],
      exact hz },
    { apply t.center_mass_mem_convex_hull hw₀,
      { simp only [hw₁, zero_lt_one] },
      { exact λ i hi, finset.mem_coe.2 (finset.mem_image_of_mem _ hi) } } },
   { exact Union_subset (λ i, Union_subset convex_hull_mono), },
end

lemma is_linear_map.convex_hull_image {f : E → F} (hf : is_linear_map ℝ f) (s : set E) :
  convex_hull (f '' s) = f '' convex_hull s :=
set.subset.antisymm (convex_hull_min (image_subset _ (subset_convex_hull s)) $
  (convex_convex_hull s).is_linear_image hf)
  (image_subset_iff.2 $ convex_hull_min
    (image_subset_iff.1 $ subset_convex_hull _)
    ((convex_convex_hull _).is_linear_preimage hf))

lemma linear_map.convex_hull_image (f : E →ₗ[ℝ] F) (s : set E) :
  convex_hull (f '' s) = f '' convex_hull s :=
f.is_linear.convex_hull_image s

end convex_hull

/-! ### Simplex -/

section simplex

variables (ι) [fintype ι] {f : ι → ℝ}

/-- Standard simplex in the space of functions `ι → ℝ` is the set
of vectors with non-negative coordinates with total sum `1`. -/
def std_simplex (ι : Type*) [fintype ι] : set (ι → ℝ) :=
{ f | (∀ x, 0 ≤ f x) ∧ finset.univ.sum f = 1 }

lemma std_simplex_eq_inter :
  std_simplex ι = (⋂ x, {f | 0 ≤ f x}) ∩ {f | finset.univ.sum f = 1} :=
by { ext f, simp only [std_simplex, set.mem_inter_eq, set.mem_Inter, set.mem_set_of_eq] }

lemma convex_std_simplex : convex (std_simplex ι) :=
begin
  refine λ f g hf hg a b ha hb hab, ⟨λ x, _, _⟩,
  { apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1] },
  { erw [finset.sum_add_distrib, ← finset.smul_sum, ← finset.smul_sum, hf.2, hg.2,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one],
    exact hab }
end

variable {ι}

lemma ite_eq_mem_std_simplex (i : ι) : (λ j, ite (i = j) (1:ℝ) 0) ∈ std_simplex ι :=
⟨λ j, by simp only []; split_ifs; norm_num, by rw [finset.sum_ite_eq, if_pos (finset.mem_univ _)] ⟩

/-- `std_simplex ι` is the convex hull of the canonical basis in `ι → ℝ`. -/
lemma convex_hull_basis_eq_std_simplex :
  convex_hull (range $ λ(i j:ι), if i = j then (1:ℝ) else 0) = std_simplex ι :=
begin
  refine subset.antisymm (convex_hull_min _ (convex_std_simplex ι)) _,
  { rintros _ ⟨i, rfl⟩,
    exact ite_eq_mem_std_simplex i },
  { rintros w ⟨hw₀, hw₁⟩,
    rw [pi_eq_sum_univ w, ← finset.univ.center_mass_eq_of_sum_1 _ hw₁],
    exact finset.univ.center_mass_mem_convex_hull (λ i hi, hw₀ i)
      (hw₁.symm ▸ zero_lt_one) (λ i hi, mem_range_self i) }
end

variable {ι}

/-- Convex hull of a finite set is the image of the standard simplex in `s → ℝ`
under the linear map sending each function `w` to `s.sum (λ x, w x • x)`.

Since we have no sums over finite sets, we use sum over `@finset.univ _ hs.fintype`.
The map is defined in terms of operations on `(s → ℝ) →ₗ[ℝ] ℝ` so that later we will not need
to prove that this map is linear. -/
lemma set.finite.convex_hull_eq_image {s : set E} (hs : finite s) :
  convex_hull s =
    (⇑((@finset.univ _ hs.fintype).sum
      (λ x, (@linear_map.proj ℝ s _ (λ i, ℝ) _ _ x).smul_right x.1))) ''
        (@std_simplex _ hs.fintype) :=
begin
  rw [← convex_hull_basis_eq_std_simplex, ← linear_map.convex_hull_image, ← range_comp, (∘)],
  apply congr_arg,
  convert (subtype.range_val s).symm,
  ext x,
  simp [linear_map.sum_apply, ite_smul, finset.filter_eq]
end

/-- All values of a function `f ∈ std_simplex ι` belong to `[0, 1]`. -/
lemma mem_Icc_of_mem_std_simplex (hf : f ∈ std_simplex ι) (x) :
  f x ∈ I :=
⟨hf.1 x, hf.2 ▸ finset.single_le_sum (λ y hy, hf.1 y) (finset.mem_univ x)⟩

end simplex
