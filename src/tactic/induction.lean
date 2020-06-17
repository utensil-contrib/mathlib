/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import control.basic data.sum data.list.defs tactic.basic

/--
After elaboration, Lean does not have non-dependent function types with
unnamed arguments. This means that for the declaration

```lean
inductive test : Type :=
| intro : unit → test
```

the type of `test.intro` becomes

```lean
test.intro : ∀ (a : unit), test
```lean

after elaboration, where `a` is an auto-generated name.

This means that we can't know for sure whether a constructor argument was named
by the user. Hence the following hack: If an argument is non-dependent *and* its
name is `a` or `a_n` for some `n ∈ ℕ`, then we assume that this name was
auto-generated rather than chosen by the user.
-/
library_note "unnamed constructor arguments"


universes u v w


namespace list

variables {α : Type u} {β : Type v}

/-- Auxiliary definition for `foldl_with_index`. -/
def foldl_with_index_aux (f : ℕ → α → β → α) : ℕ → α → list β → α
| _ a [] := a
| i a (b :: l) := foldl_with_index_aux (i + 1) (f i a b) l

/--
Fold a list from left to right as with `foldl`, but the combining function
also receives each element's index.
-/
def foldl_with_index (f : ℕ → α → β → α) (a : α) (l : list β) : α :=
foldl_with_index_aux f 0 a l

/-- Auxiliary definition for `foldr_with_index`. -/
def foldr_with_index_aux (f : ℕ → α → β → β) : ℕ → β → list α → β
| _ b [] := b
| i b (a :: l) := f i a (foldr_with_index_aux (i + 1) b l)

/--
Fold a list from right to left as with `foldr`, but the combining function
also receives each element's index.
-/
def foldr_with_index (f : ℕ → α → β → β) (b : β) (l : list α) : β :=
foldr_with_index_aux f 0 b l

/-- Monadic variant of `foldl_with_index`. -/
def mfoldl_with_index {m : Type u → Type w} [monad m] (f : ℕ → α → β → m α)
  (a : α) (l : list β) : m α :=
l.foldl_with_index (λ i ma b, do a ← ma, f i a b) (pure a)

/-- Monadic variant of `foldr_with_index`. -/
def mfoldr_with_index {m : Type v → Type w} [monad m] (f : ℕ → α → β → m β)
  (b : β) (l : list α) : m β :=
l.foldr_with_index (λ i a mb, do b ← mb, f i a b) (pure b)

/-- The list of indices of a list. `index_list l = [0, ..., length l - 1]`. -/
def index_list : list α → list ℕ := map_with_index (λ i _, i)

def to_rbmap : list α → rbmap ℕ α :=
foldl_with_index (λ i mapp a, mapp.insert i a) (mk_rbmap ℕ α)

def all_some : list (option α) → option (list α)
| [] := some []
| (some x :: xs) := (λ z, x :: z) <$> all_some xs
| (none :: xs) := none

end list


namespace native

@[reducible] meta def rb_multimap (α β : Type) : Type :=
rb_map α (rb_set β)

meta def mk_rb_multimap (α β : Type) [ltα : has_lt α] [ltβ : has_lt β]
  [decidable_rel ((<) : α → α → Prop)]
  : rb_multimap α β :=
mk_rb_map


namespace rb_multimap

variables {α β : Type}

section

variables [has_lt α] [has_lt β] [decidable_rel ((<) : α → α → Prop)]

meta def find (m : rb_multimap α β) (a : α)
  : option (rb_set β) :=
rb_map.find m a

variables [decidable_rel ((<) : β → β → Prop)]

meta def insert (m : rb_multimap α β) (a : α) (b : β) : rb_multimap α β :=
let bs := m.find a in
rb_map.insert m a
  (match bs with
   | none := rb_map.set_of_list [b]
   | (some bs) := bs.insert b
   end)

meta def contains (m : rb_multimap α β) (a : α) (b : β) : bool :=
match m.find a with
| none := false
| (some bs) := bs.contains b
end

end

meta def to_list (m : rb_multimap α β) : list (α × rb_set β) :=
rb_map.to_list m

meta def to_multilist (m : rb_multimap α β) : list (α × list β) :=
(rb_map.to_list m).map (λ ⟨a, bs⟩, ⟨a, bs.to_list⟩)

end rb_multimap


namespace rb_set

variables {α : Type} [has_lt α] [decidable_rel ((<) : α → α → Prop)]

meta def merge (xs ys : rb_set α) : rb_set α :=
rb_set.fold ys xs (λ a xs, xs.insert a)

end rb_set
end native

open native


namespace expr

meta def local_pp_name_option : expr → option name
| (local_const _ n _ _) := some n
| _ := none

meta def local_unique_name_option : expr → option name
| (local_const n _ _ _) := some n
| _ := none

meta def local_names_option : expr → option (name × name)
| (local_const n₁ n₂ _ _) := some (n₁, n₂)
| _ := none

meta def is_local (e : expr) : bool := e.local_unique_name_option.is_some

meta def free_vars (binder_depth : ℕ) (e : expr) : rbtree ℕ :=
e.fold (mk_rbtree ℕ) $ λ e depth vars,
  match e with
  | var n := if n ≥ binder_depth + depth then vars.insert n else vars
  | _ := vars
  end

/-- Given a closed type of the form `∀ (x : T) ... (z : U), V`, this function
returns a tuple `(args, n, V)` where

- `args` is a list containing information about the arguments `x ... z`:
  argument name, binder info, argument type and whether the argument is
  dependent (i.e. whether the rest of the input `expr` depends on it).
- `n` is the length of `args`.
- `V` is the return type.

Given any other expression `e`, this function returns an empty list and `e`.

Note that the type of each argument and the return type all live in a different
contexts. For example, for the input `∀ (x : α) (y : β x) (z : γ x y), δ`,
`decompose_pi` returns `β #0` as the type of `y` and `γ #1 #0` as the type of
`z` -- the two `#0`s do not denote the same thing.
-/
meta def decompose_pi
  : expr → list (name × binder_info × expr × bool) × ℕ × expr
| (pi name binfo T rest) :=
  let (args, n_args, ret) := decompose_pi rest in
  -- NOTE: the following makes this function quadratic in the size of the input
  -- expression.
  let dep := rest.has_var_idx 0 in
  ((name, binfo, T, dep) :: args, n_args + 1, ret)
| e := ([], 0, e)

/-- Given a closed type of the form `∀ (x : T) ... (z : U), V`, this function
returns a tuple `(args, n, V)` where

- `args` is a list containing information about the arguments `x ... z`:
  argument name, binder info, argument type and whether the argument is
  dependent (i.e. whether the rest of the input `expr` depends on it).
- `n` is the length of `args`.
- `V` is the return type.

Given any other expression `e`, this function returns an empty list and `e`.

The input expression is normalised lazily. This means that the returned
expressions are not necessarily in normal form.

Note that the type of each argument and the return type all live in a different
contexts. For example, for the input `∀ (x : α) (y : β x) (z : γ x y), δ`,
`decompose_pi_normalizing` returns `β #0` as the type of `y` and `γ #1 #0`
as the type of `z` -- the two `#0`s do not denote the same thing.
-/
meta def decompose_pi_normalizing
  : expr → tactic (list (name × binder_info × expr × bool) × expr) := λ e, do
  e ← tactic.whnf e,
  match e with
  | (pi n binfo T rest) := do
      (args, ret) ← decompose_pi_normalizing rest,
      -- NOTE: the following makes this function quadratic in the size of the input
      -- expression.
      let dep := rest.has_var_idx 0,
      pure ((n , binfo, T, dep) :: args, ret)
  | _ := pure ([] , e)
  end

/-- Auxiliary function for `decompose_app`. -/
meta def decompose_app_aux : expr → expr × list expr
| (app t u) :=
  let (f , args) := decompose_app_aux t in
  (f , u :: args)
| e := (e , [])

/-- Decomposes a function application. If `e` is of the form `f x ... z`, the
result is `(f, [x, ..., z])`. If `e` is not of this form, the result is
`(e, [])`.
-/
meta def decompose_app (e : expr) : expr × list expr :=
let (f , args) := decompose_app_aux e in
(f , args.reverse)

/-- Auxiliary function for `decompose_app_normalizing`. -/
meta def decompose_app_normalizing_aux : expr → tactic (expr × list expr) := λ e, do
  e ← tactic.whnf e,
  match e with
  | (app t u) := do
      (f , args) ← decompose_app_normalizing_aux t,
      pure (f , u :: args)
  | _ := pure (e , [])
  end

/-- Decomposes a function application. If `e` is of the form `f x ... z`, the
result is `(f, [x, ..., z])`. If `e` is not of this form, the result is
`(e, [])`.

`e` is normalised lazily. This means that the returned expressions are not
necessarily in normal form.
-/
meta def decompose_app_normalizing (e : expr) : tactic (expr × list expr) := do
  (f , args) ← decompose_app_normalizing_aux e,
  pure (f , args.reverse)

/-- Returns the set of variables occurring in `e`. -/
meta def vars (e : expr) : rb_set ℕ :=
e.fold mk_rb_set $ λ e _ occs,
  match e with
  | var n := occs.insert n
  | _ := occs
  end

meta def local_constants (e : expr) : expr_set :=
e.fold mk_expr_set $ λ e _ occs,
  if e.is_local_constant
    then occs.insert e
    else occs

/-- Given an application `e = f x ... z`, this function returns a map
associating each de Bruijn index that occurs in `e` with the application
argument(s) that it occurs in. For instance, if `e = f (#2 + 1) #3 #3` then the
returned map is

    3 -> 1, 2
    2 -> 0

Arguments are counted from zero (as shown above).
-/
meta def application_variable_occurrences (e : expr) : rb_multimap ℕ ℕ :=
let (_, args) := decompose_app e in
let occs := args.map vars in
occs.foldl_with_index
  (λ i occ_map occs, occs.fold occ_map (λ var occ_map, occ_map.insert var i))
  (mk_rb_multimap ℕ ℕ)

end expr


namespace sum

def get_left {α β} : α ⊕ β → option α
| (inl a) := some a
| _ := none

def get_right {α β} : α ⊕ β → option β
| (inr b) := some b
| _ := none

def is_left {α β} (s : α ⊕ β) : bool :=
s.get_left.is_some

def is_right {α β} (s : α ⊕ β) : bool :=
s.get_right.is_some

end sum


namespace parser

def char : parser char :=
sat (λ _, true)

def digit : parser nat := do
  c ← char,
  let c' := c.to_nat - '0'.to_nat,
  if 0 ≤ c' ∧ c' ≤ 9
    then pure c'
    else parser.fail $ "expected a digit, got: " ++ c.to_string

def nat : parser nat := do
  digits ← many1 digit,
  pure $ prod.fst $
    digits.foldr
      (λ digit ⟨sum, magnitude⟩, ⟨sum + digit * magnitude, magnitude * 10⟩)
      ⟨0, 1⟩

end parser


namespace name

open parser

meta def basename : name → name
| anonymous := anonymous
| (mk_string s _) := mk_string s anonymous
| (mk_numeral n _) := mk_numeral n anonymous

/-- See [note unnamed constructor arguments]. -/
meta def likely_generated_name_p : parser unit := do
  str "a",
  optional (ch '_' *> nat),
  pure ()

/-- See [note unnamed constructor arguments]. -/
meta def is_likely_generated_name (n : name) : bool :=
match n with
| anonymous := ff
| mk_numeral _ _ := ff
| mk_string s anonymous := (likely_generated_name_p.run_string s).is_right
| mk_string _ _ := ff
end

end name


namespace tactic

open expr native

meta def open_binder_aux (n : name) (bi : binder_info) (t e : expr)
  : tactic (expr × name × expr) := do
  c_name ← tactic.mk_fresh_name,
  let c := local_const c_name c_name bi t,
  pure $ ⟨e.instantiate_var c, n, c⟩

/--
Given an `e` with `e = ∀ (x : T), U` or `e = λ (x : T), U`, `open_binder e`
returns

- `U[x/c]`, where `c` is a new local constant with type `T`;
- `x` (the binder name);
- `c` (the local constant).

Note that `c` is not introduced into the context, so `U[x/c]` will not
type-check.

Fails if `e` does not start with a pi or lambda.
-/
meta def open_binder : expr → tactic (expr × name × expr)
| (lam n bi t e) := open_binder_aux n bi t e
| (pi  n bi t e) := open_binder_aux n bi t e
| e := fail! "open_binder: expected an expression starting with a pi or lambda, but got:\n{e}"

/--
For an input expression `e = ∀ (x₁ : T₁) ... (xₙ : Tₙ), U`,
`decompose_constructor_type e` returns the following:

- For each `xᵢ`: the name `xᵢ`; a fresh local constant `cᵢ` which
  replaces `xᵢ` in the other returned expressions; and whether `xᵢ` is a
  dependent argument (i.e. whether it occurs in the remainder of `e`).
  The type `Tᵢ` is the type of `cᵢ`.
- The return type `U`.
-/
meta def decompose_constructor_type_pis
  : expr → tactic (list (name × expr × bool) × expr) := λ e, do
  e ← whnf e,
  match e with
  | (pi _ _ _ rest) := do
    -- TODO the next line makes this function quadratic in the size of the
    -- expression.
    let dep := rest.has_var_idx 0,
    ⟨e, pi_name, cnst⟩ ← open_binder e,
    ⟨args, u⟩ ← decompose_constructor_type_pis e,
    pure $ ⟨⟨pi_name, cnst, dep⟩ :: args, u⟩
  | _ := pure ⟨[], e⟩
  end

meta def get_app_fn_const_normalizing : expr → tactic name := λ e, do
  e ← whnf e,
  match e with
  | (const n _) := pure n
  | (app f _) := get_app_fn_const_normalizing f
  | _ := fail! "expected a constant (possibly applied to some arguments), but got:\n{e}"
  end

/--
`fuzzy_type_match t s` is true iff either of the following applies:

- `t` and `s` are definitionally equal.
- `t` and `s` are applications of the same local constant, i.e. we have
  `t = C x₁ ... xₙ` and `s = C y₁ ... yₘ` for some local constant `C`.
-/
-- TODO is this still too strict? What about e.g. (list (fin n) → unit) and
-- (list (fin (n + 1)) → unit)
meta def fuzzy_type_match (t s : expr) : tactic bool :=
  (is_def_eq t s *> pure tt) <|> do
    (some t_const) ← try_core $ get_app_fn_const_normalizing t | pure ff,
    (some s_const) ← try_core $ get_app_fn_const_normalizing s | pure ff,
    pure $ t_const = s_const

/-
TODO doc
Input: The local constants representing the constructor arguments.

Assumption: The input expression has the form `e = C x₁ ... xₙ` where
`C` is a local constant.

Output: A map associating each of the arg local constants `cᵢ` with the set of
indexes `j` such that `cᵢ` appears in `xⱼ` and `xⱼ`'s type fuzzily matches that
of `cᵢ`.
-/
meta def decompose_constructor_type_return (num_params : ℕ) (args : expr_set)
  : expr → tactic (rb_multimap expr ℕ) := λ ret_type, do
  ⟨_, ret_args⟩ ← decompose_app_normalizing ret_type,
  ret_args.mfoldl_with_index
    (λ i occ_map ret_arg, do
      if i < num_params
        then pure occ_map
        else do
          let ret_arg_consts := ret_arg.local_constants,
          ret_arg_consts.mfold occ_map $ λ c occ_map, do
            ret_arg_type ← infer_type ret_arg,
            eq ← fuzzy_type_match c.local_type ret_arg_type,
            pure $ if eq then occ_map.insert c i else occ_map)
    (mk_rb_multimap _ _)

/--
TODO doc
-/
meta def decompose_constructor_type (num_params : ℕ) (e : expr)
  : tactic (list (name × expr × bool × rb_set ℕ)) := do
  ⟨args, ret⟩ ← decompose_constructor_type_pis e,
  let arg_constants := rb_map.set_of_list (args.map (λ ⟨_, c, _⟩, c)),
  index_occs ← decompose_constructor_type_return num_params arg_constants ret,
  pure $ args.map $ λ ⟨n, c, dep⟩,
    let occs := (index_occs.find c).get_or_else mk_rb_map in
    ⟨n, c.local_type, dep, occs⟩

/-- Returns true iff `arg_type` is the local constant named `type_name`
(possibly applied to some arguments). If `arg_type` is the type of an argument
of one of `type_name`'s constructors and this function returns true, then the
constructor argument is a recursive occurrence. -/
meta def is_recursive_constructor_argument (type_name : name) (arg_type : expr)
  : bool :=
let base := arg_type.get_app_fn in
match base with
| (expr.const base _) := base = type_name
| _ := ff
end

@[derive has_reflect]
meta structure constructor_argument_info :=
(aname : name)
(type : expr)
(dependent : bool)
(index_occurrences : list ℕ)

@[derive has_reflect]
meta structure constructor_info :=
(cname : name)
(args : list constructor_argument_info)

@[derive has_reflect]
meta structure inductive_info :=
(iname : name)
(constructors : list constructor_info)
(num_constructors : ℕ)
(type : expr)
(num_params : ℕ)
(num_indices : ℕ)

/-- Gathers information about a constructor from the environment. Fails if `c`
does not refer to a constructor. -/
meta def get_constructor_info (env : environment) (num_params : ℕ) (c : name)
  : tactic constructor_info := do
  when (¬ env.is_constructor c) $ exceptional.fail format!
    "Expected {c} to be a constructor.",
  decl ← env.get c,
  args ← decompose_constructor_type num_params decl.type,
  pure
    { cname := decl.to_name,
      args := args.map_with_index $ λ i ⟨name, type, dep, index_occs⟩,
        ⟨name, type, dep, index_occs.to_list⟩,
    }

/-- Gathers information about an inductive type from the environment. Fails if
`T` does not refer to an inductive type. -/
meta def get_inductive_info (env : environment) (T : name)
  : tactic inductive_info := do
  when (¬ env.is_inductive T) $ exceptional.fail format!
    "Expected {T} to be an inductive type.",
  decl ← env.get T,
  let type := decl.type,
  let num_params := env.inductive_num_params T,
  let num_indices := env.inductive_num_indices T,
  let constructor_names := env.constructors_of T,
  constructors ← constructor_names.mmap
    (get_constructor_info env num_params),
  pure
    { iname := T,
      constructors := constructors,
      num_constructors := constructors.length,
      type := type,
      num_params := num_params,
      num_indices := num_indices }

meta structure eliminee_info :=
(ename : name)
(eexpr : expr)
(type : expr)
(args : rbmap ℕ expr)

meta def get_eliminee_info (ename : name) : tactic eliminee_info := do
  e ← get_local ename,
  type ← infer_type e,
  ⟨f, args⟩ ← type.decompose_app_normalizing,
  pure
    { ename := ename,
      eexpr := e,
      type := type,
      args := args.to_rbmap }

meta structure constructor_argument_naming_info :=
(einfo : eliminee_info)
(iinfo : inductive_info)
(cinfo : constructor_info)
(ainfo : constructor_argument_info)

@[reducible] meta def constructor_argument_naming_rule : Type :=
constructor_argument_naming_info → option name

meta def constructor_argument_naming_rule_rec : constructor_argument_naming_rule := λ i,
if is_recursive_constructor_argument i.iinfo.iname i.ainfo.type
  then some i.einfo.ename
  else none

meta def constructor_argument_naming_rule_named : constructor_argument_naming_rule := λ i,
let arg_name := i.ainfo.aname in
let arg_dep := i.ainfo.dependent in
if ! arg_dep && arg_name.is_likely_generated_name
  then none
  else some arg_name

meta def constructor_argument_naming_rule_index : constructor_argument_naming_rule := λ i,
let index_occs := i.ainfo.index_occurrences in
let eliminee_args := i.einfo.args in
let local_index_instantiations :=
  (index_occs.map (eliminee_args.find >=> expr.local_names_option)).all_some in
-- TODO this needs to be updated when we allow complex indices
match local_index_instantiations with
| none := none
| some [] := none
| some ((uname, ppname) :: is) :=
  if is.all (λ ⟨uname', _⟩, uname' = uname)
    then some ppname
    else none
end

meta def default_constructor_argument_name : name := `x

meta def apply_constructor_argument_naming_rules
  (info : constructor_argument_naming_info)
  (rules : list constructor_argument_naming_rule)
  : name :=
let go : option name → constructor_argument_naming_rule → option name :=
  λ n rule,
    match n with
    | some n := some n
    | none := rule info
    end
in
(rules.foldl go none).get_or_else default_constructor_argument_name

meta def constructor_argument_name (info : constructor_argument_naming_info)
  : name :=
apply_constructor_argument_naming_rules info
  [ constructor_argument_naming_rule_rec
  , constructor_argument_naming_rule_index
  , constructor_argument_naming_rule_named ]

meta def ih_name (arg_name : name) : name :=
mk_simple_name ("ih_" ++ arg_name.to_string)

meta def intro_fresh (n : name) : tactic unit := do
  n ← get_unused_name n,
  intro n,
  pure ()

/--
Reverts all hypotheses except the following:

- `eliminee`
- hypotheses which `eliminee`'s type depends on
- hypotheses whose name appears in `fix`

TODO example
-/
meta def revert_all_except (eliminee : expr) (fix : name_set) : tactic ℕ := do
  eliminee_type ← infer_type eliminee,
  ctx ← local_context,
  to_revert ← ctx.mfilter $ λ hyp, do {
    dep ← kdepends_on eliminee_type hyp,
    pure $ ¬ (dep ∨ hyp = eliminee ∨ fix.contains hyp.local_pp_name)
  },
  revert_lst to_revert

meta def constructor_argument_intros (einfo : eliminee_info)
  (iinfo : inductive_info) (cinfo : constructor_info)
  : tactic unit :=
(cinfo.args.drop iinfo.num_params).mmap' $ λ ainfo, do
  let info : constructor_argument_naming_info := ⟨einfo, iinfo, cinfo, ainfo⟩,
  intro_fresh (constructor_argument_name info)

meta def ih_intros (einfo : eliminee_info) (iinfo : inductive_info)
  (cinfo : constructor_info)
  : tactic unit :=
let rec_args :=
  cinfo.args.filter
    (λ ainfo, is_recursive_constructor_argument iinfo.iname ainfo.type) in
let ih_names :=
  rec_args.map
    (λ ainfo, ih_name $ constructor_argument_name ⟨einfo, iinfo, cinfo, ainfo⟩) in
match ih_names with
| [] := pure ()
| [_] := intro_fresh "ih"
| ns := ns.mmap' intro_fresh
end

meta def constructor_intros (einfo : eliminee_info) (iinfo : inductive_info)
  (cinfo : constructor_info) : tactic unit := do
  constructor_argument_intros einfo iinfo cinfo,
  ih_intros einfo iinfo cinfo

meta def induction'' (eliminee_name : name) (fix : name_set) : tactic unit :=
focus1 $ do
  einfo ← get_eliminee_info eliminee_name,
  let eliminee := einfo.eexpr,
  let eliminee_type := einfo.type,
  let eliminee_args := einfo.args.to_list.map prod.snd,
  env ← get_env,

  -- Find the name of the inductive type
  iname ← do {
    eliminee_type ← whnf_ginductive eliminee_type,
    (expr.const iname _) ← pure $ eliminee_type.get_app_fn,
    guard (env.is_inductive iname),
    pure iname }
  <|> fail format!
    "The type of {eliminee_name} should be an inductive type, but it is {eliminee_type}.",

  iinfo ← get_inductive_info env iname,
  let rec_name := iname ++ "rec_on",
  rec_const ← mk_const rec_name,

  -- TODO We would like to disallow mutual/nested inductive types, since these
  -- have complicated recursors which we probably don't support. However, there
  -- seems to be no way to find out whether an inductive type is mutual/nested.
  -- (`environment.is_ginductive` doesn't seem to work.)

  -- Disallow complex indices (for now)
  guard (eliminee_args.all expr.is_local) <|> fail format!
    ("induction' can only eliminate hypotheses of the form `T x₁ ... xₙ`\n" ++
    "where `T` is an inductive family and the `xᵢ` are local hypotheses."),

  -- Generalise all generalisable hypotheses except those mentioned in a "fixing"
  -- clause.
  num_generalized ← revert_all_except eliminee fix,

  -- Apply the recursor
  interactive.apply ``(%%rec_const %%eliminee),

  -- For each case (constructor):
  focus $ iinfo.constructors.map $ λ cinfo, do {
    -- Clear the eliminated hypothesis
    clear eliminee,

    -- Clear the index args (unless other stuff in the goal depends on them)
    (eliminee_args.drop iinfo.num_params).mmap' (try ∘ clear),
    -- TODO is this the right thing to do? I don't think this necessarily
    -- preserves provability: The args we clear could contain interesting
    -- information, even if nothing else depends on them. Is there a way to avoid
    -- this, i.e. clean up even more conservatively?

    -- Introduce the constructor arguments
    constructor_intros einfo iinfo cinfo,

    -- Introduce any hypotheses we've previously generalised
    intron num_generalized,
    pure ()
  },

  pure ()

end tactic


namespace tactic.interactive

open interactive lean.parser

precedence `fixing`:0

meta def induction'
  (hyp : parse ident)
  (fix : parse (optional (tk "fixing" *> many ident)))
  : tactic unit :=
  tactic.induction'' hyp (name_set.of_list $ fix.get_or_else [])

end tactic.interactive
