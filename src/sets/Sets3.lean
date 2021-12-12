/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, example sheet 3 : not in (`∉`)

The definition in Lean of `x ∉ A` is `¬ (x ∈ A)`. In other words,
`x ∉ A`, `¬ (x ∈ A)` and `(x ∈ A) → false` are all equal *by definition*
in Lean. This means that they are all interchangeable, and you can
change between them using the `change` tactic, or you can just keep this
in mind. For example, if you have a hypothesis `h : x ∉ A` and your goal
is `false`, then `apply h` will work and will change the goal to `x ∈ A`.

## Tactics

You can do all these levels just with `intros`, `apply` and `exact`!

-/

open set

variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

example : x ∉ A → (x ∈ A → false) :=
begin
  intro h,
  exact h,
end

example : x ∈ A → (x ∉ A → false) :=     /-attention!-/
begin
  intro h,
  intro h1,
  apply h1,
  exact h,
end

example : (∀ t, t ∈ A → t ∈ B) → x ∉ B → x ∉ A :=
begin
  intros h2 h1,
  specialize h2 x,
  by_cases (x ∈ A),
  have h3: x ∈ B, by exact h2 h,
  trivial,
  exact h,
end

example : x ∉ (∅ : set X) :=
begin
  change x ∈ ∅ → false,
  intro h,
  exact h,
end
