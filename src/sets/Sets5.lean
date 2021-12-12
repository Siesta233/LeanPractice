/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 5 : subset (`⊆`), union (`∪`) and intersection (`∩`)

In this sheet we learn how to manipulate `⊆`, `∪` and `∩` in Lean.

Here are some mathematical facts:

`A ⊆ B` is equivalent to `∀ x, x ∈ A → x ∈ B`;
`x ∈ A ∪ B` is equivalent to `x ∈ A ∨ x ∈ B`;
`x ∈ A ∩ B` is equivalent to `x ∈ A ∧ x ∈ B`. 

All of these things are true *by definition* in Lean, which means
that you can switch from one to the other with `change`, or you
can just treat something on the left hand side as if it said
what it said on the right hand side.

For example if your goal is `⊢ x ∈ A ∩ B` then you could write
`change x ∈ A ∧ x ∈ B,` to change the goal to `⊢ x ∈ A ∧ x ∈ B`, but you can
also use the `split,` tactic directly, and this will immediately turn the goal
into two goals `⊢ x ∈ A` and `⊢ x ∈ B`.

## New tactics you will need

You don't need to know any new tactics to solve this sheet. I've mentioned
the `change` tactic. You don't have to use it, and if you use it your
proofs will get longer. So in return I'll tell you about two other
tactics, `rcases` and `rintro`, which you don't have to use either
but if you use them they'll make your proofs shorter.

### The `rcases` tactic

`rcases` is a souped-up version of `cases`. It has slightly different
syntax. If you have a hypothesis `h : P ∧ Q` then `cases h with hP hQ,`
and `rcases h with ⟨hP, hQ⟩,` do the same thing. However, if you
have a hypothesis `h : P ∧ Q ∧ R` then Lean interprets it as `P ∧ (Q ∧ R)`
so if you want to destruct it with `cases` you have to do

```
cases h with hP hQR,
cases hQR with hQ hR
```

You can do this all in one go with `rcases h with ⟨hP, hQ, hR⟩,`. The
name `rcases` stands for "recursive cases".

`rcases` can also be used for `or` hypotheses too; here the syntax is that if
we have
```
h : P ∨ Q
```
then `rcases h with (hP | hQ),` will turn our goal into two goals, one with
`hP : P` and the other with `hQ : Q`.

Even better, `rcases` works on `h : false`. Here there are no cases at all!
So `rcases h with ⟨⟩,` solves the goal.

### The `rintro` tactic

It's quite common to find yourself doing `intro` then `cases` or,
more generally, `intro` then `rcases`. The `rintro` tactic does
these both at once! So for example if your goal is

```
⊢ (P ∧ Q) → R
```

then `rintro ⟨hP, hQ⟩,` leaves you at

```
hP : P
hQ : Q
⊢ R
```

i.e. the same as `intro h, cases h with hP hQ,`

You can introduce more than one hypothesis at once -- `rintro` generalises
`intros` as well. For example if your goal is

```
⊢ P → Q ∧ R → S
```

then `rintro hP ⟨hQ, hR⟩,` turns it into

```
hP : P
hQ : Q
hR : R
⊢ S
```

-/

open set

variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

example : A ⊆ A :=
begin
  rintro x h,
  exact h,
end

example : ∅ ⊆ A :=
begin
  rintro x h,
  exfalso, exact h,
end

example : A ⊆ univ :=
begin
  rintro x h,
  trivial,
end

example : A ⊆ B → B ⊆ C → A ⊆ C :=
begin
  rintro h1 h2 x h,
  specialize h1 h,
  specialize h2 h1,
  exact h2,
end

example : A ⊆ A ∪ B :=
begin
  rintro x h,
  change x ∈ A ∨ x ∈ B,
  left, exact h,
end

example : A ∩ B ⊆ A :=
begin
  rintro x h,
  change x ∈ A ∧ x ∈ B at h,
  exact h.1,
end

example : A ⊆ B → A ⊆ C → A ⊆ (B ∩ C) :=
begin
  rintro h1 h2 x h,
  specialize h1 h,
  specialize h2 h,
  change x ∈ B ∧ x ∈ C,
  exact ⟨h1, h2⟩,
end

example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A :=
begin
  rintro h1 h2 x h,
  change x ∈ B ∨ x ∈ C at h,
  cases h with hB hC,
  specialize h1 hB, exact h1,
  specialize h2 hC, exact h2,
end

example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D :=
begin
  rintro h1 h2 x h,
  change x ∈ A ∨ x ∈ C at h,
  change x ∈ B ∨ x ∈ D,
  cases h with hA hC,
  specialize h1 hA,
  left, exact h1,
  specialize h2 hC,
  right, exact h2,
end

example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D :=
begin
  rintro h1 h2 x h,
  change x ∈ A ∧ x ∈ C at h,
  change x ∈ B ∧ x ∈ D,
  rcases h with ⟨hA, hC⟩,
  split,
  specialize h1 hA, exact h1,
  specialize h2 hC, exact h2,
end
