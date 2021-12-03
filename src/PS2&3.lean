/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 2 : `true` and `false`

We learn about the `true` and `false` propositions.

## Tactics you will need

To solve the levels on this sheet you will need to know all previous
tactics, plus the following two new ones:

* `trivial`
* `exfalso`

### The `trivial` tactic

If your goal is `⊢ true` then `trivial,` will solve it. 

### The `exfalso` tactic

The tactic `exfalso,` turns any goal `⊢ P` into `⊢ false`. 
This is mathematically valid because `false` implies any goal.

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : true :=
begin
  trivial,
end

example : true → true :=
begin
  intro h,
  trivial,
end

example : false → true :=
begin
  trivial,
end

example : false → false :=
begin
  trivial,
end

example : (true → false) → false :=
begin
  intro h,
  exact h trivial,                    /-remember such usage-/
end

example : false → P :=
begin
  trivial,
end

example : true → false → true → false → true → false :=
begin
  intros h1 h2 h3 h4 h5,
  exfalso,
  exact h2,
end

example : P → ((P → false) → false) :=
begin
  intro hP,
  intro hPf,
  exact hPf hP,
end

example : (P → false) → P → Q :=
begin
  intros hPf hP,
  exfalso,
  exact hPf hP,
end

example : (true → false) → P :=
begin
  intro h,
  exfalso,
  exact h trivial,
end

/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# Important : the definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *the same thing* and can be used interchangeably. You can change
from one to the other for free.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `change` (optional)
* `by_contra`
* `by_cases`

### The `change` tactic

The `change` tactic changes a goal to a goal which
is *equal to it by definition*. The example you need to know
is that `¬ P` and `P → false` are equal by definition.

If your goal is `⊢ ¬ P` then `change P → false,` will
change it to `P → false`. Similarly if you have a hypothesis
`h : ¬ P` then `change P → false at h,` will change it to `h : P → false`.

Note that this tactic is just for psychological purposes. If you finish
a proof which uses this tactic, try commenting out the `change` lines
and note that it doesn't break.

### The `by_contra` tactic

If your goal is `⊢ P` and you want to prove it by contradiction,
`by_contra h,` will change the goal to `false` and add a hypothesis
`h : ¬ P`.

### The `by_cases` tactic

If `P : Prop` is a true-false statement then `by_cases hP : P,`
turns your goal into two goals, one with hypothesis `hP : P`
and the other with hypothesis `hP : ¬ P`.

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

example : ¬ P → (P → false) :=
begin
  intro h,
  change P → false at h,
  trivial,
end

example : ¬ true → false :=
begin
  intro h,
  change true → false at h,
  exact h trivial,
end

example : false → ¬ true :=
begin
  intro h,
  change true → false,
  intro ht,
  exact h,
end

example : ¬ false → true :=
begin
  intro h,
  change false → false at h,
  trivial,
end

example : true → ¬ false :=
begin
  intro h,
  change false → false,
  trivial,
end

example : false → ¬ P :=
begin
  intro h,
  change P → false,
  intro P, 
  exact h,
end

example : P → ¬ P → false :=
begin
  intros hP hP',
  change P → false at hP',
  exact hP' hP,
end

example : P → ¬ (¬ P) :=
begin
  intro hP,
  change ¬P → false,
  intro hP',
  change P → false at hP',
  exact hP' hP,
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  intro hPQ,
  intro hQ,
  change Q → false at hQ,
  change P → false,
  intro hP,
  apply hQ,
  exact hPQ hP,
end

example : ¬ ¬ false → false :=
begin
  by_cases false,
  {intro h,
    change ¬ false → false at h,
    exact h,},
  {intro h,
  change ¬ false → false at h,
  exact h_1 h,},
end

example : ¬ ¬ P → P :=
begin
  by_cases P,
  {intro h,
  change ¬ P → false at h,
  exact h},
  {intro h,
  change ¬ P → false at h,
  exfalso,
  exact h_1 h,},
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  intro h,
  intro hP,
  by_contra hP,
  have hP': ¬ P, apply h hP,
  trivial,
end