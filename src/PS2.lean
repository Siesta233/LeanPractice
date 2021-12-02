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