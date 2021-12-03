/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `split`

### The `cases` tactic

If `h : P ∧ Q` is a hypothesis, then `cases h with hP hQ,`
decomposes it into two hypotheses `hP : P` and `hQ : Q`.

### The `split` tactic

If `⊢ P ∧ Q` is in the goal, The `split` tactic will turn it into
two goals, `⊢ P` and `⊢ Q`. NB tactics operate on the first goal only.

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : P ∧ Q → P :=
begin
  intro h,
  cases h with hP hQ,
  apply hP,
  /-intro h, apply h.1-/
end

example : P ∧ Q → Q :=
begin
  intro h,
  apply h.2,
end

example : (P → Q → R) → (P ∧ Q → R) :=
begin
  intro h,
  intro hPQ,
  apply h hPQ.1 hPQ.2,
end

example : P → Q → P ∧ Q :=
begin
  intros hP hQ,
  split,
  apply hP,
  apply hQ,
end

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P :=
begin
  intro h,
  split,
  apply h.2,
  apply h.1,
end

example : P → P ∧ true :=
begin
  intro h,
  split,
  exact h,
  trivial,
end

example : false → P ∧ false :=
begin
  trivial,
end

/-- `∧` is transitive -/
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  intros hPQ hQR,
  split,
  apply hPQ.1,
  apply hQR.2,
end

example : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  intro hPQR,
  intros hP hQ,
  apply hPQR,
  split,
  apply hP,
  apply hQ
end

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

### The `refl` tactic

If your goal is `P ↔ P` then `refl,` will solve it.

### The `rw` tactic

If `h : P ↔ Q` is a hypothesis, you can decompose it
using `cases h with hPQ hQP,`. However, if you keep
it around then you can do `rw h,` which changes all `P`s in the goal to `Q`s.
Variant: `rw h at h2,` will change all `P`s to `Q`s in hypothesis `h2`.

-/

variables (S : Prop)

example : P ↔ P :=
by refl

example : (P ↔ Q) → (Q ↔ P) :=
begin
  intro hPQ,
  split,
  apply hPQ.2,
  apply hPQ.1,
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split,
  {intro hPQ,
  rw hPQ,},
  {intro hQP,
  rw hQP,},
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intros hPQ hQR,
  split,
  {rw[hPQ, hQR], intro h, exact h,},
  {rw[hPQ, hQR], intro h, exact h,},
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split,                                    /-very much the same-/
  {intro h, split, apply h.2, apply h.1,},
  {intro h, split, apply h.2, apply h.1,}
end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,
  {intro hPQR,
  split,
  {apply hPQR.1.1,},
  {split,
  apply hPQR.1.2,
  apply hPQR.2}},
  {intro hPQR,
  split,
  {split,
  apply hPQR.1,
  apply hPQR.2.1},
  apply hPQR.2.2,},
end

example : P ↔ (P ∧ true) :=
begin
  split,
  {intro hP,
  split,
  apply hP,
  trivial,},
  {intro hP',
  apply hP'.1},
end

example : false ↔ (P ∧ false) :=
begin
  split,
  {trivial,},
  {intro h,
  apply h.2}
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  intros hPQ hRS,
  split,
  {intro hPR,
  split,
  rw ←hPQ, apply hPR.1,
  rw ←hRS, apply hPR.2,},
  {intro hQS,
  split,
  rw hPQ, apply hQS.1,
  rw hRS, apply hQS.2,},
end

example : ¬ (P ↔ ¬ P) :=
begin
  by_contra h1,
  by_cases P,
  {have h2: ¬ P, rw h1 at h,
  change P → false at h,
  trivial,
  trivial,},
  {have h2: P, rw ←h1 at h,
  apply h,
  trivial,},
end

/-at: rw h₁ at h₂-/
