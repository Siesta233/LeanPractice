/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

### The `left` and `right` tactics.

If your goal is `⊢ P ∨ Q` then `left,` will change it to `⊢ P`
and `right,` will change it to `⊢ Q`.

### The `cases` tactic again

If we have `h : P ∨ Q` as a hypothesis then `cases h with hP hQ`
will turn your goal into two goals, one with `hP : P` as a hypothesis
and the other with `hQ : Q`.

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.

variables (P Q R S : Prop)

example : P → P ∨ Q :=
begin
  intro hP,
  left,
  apply hP,
end

example : Q → P ∨ Q :=
begin
  intro hQ,
  right, apply hQ,
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intros hPQ h₁ h₂,
  cases hPQ with hP hQ,
  apply h₁ hP,
  apply h₂ hQ,
end

-- symmetry of `or`
example : P ∨ Q → Q ∨ P :=
begin
  intro hPQ,
  cases hPQ with hP hQ,
  right,
  exact hP,
  left,
  exact hQ,
end

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  split,
  {intros h,
  cases h with hPQ hR,
  cases hPQ with hP hQ,
  left, apply hP,
  right, left, apply hQ,
  right, right, apply hR,},
  intro h,
  cases h with hP hQR,
  left, left, apply hP,
  cases hQR with hQ hR,
  left, right, apply hQ,
  right, apply hR,
end

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  intros hPR hQS hPQ,
  cases hPQ with hP hQ,
  left,
  apply hPR hP,
  right,
  apply hQS hQ,
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  intros hPQ hPR,
  cases hPR,
  left,
  apply hPQ hPR,
  right, 
  apply hPR,
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  intros hPR hQS,
  split,
  {intro hPQ,
  cases hPQ with hP hQ,
  left, rw ←hPR, apply hP,
  right, rw ←hQS, apply hQ,},
  intro hRS,
  cases hRS,
  left, rw hPR, apply hRS,
  right, rw hQS, apply hRS,
end

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  split,
  {intro h1,
  by_cases P,
  {have hPQ: P ∨ Q, {left, exact h,},
  trivial,},
  split,
  exact h,
  by_cases Q,
  {have hPQ : P ∨ Q, {right, exact h,},
  by_contra hPQ,
  trivial,},
  exact h,
  },
  intro h,
  by_cases P ∨ Q,
  cases h with hP hQ,
  have hP': ¬ P, by exact h.1,
  trivial,                          /-attention!-/
  have hQ': ¬ Q, by exact h.2,
  trivial,
  exact h,
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  split,
  {intro h,
  by_cases P,
  {have hQ : Q ∨ ¬ Q, 
  {by_cases Q, left, exact h, right, exact h},
  cases hQ with hQ hQ',
  {have hPQ : P ∧ Q, {split, exact h, exact hQ,},
  trivial,},
  right, exact hQ',},
  left, exact h,
  },
  intro h,
  cases h with hP' hQ',
  {change P → false at hP',
  have hPQ': P ∧ Q → false,
  {intro h₁, exact hP' h₁.1,},
  trivial,},
  {change Q → false at hQ',
  have hPQ': P ∧ Q → false,
  {intro h₂, exact hQ' h₂.2,},
  trivial,},
end
