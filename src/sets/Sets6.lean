/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 6 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal. 

## Tactics 

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open set

variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

example : A ⊆ B → B ⊆ A → A = B :=
begin
  rintro h1 h2,
  ext x,
  split,
  intro h,
  specialize h1 h, exact h1,
  intro h,
  specialize h2 h, exact h2,
end

example : A ∪ A = A :=
begin
  ext,
  split,
  {intro h,
  change x ∈ A ∨ x ∈ A at h,
  cases h, exact h, exact h,},
  intro h,
  change x ∈ A ∨ x ∈ A,
  left, exact h,
end

example : A ∩ A = A :=
begin
  ext,
  split,
  intro h, 
  change x ∈ A ∧ x ∈ A at h,
  exact h.1,
  intro h,
  change x ∈ A ∧ x ∈ A,
  exact ⟨h, h⟩,
end

example : A ∩ B = B ∩ A :=
begin
  ext,
  split,
  intro h,
  change x ∈ A ∧ x ∈ B at h,
  change x ∈ B ∧ x ∈ A,
  rcases h with ⟨hA, hB⟩,
  exact ⟨hB, hA⟩,
  intro h,
  change x ∈ B ∧ x ∈ A at h,
  change x ∈ A ∧ x ∈ B,
  rcases h with ⟨hB, hA⟩,
  exact ⟨hA, hB⟩,
end

example : A ∩ (B ∩ C) = (A ∩ B) ∩ C :=
begin
  ext,
  split,
  intro h,
  rcases h with ⟨hA, hB, hC⟩,
  change x ∈ (A ∩ B) ∧ x ∈ C,
  change (x ∈ A ∧ x ∈ B) ∧ (x ∈ C),
  exact ⟨⟨hA, hB⟩, hC⟩,
  intro h,
  rcases h with ⟨hAB, hC⟩,
  rcases hAB with ⟨hA, hB⟩,
  exact ⟨hA, ⟨hB, hC⟩⟩,
end

example : A ∪ (B ∪ C) = (A ∪ B) ∪ C :=
begin
  ext,
  split,
  {intro h,
  change (x ∈ A ∪ B) ∨ x ∈ C,
  change x ∈ A ∨ (x ∈ B ∪ C) at h,
  cases h,
  left, left, exact h,
  cases h,
  left, right, exact h,
  right, exact h,},
  intro h,
  cases h, cases h,
  left, exact h,
  right, left, exact h,
  right, right, exact h,
end