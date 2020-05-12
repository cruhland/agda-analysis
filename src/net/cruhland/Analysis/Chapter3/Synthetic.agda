open import net.cruhland.axiomatic.Logic using (LogicBundle)

module net.cruhland.Analysis.Chapter3.Synthetic (LB : LogicBundle) where

open LogicBundle LB

{-= Chapter 3: Set theory (synthetic axioms approach) =-}

-- (aka, attempting to encode sets with postulates as closely to the
-- book as possible)

{- 3.1 Fundamentals -}

postulate
  -- Definition 3.1.1
  -- We define a set A to be any unordered collection of objects
  SSet : Set
  -- [todo] e.g. {3,8,5,2} is a set

  -- Q: Should we introduce a separate type of Objects?
  -- It would be better as a typeclass so terms of SSet would be included

  -- If x is an object, we say that x is an element of A or x ∈ A if x
  -- lies in the collection
  _∈_ : {A : Set} → A → SSet → Set

-- Otherwise we say that x ∉ A
_∉_ : {A : Set} → A → SSet → Set
x ∉ S = ¬ (x ∈ S)

-- [todo] For instance, 3 ∈ {1,2,3,4,5} but 7 ∉ {1,2,3,4,5}

-- Axiom 3.1 (Sets are objects). If A is a set, then A is also an
-- object. In particular, given two sets A and B, it is meaningful to
-- ask whether A is also an element of B.
set-in-set? : SSet → SSet → Set
set-in-set? A B = A ∈ B

-- [todo] The set {3, {3,4}, 4} is a set of three distinct elements,
-- one of which happens to itself be a set of two elements.

-- Definition 3.1.4 (Equality of sets). Two sets A and B are _equal_,
-- A = B, iff every element of A is an element of B and vice versa.
_≗_ : SSet → SSet → Set₁
A ≗ B = {𝒰 : Set} → (x : 𝒰) → x ∈ A ↔ x ∈ B

-- Example 3.1.5
-- [todo] {1,2,3,4,5} and {3,4,2,1,5} are the same set
-- [todo] {3,3,1,5,2,4,2} is equal to {1,2,3,4,5}

-- Exercise 3.1.1
-- Reflexivity, symmetry, and transitivity of equality
≗-refl : ∀ {A} → A ≗ A
≗-refl = λ x → ↔-refl

≗-sym : ∀ {A B} → A ≗ B → B ≗ A
≗-sym A≗B = λ x → ↔-sym (A≗B x)

≗-trans : ∀ {A B C} → A ≗ B → B ≗ C → A ≗ C
≗-trans A≗B B≗C = λ x → ↔-trans (A≗B x) (B≗C x)
