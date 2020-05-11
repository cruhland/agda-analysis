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
