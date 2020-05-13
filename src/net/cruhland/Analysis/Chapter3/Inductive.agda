open import net.cruhland.axiomatic.Logic using (LogicBundle)

module net.cruhland.Analysis.Chapter3.Inductive (LB : LogicBundle) where

open LogicBundle LB

{-= Chapter 3: Set theory (inductive datatype approach) =-}

{- 3.1 Fundamentals -}

-- Definition 3.1.1
-- We define a set A to be any unordered collection of objects
data ISet : Set where

-- [todo] e.g. {3,8,5,2} is a set

-- If x is an object, we say that x is an element of A or x ∈ A if x
-- lies in the collection
_∈_ : {A : Set} → A → ISet → Set
x ∈ S = ⊤

-- Otherwise we say that x ∉ A
_∉_ : {A : Set} → A → ISet → Set
x ∉ S = ¬ (x ∈ S)

-- [todo] For instance, 3 ∈ {1,2,3,4,5} but 7 ∉ {1,2,3,4,5}

-- Axiom 3.1 (Sets are objects). If A is a set, then A is also an
-- object. In particular, given two sets A and B, it is meaningful to
-- ask whether A is also an element of B.
set-in-set? : ISet → ISet → Set
set-in-set? A B = A ∈ B

-- [todo] The set {3, {3,4}, 4} is a set of three distinct elements,
-- one of which happens to itself be a set of two elements.

-- Definition 3.1.4 (Equality of sets). Two sets A and B are _equal_,
-- A = B, iff every element of A is an element of B and vice versa.
-- [todo] define once you've made some constructors for the datatype

-- Example 3.1.5
-- [todo] {1,2,3,4,5} and {3,4,2,1,5} are the same set
-- [todo] {3,3,1,5,2,4,2} is equal to {1,2,3,4,5}

-- Exercise 3.1.1
-- Reflexivity, symmetry, and transitivity of equality
-- [todo] prove once you've defined equality

-- Substitution property of equality
-- [todo] ∈-subst: x ∈ A → A ≗ B → x ∈ B
-- [todo] subst-∈: A ∈ 𝒰 → A ≗ B → B ∈ 𝒰

{-
data DSet : Set₁ where
  ∅ : DSet
  atom : {A : Set} → A → DSet
  singleton : DSet → DSet
  pair : DSet → DSet → DSet

_ : DSet
_ = singleton ∅

_ : DSet
_ = singleton (singleton ∅)

_ : DSet
_ = pair ∅ (singleton ∅)
-}
