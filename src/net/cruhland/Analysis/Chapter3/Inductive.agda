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
