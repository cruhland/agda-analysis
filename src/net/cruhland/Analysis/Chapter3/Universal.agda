open import Level renaming (zero to lzero; suc to lsuc)
open import net.cruhland.axiomatic.Logic using (LogicBundle)
open import net.cruhland.axiomatic.Peano using (PeanoBundle)

module net.cruhland.Analysis.Chapter3.Universal
  (LB : LogicBundle) (PB : PeanoBundle LB) where

open LogicBundle LB
open PeanoBundle PB

{-= Chapter 3: Set theory (Agda universes approach) =-}

-- (aka, exploring how much Agda's universes capture the usual notions
-- of set theory)

{- 3.1 Fundamentals -}

-- Definition 3.1.1
-- We define a set A to be any unordered collection of objects
-- [note] we will use Agda's Set for this

-- [todo] e.g. {3,8,5,2} is a set

-- If x is an object, we say that x is an element of A or x ∈ A if x
-- lies in the collection
member : ∀ {α} (A : Set α) → A → Set
member S x = ⊤

infix 9 member
syntax member S x = x ∈ S

_ : zero ∈ ℕ
_ = ⊤-intro

-- Otherwise we say that x ∉ A

-- [note] We can't write a definition of non-membership, because
-- there's no way to express in Agda that a variable _doesn't have_
-- some type. We can only say it _does_ have a type.

-- [todo] For instance, 3 ∈ {1,2,3,4,5} but 7 ∉ {1,2,3,4,5}

-- Axiom 3.1 (Sets are objects). If A is a set, then A is also an
-- object. In particular, given two sets A and B, it is meaningful to
-- ask whether A is also an element of B.
set-in-set? : ∀ {α} → Set α → Set
set-in-set? {α} A = A ∈ Set α
