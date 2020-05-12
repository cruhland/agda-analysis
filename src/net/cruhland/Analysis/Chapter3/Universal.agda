open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
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

-- [todo] The set {3, {3,4}, 4} is a set of three distinct elements,
-- one of which happens to itself be a set of two elements.

-- Definition 3.1.4 (Equality of sets). Two sets A and B are _equal_,
-- A = B, iff every element of A is an element of B and vice versa.

-- [note] it doesn't seem possible in Agda to define an equality
-- relation between two sets. There's no way to "look inside" a
-- generic value of type Set and see what its elements are.
-- But we can attempt to use plain propositional equality:
_≗_ : Set → Set → Set₁
A ≗ B = A ≡ B

-- Example 3.1.5
-- [todo] {1,2,3,4,5} and {3,4,2,1,5} are the same set
-- [todo] {3,3,1,5,2,4,2} is equal to {1,2,3,4,5}

-- Exercise 3.1.1
-- Reflexivity, symmetry, and transitivity of equality
≗-refl : ∀ {A} → A ≗ A
≗-refl = refl

≗-sym : ∀ {A B} → A ≗ B → B ≗ A
≗-sym = sym

≗-trans : ∀ {A B C} → A ≗ B → B ≗ C → A ≗ C
≗-trans = trans
