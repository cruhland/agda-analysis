open import Data.List using ([]; _∷_)
import Data.List.Membership.DecPropositional as DecMembership
open import Level using (_⊔_; Level) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (DecSetoid)
open import Relation.Binary.PropositionalEquality using (setoid; decSetoid)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sets using (SetTheory)
open import net.cruhland.models.Logic using (_∨_; ∨-introᴸ; ∨-introᴿ)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)

module net.cruhland.Analysis.Chapter3.Fundamentals (ST : SetTheory) where
  open PeanoArithmetic peanoArithmetic using (ℕ; _≡?_)

  open SetTheory ST using
    ( _∈_; _∉_; _≗_; _≗̸_; El; PSet; PSet-Setoid; ≗-refl; Setoid; ≗-sym; ≗-trans
    ; finite; module Memberᴸ; module Subsetᴸ
    )

  variable
    σ₁ σ₂ α β : Level
    S : Setoid σ₁ σ₂

  ℕ-Setoid : Setoid lzero lzero
  ℕ-Setoid = setoid ℕ

  ℕ-DecSetoid : DecSetoid lzero lzero
  ℕ-DecSetoid = decSetoid _≡?_

  open Memberᴸ {DS = ℕ-DecSetoid} using (_∈?_)
  open Subsetᴸ {DS = ℕ-DecSetoid} using (_≗?_)

  {- 3.1 Fundamentals -}

  -- Definition 3.1.1. (Informal) We define a _set_ A to be any
  -- unordered collection of objects
  _ : Setoid σ₁ σ₂ → ∀ α → Set (σ₁ ⊔ σ₂ ⊔ lsuc α)
  _ = PSet

  -- e.g., {3, 8, 5, 2} is a set.
  [3852] = 3 ∷ 8 ∷ 5 ∷ 2 ∷ []
  ⟨3852⟩ : PSet ℕ-Setoid lzero
  ⟨3852⟩ = finite {S = ℕ-Setoid} [3852]

  -- If x is an object, we say that x _is an element of_ A or x ∈ A if
  -- x lies in the collection
  _ : El S → PSet S α → Set α
  _ = _∈_

  -- otherwise we say that x ∉ A.
  _ : El S → PSet S α → Set α
  _ = _∉_

  [12345] = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
  ⟨12345⟩ = finite {S = ℕ-Setoid} [12345]

  -- For instance, 3 ∈ {1, 2, 3, 4, 5}
  _ : 3 ∈ ⟨12345⟩
  _ = toWitness {Q = 3 ∈? [12345]} _

  -- but 7 ∉ {1, 2, 3, 4, 5}.
  _ : 7 ∉ ⟨12345⟩
  _ = toWitnessFalse {Q = 7 ∈? [12345]} _

  -- Axiom 3.1 (Sets are objects). If A is a set, then A is also an
  -- object. In particular, given two sets A and B, it is meaningful to
  -- ask whether A is also an element of B.
  set-in-set? : PSet S α → PSet (PSet-Setoid S α) β → Set β
  set-in-set? A B = A ∈ B

  -- Example 3.1.2. The set {3, {3, 4}, 4} is a set of three distinct
  -- elements, one of which happens to itself be a set of two
  -- elements.
  -- [note] We wrap the elements in a sum type because our sets
  -- require all elements to have the same type. Apart from that, this
  -- set will behave identically to the one given in the example.
  _ : PSet (setoid (ℕ ∨ PSet ℕ-Setoid lzero)) lzero
  _ = finite (∨-introᴸ 3 ∷ ∨-introᴿ (finite (3 ∷ 4 ∷ [])) ∷ ∨-introᴸ 4 ∷ [])

  -- To summarize so far...if x is an object and A is a set, then
  -- either x ∈ A is true or x ∈ A is false.
  -- [note] This statement is not actually correct in type theory, as
  -- it would amount to the relation _∈_ always being decidable. For
  -- specific types (such as finite sets of natural numbers) this is
  -- the case, but it doesn't hold in general. This will have
  -- interesting consequences that we'll have to deal with in later
  -- chapters.

  -- Definition 3.1.4 (Equality of sets). Two sets A and B are
  -- _equal_, A ≗ B, iff every element of A is an element of B and
  -- vice versa.
  _ : {S : Setoid σ₁ σ₂} → PSet S α → PSet S α → Set (σ₁ ⊔ α)
  _ = _≗_

  -- Example 3.1.5
  [34215] = 3 ∷ 4 ∷ 2 ∷ 1 ∷ 5 ∷ []
  _ : ⟨12345⟩ ≗ finite [34215]
  _ = toWitness {Q = [12345] ≗? [34215]} _

  [3315242] = 3 ∷ 3 ∷ 1 ∷ 5 ∷ 2 ∷ 4 ∷ 2 ∷ []
  _ : ⟨12345⟩ ≗ finite [3315242]
  _ = toWitness {Q = [12345] ≗? [3315242]} _

  -- [note] informal examples given prior to Definition 3.1.4
  [2358] = 2 ∷ 3 ∷ 5 ∷ 8 ∷ []
  _ : ⟨3852⟩ ≗ finite [2358]
  _ = toWitness {Q = [3852] ≗? [2358]} _

  [38521] = 3 ∷ 8 ∷ 5 ∷ 2 ∷ 1 ∷ []
  _ : ⟨3852⟩ ≗̸ finite [38521]
  _ = toWitnessFalse {Q = [3852] ≗? [38521]} _

  [385] = 3 ∷ 8 ∷ 5 ∷ []
  _ : ⟨3852⟩ ≗̸ finite [385]
  _ = toWitnessFalse {Q = [3852] ≗? [385]} _

  -- Exercise 3.1.1
  -- One can easily verify that this notion of equality is reflexive,
  -- symmetric, and transitive.
  _ : {A : PSet S α} → A ≗ A
  _ = ≗-refl

  _ : {A B : PSet S α} → A ≗ B → B ≗ A
  _ = ≗-sym

  _ : {A B C : PSet S α} → A ≗ B → B ≗ C → A ≗ C
  _ = ≗-trans
