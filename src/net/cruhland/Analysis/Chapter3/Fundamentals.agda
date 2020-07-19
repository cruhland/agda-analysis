open import Data.List using ([]; _∷_)
import Data.List.Membership.DecPropositional as DecMembership
open import Level using (_⊔_; Level) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (setoid)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sets using (SetTheory)
import net.cruhland.axioms.Sets.Finite as FiniteSets
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)

module net.cruhland.Analysis.Chapter3.Fundamentals (ST : SetTheory) where
  open PeanoArithmetic peanoArithmetic using (ℕ; _≡?_)
  open DecMembership {A = ℕ} _≡?_ using () renaming (_∈?_ to _∈ᴸ?_)

  open SetTheory ST using
    (_∈_; _∉_; ES; El; PSet; PSet-Setoid; PU; SA; SS; Setoid)
  open FiniteSets SA ES PU SS using (finite; a∈finite; a∉finite)

  variable
    σ₁ σ₂ α β : Level
    S : Setoid σ₁ σ₂

  ℕ-Setoid : Setoid lzero lzero
  ℕ-Setoid = setoid ℕ

  {- 3.1 Fundamentals -}

  -- Definition 3.1.1. (Informal) We define a _set_ A to be any
  -- unordered collection of objects
  _ : Setoid σ₁ σ₂ → ∀ α → Set (σ₁ ⊔ σ₂ ⊔ lsuc α)
  _ = PSet

  -- e.g., {3, 8, 5, 2} is a set.
  _ : PSet ℕ-Setoid lzero
  _ = finite (3 ∷ 8 ∷ 5 ∷ 2 ∷ [])

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
  _ = a∈finite (toWitness {Q = 3 ∈ᴸ? [12345]} _)

  -- but 7 ∉ {1, 2, 3, 4, 5}.
  _ : 7 ∉ ⟨12345⟩
  _ = a∉finite (toWitnessFalse {Q = 7 ∈ᴸ? [12345]} _)

  -- Axiom 3.1 (Sets are objects). If A is a set, then A is also an
  -- object. In particular, given two sets A and B, it is meaningful to
  -- ask whether A is also an element of B.
  set-in-set? : PSet S α → PSet (PSet-Setoid S α) β → Set β
  set-in-set? A B = A ∈ B
