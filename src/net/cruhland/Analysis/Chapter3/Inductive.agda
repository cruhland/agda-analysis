open import net.cruhland.axiomatic.Logic using (LogicBundle)

module net.cruhland.Analysis.Chapter3.Inductive (LB : LogicBundle) where

open LogicBundle LB

-- Inductive datatype approach to defining sets
data ISet : Set where

_∈_ : {A : Set} → A → ISet → Set
x ∈ S = ⊤

_∉_ : {A : Set} → A → ISet → Set
x ∉ S = ¬ (x ∈ S)

-- Axiom 3.1 (Sets are objects). We can ask if one set is an element
-- of another.
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
