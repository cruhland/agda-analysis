open import net.cruhland.axiomatic.Logic using (LogicBundle)

module net.cruhland.Analysis.Chapter3.Synthetic (LB : LogicBundle) where

open LogicBundle LB

-- Attempting to encode sets with postulates as closely to the book as
-- possible

-- Definition 3.1.1 (Informal)
postulate
  SSet : Set
  -- Q: Should we introduce a separate type of Objects?
  -- It would be better as a typeclass so terms of SSet would be included
  _∈_ : {A : Set} → A → SSet → Set

_∉_ : {A : Set} → A → SSet → Set
x ∉ S = ¬ (x ∈ S)

-- Axiom 3.1 (Sets are objects).
set-in-set? : SSet → SSet → Set
set-in-set? A B = A ∈ B
