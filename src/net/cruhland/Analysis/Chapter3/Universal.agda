open import Level renaming (zero to lzero; suc to lsuc)
open import net.cruhland.axiomatic.Logic using (LogicBundle)
open import net.cruhland.axiomatic.Peano using (PeanoBundle)

module net.cruhland.Analysis.Chapter3.Universal
  (LB : LogicBundle) (PB : PeanoBundle LB) where

open LogicBundle LB
open PeanoBundle PB

-- Exploring how much Agda's Set universes capture the usual notions
-- of set theory.

member : ∀ {α} (A : Set α) → A → Set
member S x = ⊤

infix 9 member
syntax member S x = x ∈ S

_ : zero ∈ ℕ
_ = ⊤-intro

-- We can't write a definition of non-membership, because there's no
-- way to express in Agda that a variable _doesn't have_ some type. We
-- can only say it _does_ have a type.

-- Axiom 3.1 (Sets are objects).
set-in-set? : ∀ {α} → Set α → Set
set-in-set? {α} A = A ∈ Set α
