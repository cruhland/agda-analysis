module net.cruhland.Analysis.Chapter2 where

open import Agda.Builtin.FromNat using (Number)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import net.cruhland.axiomatic.Peano using (Peano)

module _ {ℕ : Set} {{P : Peano ℕ}} where
  open Peano P

  -- Proposition 2.1.4
  threeProof : ℕ
  threeProof = succ (succ (succ zero))

  threeDigit : ℕ
  threeDigit = 3

  -- Proposition 2.1.6
  4≢0 : 4 ≢ 0
  4≢0 = succ≢zero

  -- Proposition 2.1.8
  6≢2 : 6 ≢ 2
  6≢2 = λ 6≡2 → 4≢0 (succ-inj (succ-inj 6≡2))
