module net.cruhland.Analysis.Chapter4.Rationals where

open import Agda.Builtin.FromNat using (Number)
open import net.cruhland.axioms.Eq using (_≄ⁱ_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Logic using (⊤; ⊥; ¬_)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)

open import net.cruhland.models.Integers peanoArithmetic
  using (ℤ; eq; number; negative; ≃ᶻ-refl)
  renaming (_≃_ to _≃ᶻ_; _*_ to _*ᶻ_)

{- 4.2 The rationals -}

-- Definition 4.2.1. A _rational number_ is an expression of the form
-- a//b, where a and b are integers and b is non-zero; a//0 is not
-- considered to be a rational number. Two rational numbers are
-- considered to be equal, a//b = c//d, if and only if ad = cb. The
-- set of all rational numbers is denoted ℚ.
infixl 8 _//_
record ℚ : Set where
  constructor _//_
  field
    a b : ℤ
    {{b≄ⁱ0}} : b ≄ⁱ 0

infix 4 _≃_
data _≃_ (p q : ℚ) : Set where
  ≃-intro : let p↑ // p↓ = p ; q↑ // q↓ = q in p↑ *ᶻ q↓ ≃ᶻ q↑ *ᶻ p↓ → p ≃ q

infix 4 _≄_
_≄_ : ℚ → ℚ → Set
p ≄ q = ¬ (p ≃ q)

_ : 3 // 4 ≃ 6 // 8
_ = ≃-intro ≃ᶻ-refl

_ : 6 // 8 ≃ -3 // -4
_ = ≃-intro ≃ᶻ-refl

_ : 3 // 4 ≄ 4 // 3
_ = λ { (≃-intro ()) }
