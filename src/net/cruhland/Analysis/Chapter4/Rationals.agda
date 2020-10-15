module net.cruhland.Analysis.Chapter4.Rationals where

open import Agda.Builtin.FromNat using (Number)
open import Relation.Binary.PropositionalEquality using (refl)
open import net.cruhland.models.Logic using (⊤; ⊥; ¬_)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)

open import net.cruhland.models.Integers peanoArithmetic
  using (_—_; ℤ; number; negative)
  renaming
    ( _≃_ to _≃ᶻ_; _≄_ to _≄ᶻ_; _*_ to _*ᶻ_
    ; ≃-intro to ≃ᶻ-intro; ≃-refl to ≃ᶻ-refl
    )

{- 4.2 The rationals -}

-- Definition 4.2.1. A _rational number_ is an expression of the form
-- a//b, where a and b are integers and b is non-zero; a//0 is not
-- considered to be a rational number. Two rational numbers are
-- considered to be equal, a//b = c//d, if and only if ad = cb. The
-- set of all rational numbers is denoted ℚ.
infix 8 _//_
data ℚ : Set where
  _//_ : (a b : ℤ) → {b ≄ᶻ 0} → ℚ

ℚ-elimᴺ : ℚ → ℤ
ℚ-elimᴺ (a // _) = a

ℚ-elimᴰ : ℚ → ℤ
ℚ-elimᴰ (_ // b) = b

infix 4 _≃_
data _≃_ (p q : ℚ) : Set where
  ≃-intro : ℚ-elimᴺ p *ᶻ ℚ-elimᴰ q ≃ᶻ ℚ-elimᴺ q *ᶻ ℚ-elimᴰ p → p ≃ q

infix 4 _≄_
_≄_ : ℚ → ℚ → Set
p ≄ q = ¬ (p ≃ q)

_ : (3 // 4) {λ ()} ≃ (6 // 8) {λ ()}
_ = ≃-intro ≃ᶻ-refl

_ : (6 // 8) {λ ()} ≃ (-3 // -4) {λ ()}
_ = ≃-intro ≃ᶻ-refl

_ : (3 // 4) {λ ()} ≄ (4 // 3) {λ ()}
_ = λ { (≃-intro ()) }
