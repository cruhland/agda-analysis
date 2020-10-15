module net.cruhland.Analysis.Chapter4.Rationals where

open import Agda.Builtin.FromNat using (Number)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Logic using (⊤; ⊥; ¬_; ¬sym)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)

open PeanoArithmetic peanoArithmetic
  using (ℕ; step; zero; step≢zero; step-inj) renaming (number to ℕ-number)
open import net.cruhland.models.Integers peanoArithmetic
  using (_—_; -_; ℤ; ℤ⁺; ℤ⁻; fromℕ; number; negative)
  renaming
    ( _≃_ to _≃ᶻ_; _≄_ to _≄ᶻ_; _*_ to _*ᶻ_
    ; ≃-intro to ≃ᶻ-intro; ≃-refl to ≃ᶻ-refl
    )

{- 4.2 The rationals -}

data _≢ⁱ_ : ℕ → ℕ → Set where
  instance
    z≢s : ∀ {m} → zero ≢ⁱ step m
    s≢z : ∀ {n} → step n ≢ⁱ zero
    s≢s : ∀ {n m} → {{n ≢ⁱ m}} → step n ≢ⁱ step m

≢ⁱ→≢ : ∀ {n m} {{_ : n ≢ⁱ m}} → n ≢ m
≢ⁱ→≢ {{z≢s}} = ¬sym step≢zero
≢ⁱ→≢ {{s≢z}} = step≢zero
≢ⁱ→≢ {{s≢s}} = ≢ⁱ→≢ ∘ step-inj

_≢ᴺ_ : ℕ → ℕ → Set
_≢ᴺ_ = _≢_

_ : 3 ≢ᴺ 5
_ = ≢ⁱ→≢

record NonZero (a : ℤ) : Set where
  field
    {{a⁺≢a⁻}} : ℤ⁺ a ≢ⁱ ℤ⁻ a

_ : NonZero 3
_ = record {}

_ : NonZero 5
_ = record {}

instance
  NonZeroℕ⁺ : ∀ {n} {{_ : n ≢ⁱ 0}} → NonZero (fromℕ n)
  NonZeroℕ⁺ = record {}

  NonZeroℕ⁻ : ∀ {n} {{_ : 0 ≢ⁱ n}} → NonZero (- fromℕ n)
  NonZeroℕ⁻ = record {}

-- Definition 4.2.1. A _rational number_ is an expression of the form
-- a//b, where a and b are integers and b is non-zero; a//0 is not
-- considered to be a rational number. Two rational numbers are
-- considered to be equal, a//b = c//d, if and only if ad = cb. The
-- set of all rational numbers is denoted ℚ.
infix 8 _//_
record ℚ : Set where
  constructor _//_
  field
    a b : ℤ
    {{b≄0}} : NonZero b

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

_ : 3 // 4 ≃ 6 // 8
_ = ≃-intro ≃ᶻ-refl

_ : 6 // 8 ≃ -3 // -4
_ = ≃-intro ≃ᶻ-refl

_ : 3 // 4 ≄ 4 // 3
_ = λ { (≃-intro ()) }
