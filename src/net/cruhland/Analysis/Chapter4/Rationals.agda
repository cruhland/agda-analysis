module net.cruhland.Analysis.Chapter4.Rationals where

open import Agda.Builtin.FromNat using (Number)
-- Needed for resolving instance arguments
open import Relation.Binary.PropositionalEquality
  using () renaming (refl to ≡-refl)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; _≄ⁱ_; ≄ⁱ-elim; Eq; ≃-intro; ≄-intro)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Logic using (⊤; ⊥; ¬_)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)

open import net.cruhland.models.Integers peanoArithmetic
  using (ℤ; number; negative; ≃ᶻ-refl) renaming (_*_ to _*ᶻ_; eq to eq-ℤ)

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

infix 4 _≃₀_
data _≃₀_ (p q : ℚ) : Set where
  instance
    ≃₀-intro :
      let p↑ // p↓ = p
          q↑ // q↓ = q
       in {{i : p↑ *ᶻ q↓ ≃ q↑ *ᶻ p↓}} → p ≃₀ q

infix 4 _≄₀ⁱ_
data _≄₀ⁱ_ (p q : ℚ) : Set where
  instance
    ≄₀ⁱ-intro :
      let p↑ // p↓ = p
          q↑ // q↓ = q
       in {{i : p↑ *ᶻ q↓ ≄ⁱ q↑ *ᶻ p↓}} → p ≄₀ⁱ q

≄₀ⁱ-elim : ∀ {p q} {{i : p ≄₀ⁱ q}} → ¬ (p ≃₀ q)
≄₀ⁱ-elim {{≄₀ⁱ-intro {{≄ⁱ-ℤ}}}} (≃₀-intro {{≃-ℤ}}) = ≄ⁱ-elim {{i = ≄ⁱ-ℤ}} ≃-ℤ

instance
  eq : Eq ℚ
  eq = record
    { _≃_ = _≃₀_
    ; refl = {!!}
    ; sym = {!!}
    ; trans = {!!}
    ; _≄ⁱ_ = _≄₀ⁱ_
    ; ≄ⁱ-elim = λ {{i}} → ≄₀ⁱ-elim {{i}}
    }

_ : 3 // 4 ≃ 6 // 8
_ = ≃-intro

_ : 6 // 8 ≃ -3 // -4
_ = ≃-intro

_ : 3 // 4 ≄ 4 // 3
_ = ≄-intro
