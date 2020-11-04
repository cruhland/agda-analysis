module net.cruhland.Analysis.Chapter4.Rationals where

-- Needed for positive integer literals
import Agda.Builtin.FromNat as FromNat
open import Relation.Nullary.Decidable using (False)
open import net.cruhland.axioms.DecEq using (_≃?_; ≃-derive; ≄-derive)
open import net.cruhland.axioms.Eq using (_≃_; _≄_; Eq)
open import net.cruhland.axioms.Operators using (_+_; _*_)
-- Needed for positive integer literals
open import net.cruhland.models.Logic using (_↔_; ↔-intro)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)

import net.cruhland.models.Integers peanoArithmetic as ℤ
open ℤ using (ℤ)
import net.cruhland.models.Rationals peanoArithmetic as ℚ
open ℚ using (_//_; ℚ)

{- 4.2 The rationals -}

-- Definition 4.2.1. A _rational number_ is an expression of the form
-- a//b, where a and b are integers and b is non-zero; a//0 is not
-- considered to be a rational number. Two rational numbers are
-- considered to be equal, a//b = c//d, if and only if ad = cb. The
-- set of all rational numbers is denoted ℚ.
_ : Set
_ = ℚ

_ : (a b : ℤ) {{_ : False (b ≃? 0)}} → ℚ
_ = _//_

_ : ℚ → ℚ → Set
_ = _≃_

_ :
  ∀ {a b c d} {{_ : False (b ≃? 0)}} {{_ : False (d ≃? 0)}} →
    a // b ≃ c // d ↔ a * d ≃ c * b
_ = ↔-intro ℚ._≃₀_.elim ℚ.≃₀-intro

-- Thus for instance 3//4 = 6//8 = -3//-4, but 3//4 ≠ 4//3.
_ : 3 // 4 ≃ 6 // 8
_ = ≃-derive

_ : 6 // 8 ≃ -3 // -4
_ = ≃-derive

_ : 3 // 4 ≄ 4 // 3
_ = ≄-derive

-- This is a valid definition of equality.
-- Exercise 4.2.1
_ : Eq ℚ
_ = ℚ.eq

-- Now we need a notion of addition, multiplication, and
-- negation. Again, we will take advantage of our pre-existing
-- knowledge, which tells us that a/b+c/d should equal (ad+bc)/(bd)
-- and that a/b*c/d should equal ac/bd, while -(a/b) equals
-- (-a)/b. Note that if b and d are non-zero, then bd is also
-- non-zero, by Proposition 4.1.8, so the sum or product of two
-- rational numbers remains a rational number.
-- Definition 4.2.2
_ : ℚ → ℚ → ℚ
_ = _+_ {{ℚ.plus}}

_ : ℚ → ℚ → ℚ
_ = _*_ {{ℚ.star}}
