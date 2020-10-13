module net.cruhland.Analysis.Chapter4.Rationals where

open import Agda.Builtin.FromNat using (Number)
open import net.cruhland.models.Logic using (⊤)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)

open import net.cruhland.axioms.Integers peanoArithmetic
  using (ℤ; number)
  renaming (_≄_ to _≄ᶻ_)

{- 4.2 The rationals -}

-- Definition 4.2.1. A _rational number_ is an expression of the form
-- a//b, where a and b are integers and b is non-zero; a//0 is not
-- considered to be a rational number. Two rational numbers are
-- considered to be equal, a//b = c//d, if and only if ad = cb. The
-- set of all rational numbers is denoted ℚ.
data ℚ : Set where
  _//_ : (a b : ℤ) → {b ≄ᶻ 0} → ℚ
