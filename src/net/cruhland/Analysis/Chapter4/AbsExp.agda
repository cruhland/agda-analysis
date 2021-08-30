open import net.cruhland.axioms.DecEq using (≃-derive)
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.Operators using (-_; _-_)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Literals
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)

module net.cruhland.Analysis.Chapter4.AbsExp where

open import net.cruhland.models.Integers.NatPairDefn peanoArithmetic
  using (integers)
open import net.cruhland.models.Rationals.IntPairImpl peanoArithmetic integers
  as ℚ using (ℚ; abs; dist)

{- 4.3 Absolute value and exponentiation -}

-- Definition 4.3.1 (Absolute value). If x is a rational number, the
-- _absolute value_ |x| of x is defined as follows.

-- If x is positive, then |x| ≔ x.
_ : {x : ℚ} → S.Positive x → abs x ≃ x
_ = ℚ.abs-pos

-- If x is negative, then |x| ≔ -x.
_ : {x : ℚ} → S.Negative x → abs x ≃ - x
_ = ℚ.abs-neg

-- If x is zero, then |x| ≔ 0.
_ : {x : ℚ} → x ≃ 0 → abs x ≃ 0
_ = ℚ.abs-zero

-- Definition 4.3.2 (Distance). Let x and y be rational numbers. The
-- quantity |x - y| is called the _distance between x and y_ and is
-- sometimes denoted d(x,y), thus d(x,y) ≔ |x - y|.
_ : {x y : ℚ} → dist x y ≃ abs (x - y)
_ = Eq.refl

-- For instance, d(3,5) = 2.
_ : dist 3 5 ≃ 2
_ = ≃-derive
