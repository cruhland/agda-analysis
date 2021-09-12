open import net.cruhland.axioms.DecEq using (≃-derive)
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.Operators using (_+_; -_; _-_; _≤_; _≥_)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (_↔_; ↔-intro)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)

module net.cruhland.Analysis.Chapter4.AbsExp where

open import net.cruhland.models.Integers.NatPairDefn peanoArithmetic
  using (integers)
open import net.cruhland.models.Rationals.IntPairImpl peanoArithmetic integers
  as ℚ using (ℚ)

{- 4.3 Absolute value and exponentiation -}

-- Definition 4.3.1 (Absolute value). If x is a rational number, the
-- _absolute value_ |x| of x is defined as follows.

-- If x is positive, then |x| ≔ x.
_ : {x : ℚ} → S.Positive x → ℚ.abs x ≃ x
_ = ℚ.abs[q]≃q-from-pos[q]

-- If x is negative, then |x| ≔ -x.
_ : {x : ℚ} → S.Negative x → ℚ.abs x ≃ - x
_ = ℚ.abs[q]≃[-q]-from-neg[q]

-- If x is zero, then |x| ≔ 0.
_ : {x : ℚ} → x ≃ 0 → ℚ.abs x ≃ 0
_ = ℚ.abs[q]≃0-from-q≃0

-- Definition 4.3.2 (Distance). Let x and y be rational numbers. The
-- quantity |x - y| is called the _distance between x and y_ and is
-- sometimes denoted d(x,y), thus d(x,y) ≔ |x - y|.
_ : {x y : ℚ} → ℚ.dist x y ≃ ℚ.abs (x - y)
_ = Eq.refl

-- For instance, d(3,5) = 2.
_ : ℚ.dist 3 5 ≃ 2
_ = ≃-derive

-- Exercise 4.3.1
-- Proposition 4.3.3 (Basic properties of absolute value and
-- distance). Let x, y, z be rational numbers.

-- (a) (Non-degeneracy of absolute value) We have |x| ≥ 0.
abs≥0 : {x : ℚ} → ℚ.abs x ≥ 0
abs≥0 {x} = ℚ.abs≥0 {x}

-- Also, |x| = 0 if and only if x is 0.
abs[x]≃0↔x≃0 : {x : ℚ} → ℚ.abs x ≃ 0 ↔ x ≃ 0
abs[x]≃0↔x≃0 {x} = ↔-intro (ℚ.q≃0-from-abs[q]≃0 {x}) ℚ.abs[q]≃0-from-q≃0

-- (b) (Triangle inequality for absolute value)
-- We have |x + y| ≤ |x| + |y|.
abs-triangle : {x y : ℚ} → ℚ.abs (x + y) ≤ ℚ.abs x + ℚ.abs y
abs-triangle {x} {y} = ℚ.abs-triangle {x} {y}
