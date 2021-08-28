import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.DecEq using (_≃?_; ≃-derive; ≄-derive)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_; Eq)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_; _*_; -_; _-_; _⁻¹; _/_)
open import net.cruhland.axioms.Ordering as Ord using (_≤_; _<_; _≥_; _>_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Function using (_∘_; id; it)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic
  using (_∨_; _↔_; ↔-intro; False; contrapositive; _↯_)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)

module net.cruhland.Analysis.Chapter4.Rationals where

private
  open module ℕ = PeanoArithmetic peanoArithmetic using (ℕ)

open import net.cruhland.models.Integers.NatPairDefn peanoArithmetic
  using (integers)
open import net.cruhland.models.Integers.NatPairImpl peanoArithmetic as ℤ
  using (ℤ)

open import net.cruhland.models.Rationals.IntPairImpl peanoArithmetic integers
  as ℚ using (ℚ; _//_)

{- 4.2 The rationals -}

-- Definition 4.2.1. A _rational number_ is an expression of the form
-- a//b, where a and b are integers and b is non-zero; a//0 is not
-- considered to be a rational number. Two rational numbers are
-- considered to be equal, a//b = c//d, if and only if ad = cb. The
-- set of all rational numbers is denoted ℚ.
_ : Set
_ = ℚ

_ : (a b : ℤ) {{_ : b ≄ 0}} → ℚ
_ = _//_

_ : ℚ → ℚ → Set
_ = _≃_ {{ℚ.eq}}

_ :
  ∀ {a b c d} {{_ : b ≄ 0}} {{_ : d ≄ 0}} →
    a // b ≃ c // d ↔ a * d ≃ c * b
_ = ↔-intro ℚ._≃₀_.elim ℚ.≃₀-intro

-- Thus for instance 3//4 = 6//8 = -3//-4, but 3//4 ≠ 4//3.
module _ where
  instance _ = ≄-derive

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

_ : ℚ → ℚ
_ = -_ {{ℚ.neg-dash}}

-- Lemma 4.2.3
_ : {a b₁ b₂ : ℚ} → b₁ ≃ b₂ → b₁ + a ≃ b₂ + a
_ = AA.subst₂ {{r = ℚ.+-substitutiveᴸ}}

+-substᴿ : {a b₁ b₂ : ℚ} → b₁ ≃ b₂ → a + b₁ ≃ a + b₂
+-substᴿ {a} = AA.subst₂ {{r = ℚ.+-substitutiveᴿ}} {b = a}

_ : {a b₁ b₂ : ℚ} → b₁ ≃ b₂ → b₁ * a ≃ b₂ * a
_ = AA.subst₂ {{r = ℚ.*-substitutiveᴸ}}

*-substᴿ : {a b₁ b₂ : ℚ} → b₁ ≃ b₂ → a * b₁ ≃ a * b₂
*-substᴿ {a} = AA.subst₂ {{r = ℚ.*-substitutiveᴿ}} {b = a}

_ : {a₁ a₂ : ℚ} → a₁ ≃ a₂ → - a₁ ≃ - a₂
_ = AA.subst₁ {{r = ℚ.neg-substitutive}}

-- We note that the rational numbers a//1 behave in a manner identical
-- to the integers a:
compat-+ : ∀ {a b} → (a // 1) + (b // 1) ≃ (a + b) // 1
compat-+ {a} = Eq.sym (AA.compat₂ {{r = ℚ.+-compatible-ℤ}} {a})

compat-* : ∀ {a b} → (a // 1) * (b // 1) ≃ (a * b) // 1
compat-* {a} = Eq.sym (AA.compat₂ {{r = ℚ.*-compatible-ℤ}} {a})

_ : ∀ {a} → - (a // 1) ≃ (- a) // 1
_ = Eq.sym (AA.compat₁ {{r = ℚ.neg-compatible-ℤ}})

-- Also, a//1 and b//1 are only equal when a and b are equal.
_ : ∀ {a b} → a // 1 ≃ b // 1 ↔ a ≃ b
_ = ↔-intro fwd rev
  where
    fwd = AA.inject {{r = ℚ.from-ℤ-injective}}
    rev = AA.subst₁ {{r = ℚ.from-ℤ-substitutive}}

-- Because of this, we will identify a with a//1 for each integer a:
-- a ≡ a//1; the above identities then guarantee that the arithmetic
-- of the integers is consistent with the arithmetic of the
-- rationals. Thus just as we embedded the natural numbers inside the
-- integers, we embed the integers inside the rational numbers.
_ : ∀ {a} → (a as ℚ) ≃ a // 1     -- uses ℚ.from-ℤ for (a as ℚ)
_ = ℚ.≃₀-intro Eq.refl

-- In particular, all natural numbers are rational numbers, for
-- instance 0 is equal to 0//1 and 1 is equal to 1//1.
_ : 0 ≃ 0 // 1
_ = ≃-derive

_ : 1 ≃ 1 // 1
_ = ≃-derive

-- Observe that a rational number a//b is equal to 0 = 0//1 if and
-- only if a × 1 = b × 0, i.e., if the numerator a is equal to 0.
_ : {q : ℚ} → q ≃ 0 ↔ ℚ.numerator q ≃ 0
_ = ↔-intro ℚ.q↑≃0-from-q≃0 ℚ.q≃0-from-q↑≃0

--  Thus if a and b are non-zero then so is a//b.
_ : {a b : ℤ} → a ≄ 0 → {{_ : b ≄ 0}} → a // b ≄ 0
_ = λ a≄0 → contrapositive ℚ.q↑≃0-from-q≃0 a≄0

-- We now define a new operation on the rationals: reciprocal.
-- If x = a//b is a non-zero rational (so that a,b ≠ 0) then we
-- define the _reciprocal_ x⁻¹ of x to be the rational number
-- x⁻¹ ≔ b//a.
_ : (q : ℚ) {{_ : q ≄ 0}} → ℚ
_ = _⁻¹ {{ℚ.reciprocal}}

-- It is easy to check that this operation is consistent with our
-- notion of equality: if two rational numbers a//b, a′//b′ are equal,
-- then their reciprocals are also equal.
_ : {q₁ q₂ : ℚ} {{_ : q₁ ≄ 0}} {{_ : q₂ ≄ 0}} → q₁ ≃ q₂ → q₁ ⁻¹ ≃ q₂ ⁻¹
_ = AA.subst₁ {{ℚ.recip-substitutive}}

-- Proposition 4.2.4 (Laws of algebra for rationals)
-- Exercise 4.2.3
+-comm : {x y : ℚ} → x + y ≃ y + x
+-comm {x} = AA.comm {{r = ℚ.+-commutative}} {x}

+-assoc : {x y z : ℚ} → (x + y) + z ≃ x + (y + z)
+-assoc {x} = AA.assoc {{r = ℚ.+-associative}} {x}

_ : {x : ℚ} → x + 0 ≃ x
_ = AA.ident {{r = ℚ.+-identityᴿ}}

_ : {x : ℚ} → 0 + x ≃ x
_ = AA.ident {{r = ℚ.+-identityᴸ}}

+-invᴿ : {x : ℚ} → x + (- x) ≃ 0
+-invᴿ {x} = AA.inv {{r = ℚ.+-inverseᴿ}} {x}

+-invᴸ : {x : ℚ} → (- x) + x ≃ 0
+-invᴸ {x} = AA.inv {{r = ℚ.+-inverseᴸ}} {x}

*-comm : {x y : ℚ} → x * y ≃ y * x
*-comm {x} = AA.comm {{r = ℚ.*-commutative}} {x}

*-assoc : {x y z : ℚ} → (x * y) * z ≃ x * (y * z)
*-assoc {x} = AA.assoc {{r = ℚ.*-associative}} {x}

_ : {x : ℚ} → x * 1 ≃ x
_ = AA.ident {{r = ℚ.*-identityᴿ}}

_ : {x : ℚ} → 1 * x ≃ x
_ = AA.ident {{r = ℚ.*-identityᴸ}}

*-distrib-+ᴸ : {x y z : ℚ} → x * (y + z) ≃ x * y + x * z
*-distrib-+ᴸ {x} = AA.distrib {{r = ℚ.*-distributive-+ᴸ}} {x}

*-distrib-+ᴿ : {x y z : ℚ} → (y + z) * x ≃ y * x + z * x
*-distrib-+ᴿ {x} {y} = AA.distrib {{r = ℚ.*-distributive-+ᴿ}} {x} {y}

_ : {q : ℚ} {{_ : q ≄ 0}} → q * q ⁻¹ ≃ 1
_ = AA.inv {invert = _⁻¹} {{r = ℚ.*-inverseᴿ}}

_ : {q : ℚ} {{_ : q ≄ 0}} → q ⁻¹ * q ≃ 1
_ = AA.inv {invert = _⁻¹} {{r = ℚ.*-inverseᴸ}}

-- We can now define the _quotient_ x/y of two rational numbers x and
-- y, _provided that_ y is non-zero, by the formula x/y ≔ x × y⁻¹.
_ : (x y : ℚ) {{_ : y ≄ 0}} → ℚ
_ = _/_ {{ℚ.div-ℚ}}

-- Thus, for instance:
_ =
  let instance _ = ≄-derive
   in begin
        (3 // 4) / (5 // 6)
      ≃⟨ ℚ.≃₀-intro Eq.refl ⟩
        (3 // 4) * (6 // 5)
      ≃⟨ ℚ.≃₀-intro Eq.refl ⟩
        (3 * 6) // (4 * 5)
      ≃⟨⟩
        18 // 20
      ≃⟨ ℚ.≃₀-intro Eq.refl ⟩
        9 // 10
      ∎

-- Using this formula, it is easy to see that a/b = a//b for every
-- integer a and every non-zero integer b. Thus we can now discard the
-- // notation, and use the more customary a/b instead of a//b.
_ : {a b : ℤ} {{_ : b ≄ 0}} → a / b ≃ a // b
_ = ℚ.a/b≃a//b

-- In a similar spirit, we define subtraction on the rationals by the
-- formula x - y ≔ x + (- y), just as we did with the integers.
_ : ℚ → ℚ → ℚ
_ = _-_ {{r = ℚ.sub-dash}}

-- Definition 4.2.6. A rational number x is said to be _positive_ iff
-- we have x = a/b for some positive integers a and b. It is said to
-- be _negative_ iff we have x = -y for some positive rational y.
_ : ℚ → Set
_ = S.Positive {{r = ℚ.positivity}}

_ : ℚ → Set
_ = S.Negative {{r = ℚ.negativity}}

-- (i.e., x = (- a)/b for some positive integers a and b)
alt-negative :
  {a b : ℤ} → S.Positive a → (pos[b] : S.Positive b) →
  let instance b≄0 = S.pos≄0 pos[b] in S.Negative ((- a) / b)
alt-negative {a} {b} pos[a] pos[b] =
  let instance
        b≄0 = S.pos≄0 pos[b]
      pos[a/b] = ℚ.Positive₀-intro pos[a] pos[b] Eq.refl
      [-a]/b≃-[a/b] = Eq.sym (AA.fnOpCommᴸ {a = a})
   in ℚ.Negative₀-intro pos[a/b] [-a]/b≃-[a/b]

-- Thus for instance, every positive integer is a positive rational
-- number, and every negative integer is a negative rational number,
-- so our new definition is consistent with our old one.
pos[ℚ]-from-pos[ℤ] : {a : ℤ} → S.Positive a → S.Positive (a as ℚ)
pos[ℚ]-from-pos[ℤ] {a} pos[a] =
  let a:ℚ≃a/1 =
        begin
          (a as ℚ)
        ≃⟨⟩
          a // 1
        ≃˘⟨ ℚ.a/b≃a//b ⟩
          a / 1
        ∎
   in ℚ.Positive₀-intro pos[a] ℤ.1-Positive a:ℚ≃a/1

neg[ℚ]-from-neg[ℤ] : {a : ℤ} → S.Negative a → S.Negative (a as ℚ)
neg[ℚ]-from-neg[ℤ] {a} neg[a] =
  let pos[-a] = ℤ.neg-Negative neg[a]
      pos[-a:ℚ] = pos[ℚ]-from-pos[ℤ] pos[-a]
      -[-a:ℚ]≃a:ℚ = Eq.sym AA.inv-involutive
   in ℚ.Negative₀-intro pos[-a:ℚ] -[-a:ℚ]≃a:ℚ

-- Lemma 4.2.7 (Trichotomy of rationals). Let x be a rational
-- number. Then exactly one of the following three statements is true:
-- (a) x is equal to 0. (b) x is a positive rational number. (c) x is
-- a negative rational number.
_ : (x : ℚ) → AA.ExactlyOneOfThree (x ≃ 0) (S.Positive x) (S.Negative x)
_ = S.trichotomy {{r = ℚ.sign-trichotomy}}

-- Definition 4.2.8 (Ordering of the rationals). Let x and y be
-- rational numbers. We say that x > y iff x - y is a positive
-- rational number, and x < y iff x - y is a negative rational
-- number. We write x ≥ y iff either x > y or x = y, and similarly
-- define x ≤ y.
_ : {x y : ℚ} → x > y ↔ S.Positive (x - y)
_ = ↔-intro id id

_ : {x y : ℚ} → x < y ↔ S.Negative (x - y)
_ = ↔-intro id id

_ : {x y : ℚ} → x ≥ y ↔ x > y ∨ x ≃ y
_ = ↔-intro id id

_ : {x y : ℚ} → x ≤ y ↔ x < y ∨ x ≃ y
_ = ↔-intro id id

-- Exercise 4.2.5
-- Proposition 4.2.9 (Basic properties of order on the rationals). Let
-- x, y, z be rational numbers. Then the following properties hold.

-- (a) (Order trichotomy) Exactly one of the three statements x = y,
-- x < y, or x > y is true.
_ : (x y : ℚ) → AA.ExactlyOneOfThree (x ≃ y) (x < y) (x > y)
_ = Ord.trichotomy {{r = ℚ.order-trichotomy}}

-- (b) (Order is anti-symmetric) One has x < y if and only if y > x.
<↔> : {x y : ℚ} → x < y ↔ y > x
<↔> {x} {y} = ↔-intro (Ord.<-flip {x = x}) (Ord.>-flip {x = y})

-- (c) (Order is transitive) If x < y and y < z, then x < z.
<-trans : {x y z : ℚ} → x < y → y < z → x < z
<-trans {x} = Eq.trans {{r = ℚ.<-transitive}} {x}

-- (d) (Addition preserves order) If x < y, then x + z < y + z.
+-pres-< : {x y z : ℚ} → x < y → x + z < y + z
+-pres-< {x} =
  AA.subst₂ {{r = AA.Substitutive²ᶜ.substitutiveᴸ ℚ.<-substitutive-+}} {a₁ = x}

-- (e) (Positive multiplication preserves order) If x < y and z is
-- positive, then xz < yz.
*-pres-< : {x y z : ℚ} {{_ : S.Positive z}} → x < y → x * z < y * z
*-pres-< {x} =
  AA.subst₂ {{r = AA.Substitutive²ᶜ.substitutiveᴸ ℚ.<-substitutive-*}} {a₁ = x}
