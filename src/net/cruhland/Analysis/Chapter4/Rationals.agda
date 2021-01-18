module net.cruhland.Analysis.Chapter4.Rationals where

open import Relation.Nullary.Decidable using (False; fromWitnessFalse)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_; _value_)
open import net.cruhland.axioms.DecEq using
  (_≃?_; ≃-derive; ≄-derive; ≄ⁱ-derive)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; _≄ⁱ_; ≄ⁱ-elim; Eq; ≄ⁱ-intro; refl; sym; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_; _*_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (_↔_; ↔-intro; ↔-elimᴸ)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)

module ℕ = PeanoArithmetic peanoArithmetic
open ℕ using (ℕ)
import net.cruhland.models.Integers peanoArithmetic as ℤ
open ℤ using (ℤ)
import net.cruhland.models.Rationals peanoArithmetic as ℚ
open ℚ using (_//1; _//_; _//_~_; _⁻¹; _⁻¹′; _/′_; ℚ)

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

_ : ℚ → ℚ
_ = -_ {{ℚ.dashᴸ}}

-- Lemma 4.2.3
_ : {a b₁ b₂ : ℚ} → b₁ ≃ b₂ → b₁ + a ≃ b₂ + a
_ = AA.subst {{r = ℚ.+-substitutiveᴸ}}

+-substᴿ : {a b₁ b₂ : ℚ} → b₁ ≃ b₂ → a + b₁ ≃ a + b₂
+-substᴿ {a} = AA.subst {{r = ℚ.+-substitutiveᴿ {a}}}

_ : {a b₁ b₂ : ℚ} → b₁ ≃ b₂ → b₁ * a ≃ b₂ * a
_ = AA.subst {{r = ℚ.*-substitutiveᴸ}}

*-substᴿ : {a b₁ b₂ : ℚ} → b₁ ≃ b₂ → a * b₁ ≃ a * b₂
*-substᴿ {a} = AA.subst {{r = ℚ.*-substitutiveᴿ {a}}}

_ : {a₁ a₂ : ℚ} → a₁ ≃ a₂ → - a₁ ≃ - a₂
_ = AA.subst {{r = ℚ.neg-substitutive₁}}

-- We note that the rational numbers a//1 behave in a manner identical
-- to the integers a:
compat-+ : ∀ {a b} → (a //1) + (b //1) ≃ (a + b) //1
compat-+ {a} = sym (AA.compat₂ {{r = ℚ.+-compatible-ℤ}} {a})

compat-* : ∀ {a b} → (a //1) * (b //1) ≃ (a * b) //1
compat-* {a} = sym (AA.compat₂ {{r = ℚ.*-compatible-ℤ}} {a})

_ : ∀ {a} → - (a //1) ≃ (- a) //1
_ = sym (AA.compat₁ {{r = ℚ.neg-compatible-ℤ}})

-- Also, a//1 and b//1 are only equal when a and b are equal.
_ : ∀ {a b} → a //1 ≃ b //1 ↔ a ≃ b
_ = ↔-intro
  (AA.inject {{r = ℚ.from-ℤ-injective}})
  (AA.subst {{r = ℚ.from-ℤ-substitutive₁}})

-- Because of this, we will identify a with a//1 for each integer a:
-- a ≡ a//1; the above identities then guarantee that the arithmetic
-- of the integers is consistent with the arithmetic of the
-- rationals. Thus just as we embedded the natural numbers inside the
-- integers, we embed the integers inside the rational numbers.
_ : ∀ {a} → (a as ℚ) ≃ a // 1     -- uses ℚ.from-ℤ for (a as ℚ)
_ = ℚ.≃₀-intro refl

-- In particular, all natural numbers are rational numbers, for
-- instance 0 is equal to 0//1 and 1 is equal to 1//1.
_ : ((ℕ value 0) as ℚ) ≃ 0 // 1
_ = ≃-derive

_ : ((ℕ value 1) as ℚ) ≃ 1 // 1
_ = ≃-derive

-- Observe that a rational number a//b is equal to 0 = 0//1 if and
-- only if a × 1 = b × 0, i.e., if the numerator a is equal to 0.
_ : ∀ {q} → q ≃ 0 ↔ ℚ.n q ≃ 0
_ = ↔-intro ℚ.q↑≃0 ℚ.q≃0

--  Thus if a and b are non-zero then so is a//b.
_ : {a b : ℤ} → a ≄ 0 → {b≄0 : b ≄ 0} → a // b ~ b≄0 ≄ 0
_ = _∘ ℚ.q↑≃0

-- We now define a new operation on the rationals: reciprocal.
-- If x = a//b is a non-zero rational (so that a,b ≠ 0) then we
-- define the _reciprocal_ x⁻¹ of x to be the rational number
-- x⁻¹ ≔ b//a.
_ : {q : ℚ} → q ≄ 0 → ℚ
_ = _⁻¹

-- It is easy to check that this operation is consistent with our
-- notion of equality: if two rational numbers a//b, a′//b′ are equal,
-- then their reciprocals are also equal.
_ : {q₁ q₂ : ℚ} (q₁≄0 : q₁ ≄ 0) (q₂≄0 : q₂ ≄ 0) → q₁ ≃ q₂ → q₁≄0 ⁻¹ ≃ q₂≄0 ⁻¹
_ = ℚ.recip-subst

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

_ : ∀ {x} {{_ : x ≄ⁱ 0}} → x * x ⁻¹′ ≃ 1
_ = AA.inv {{r = ℚ.recip′-inverseᴿ}}

_ : ∀ {x} {{_ : x ≄ⁱ 0}} → x ⁻¹′ * x ≃ 1
_ = AA.inv {{r = ℚ.recip′-inverseᴸ}}

-- We can now define the _quotient_ x/y of two rational numbers x and
-- y, _provided that_ y is non-zero, by the formula x/y ≔ x × y⁻¹.
_ : (x y : ℚ) {{_ : y ≄ⁱ 0}} → ℚ
_ = _/′_

-- Thus, for instance:
_ = let instance _ = ≄ⁱ-derive in
  begin
    (3 // 4) /′ (5 // 6)
  ≃⟨⟩
    (3 // 4) * (6 // 5)
  ≃⟨⟩
    18 // 20
  ≃⟨ ℚ.≃₀-intro refl ⟩
    9 // 10
  ∎

-- Using this formula, it is easy to see that a/b = a//b for every
-- integer a and every non-zero integer b. Thus we can now discard the
-- // notation, and use the more customary a/b instead of a//b.
//-redundant :
  {a b : ℤ} {{b≄ⁱ0 : b ≄ⁱ 0}} {{_ : (b as ℚ) ≄ⁱ 0}} →
    (a as ℚ) /′ (b as ℚ) ≃ a // b ~ ≄ⁱ-elim b≄ⁱ0
//-redundant {a} = ℚ.≃₀-intro (AA.assoc {_⊙_ = _*_} {a = a})

-- In a similar spirit, we define subtraction on the rationals by the
-- formula x - y ≔ x + (- y), just as we did with the integers.
_ : ℚ → ℚ → ℚ
_ = _-_ {{r = ℚ.dash₂}}

-- Definition 4.2.6. A rational number x is said to be _positive_ iff
-- we have x = a/b for some positive integers a and b. It is said to
-- be _negative_ iff we have x = -y for some positive rational y
-- (i.e., x = (- a)/b for some positive integers a and b).
_ : ℚ → Set
_ = ℚ.Positive

_ : ℚ → Set
_ = ℚ.Negative

alt-negative :
  ∀ {a b} → ℤ.Positive a → (b⁺ : ℤ.Positive b) →
    let instance b≄ⁱ0 = ≄ⁱ-intro (AA.subst (ℤ.pos-nonzero b⁺))
     in ℚ.Negative ((- a as ℚ) /′ (b as ℚ))
alt-negative {a} {b} a⁺ b⁺ =
  let instance b≄ⁱ0 = ≄ⁱ-intro (AA.subst (ℤ.pos-nonzero b⁺))
      p = (a as ℚ) /′ (b as ℚ)
      p-pos = record
        { n-pos = AA.subst (sym AA.ident) a⁺
        ; d-pos = AA.subst (sym AA.ident) b⁺ }
      [-a]/b≃-p =
        begin
          (- a as ℚ) /′ (b as ℚ)
        ≃⟨⟩
          (- a as ℚ) * (b as ℚ) ⁻¹′
        ≃⟨ AA.subst {{r = ℚ.*-substitutiveᴸ {(b as ℚ) ⁻¹′}}}
             (AA.compat₁ {a = a}) ⟩
          (- (a as ℚ)) * (b as ℚ) ⁻¹′
        ≃⟨ AA.commᴸ {a = a as ℚ} {b = (b as ℚ) ⁻¹′} ⟩
          - ((a as ℚ) * (b as ℚ) ⁻¹′)
        ≃⟨⟩
          - ((a as ℚ) /′ (b as ℚ))
        ≃⟨⟩
          - p
        ∎
   in record { p = p ; p-pos = p-pos ; q≃-p = [-a]/b≃-p }

-- Thus for instance, every positive integer is a positive rational
-- number, and every negative integer is a negative rational number,
-- so our new definition is consistent with our old one.
ℚ⁺-compat-ℤ⁺ : ∀ {a} → ℤ.Positive a → ℚ.Positive (a as ℚ)
ℚ⁺-compat-ℤ⁺ a⁺ = record { n-pos = a⁺ ; d-pos = ℤ.1-Positive }

ℚ⁻-compat-ℤ⁻ : ∀ {a} → ℤ.Negative a → ℚ.Negative (a as ℚ)
ℚ⁻-compat-ℤ⁻ {a} a⁻ = record
  { p = - (a as ℚ)
  ; p-pos = record { n-pos = ℤ.neg-Negative a⁻ ; d-pos = ℤ.1-Positive }
  ; q≃-p = refl
  }
