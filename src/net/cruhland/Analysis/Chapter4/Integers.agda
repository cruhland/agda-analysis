module net.cruhland.Analysis.Chapter4.Integers where

open import Agda.Builtin.FromNat using (Number)
open import Agda.Builtin.FromNeg using (Negative)
import Agda.Builtin.Nat as Nat
open import Function using (_∘_; const; flip)
open import Relation.Binary using (IsEquivalence)
-- Need this so instance search can construct equalities
open import Relation.Binary.PropositionalEquality
  using () renaming (refl to ≡-refl)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; Eq; refl; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Logic using
  (⊤; ⊤-intro; ∧-elimᴿ; _∨_; ∨-introᴸ; ∨-introᴿ; ⊥; ⊥-elim; ¬_; _↔_; ↔-intro)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)
open import net.cruhland.models.Setoid using (Setoid₀)

open PeanoArithmetic peanoArithmetic using
  ( ℕ; <→<⁺; tri-<; tri-≃; tri->) renaming
  ( _≃_ to _≃ᴺ_; step to stepᴺ; step-subst to stepᴺ-subst
  ; step≄zero to stepᴺ≄zero; step≃+ to stepᴺ≃+
  ; _+_ to _+ᴺ_; +-assoc to +ᴺ-assoc; +-both-zero to +ᴺ-both-zero
  ; +-cancelᴸ to +ᴺ-cancelᴸ; +-cancelᴿ to +ᴺ-cancelᴿ; +-comm to +ᴺ-comm
  ; +-zeroᴿ to +ᴺ-identityᴿ; +-positive to +ᴺ-positive; +-stepᴸ to +ᴺ-stepᴸ
  ; +-substᴸ to +ᴺ-substᴸ; +-substᴿ to +ᴺ-substᴿ; +-unchanged to +ᴺ-unchanged
  ; _*_ to _*ᴺ_; *-assoc to *ᴺ-assoc; *-cancelᴸ to *ᴺ-cancelᴸ; *-comm to *ᴺ-comm
  ; *-distrib-+ᴸ to *ᴺ-distrib-+ᴺᴸ; *-distrib-+ᴿ to *ᴺ-distrib-+ᴺᴿ
  ; *-positive to *ᴺ-positive; *-substᴸ to *ᴺ-substᴸ; *-zeroᴿ to *ᴺ-zeroᴿ
  ; number to ℕ-number; Positive to Positiveᴺ; trichotomy to trichotomyᴺ
  )
import net.cruhland.models.Integers peanoArithmetic as ℤ
open ℤ using
  ( _—_; _+_; _*_; -_; _-_; a≃b+c≃d; AtLeastOne; ≃ᶻ-intro
  ; IsNegative; IsPositive; MoreThanOne; neg; nil; pos; transpose
  ; Trichotomy; trichotomy; ℤ; ℤ⁺; ℤ⁻
  )
open Trichotomy using (at-least)

{- 4.1 The integers -}

-- Definition 4.1.1 (Integers). An _integer_ is an expression of the
-- form a—b, where a and b are natural numbers. Two integers are
-- considered to be equal, a—b = c—d, if and only if a + d = c + b. We
-- let ℤ denote the set of all integers.
_ : Set
_ = ℤ

_ : ℤ → ℤ → Set
_ = _≃_

_ : ℤ
_ = 3 — 5

_ : 3 — 5 ≃ 2 — 4
_ = ≃ᶻ-intro

_ : 3 — 5 ≄ 2 — 3
_ = λ ()

-- Exercise 4.1.1
_ : Eq ℤ
_ = ℤ.eq

open ℤ._≃ᶻ_ using (≃ᶻ-elim)

-- Definition 4.1.2. The sum of two integers, (a—b) + (c—d), is
-- defined by the formula (a—b) + (c—d) ≔ (a + c)—(b + d).
_ : ℤ → ℤ → ℤ
_ = _+_

-- The product of two integers, (a—b) × (c—d), is defined by
-- (a—b) × (c—d) ≔ (ac + bd)—(ad + bc).
_ : ℤ → ℤ → ℤ
_ = _*_

-- Thus for instance, (3—5) + (1—4) is equal to (4—9).
_ : 3 — 5 + 1 — 4 ≃ 4 — 9
_ = ≃ᶻ-intro

-- There is however one thing we have to check before we can accept
-- these definitions - we have to check that if we replace one of the
-- integers by an equal integer, that the sum or product does not
-- change. For instance (3—5) is equal to (2—4), so (3—5) + (1—4)
-- ought to have the same value as (2—4) + (1—4), otherwise this would
-- not give a consistent definition of addition.
_ : 3 — 5 + 1 — 4 ≃ 2 — 4 + 1 — 4
_ = ≃ᶻ-intro

-- Lemma 4.1.3 (Addition and multiplication are well-defined).
_ : ∀ {a₁ a₂ b} → a₁ ≃ a₂ → a₁ + b ≃ a₂ + b
_ = ℤ.+-substᴸ

_ : ∀ {a b₁ b₂} → b₁ ≃ b₂ → a + b₁ ≃ a + b₂
_ = ℤ.+-substᴿ

_ : ∀ {a₁ a₂ b} → a₁ ≃ a₂ → a₁ * b ≃ a₂ * b
_ = ℤ.*-substᴸ

*-substᴿ : ∀ {a b₁ b₂} → b₁ ≃ b₂ → a * b₁ ≃ a * b₂
*-substᴿ {a} = ℤ.*-substᴿ {a}

-- The integers n—0 behave in the same way as the natural numbers n;
-- indeed one can check that (n—0) + (m—0) = (n + m)—0 and
-- (n—0) × (m—0) = nm—0.
_ : ∀ {n m} → n — 0 + m — 0 ≃ (n +ᴺ m) — 0
_ = ≃ᶻ-intro

*-compat-*ᴺ : ∀ {n m} → n — 0 * m — 0 ≃ (n *ᴺ m) — 0
*-compat-*ᴺ {n} {m} = ≃ᶻ-intro {{eq′}}
  where
    eq′ =
      begin
        n *ᴺ m +ᴺ 0 +ᴺ 0
      ≃⟨ +ᴺ-assoc {n *ᴺ m} ⟩
        n *ᴺ m +ᴺ (0 +ᴺ 0)
      ≃˘⟨ +ᴺ-substᴿ (+ᴺ-substᴸ {m = 0} (*ᴺ-zeroᴿ {n})) ⟩
        n *ᴺ m +ᴺ (n *ᴺ 0 +ᴺ 0)
      ∎

-- Furthermore, (n—0) is equal to (m—0) if and only if n = m.
_ : ∀ {n m} → n — 0 ≃ m — 0 ↔ n ≃ᴺ m
_ = ↔-intro (+ᴺ-cancelᴿ ∘ ≃ᶻ-elim) (λ n≃m → ≃ᶻ-intro {{+ᴺ-substᴸ n≃m}})

-- Thus we may _identify_ the natural numbers with integers by setting
-- n ≃ n—0; this does not affect our definitions of addition or
-- multiplication or equality since they are consistent with each
-- other.
-- [note] We can't make this identification in type theory because
-- both propositional equality and setoid equality require that their
-- associated values belong to the same type. However, we can use the
-- Number typeclass to interpret numeric literals as elements of
-- ℤ. And we can define a function to convert natural numbers to their
-- integer equivalent.
_ : Number ℤ
_ = ℤ.number

-- For instance the natural number 3 is now considered to be the same
-- as the integer 3—0, thus 3 = 3—0.
_ : 3 ≃ 3 — 0
_ = ≃ᶻ-intro

-- In particular 0 is equal to 0—0 and 1 is equal to 1—0.
_ : 0 ≃ 0 — 0
_ = ≃ᶻ-intro

_ : 1 ≃ 1 — 0
_ = ≃ᶻ-intro

-- Of course, if we set n equal to n—0, then it will also be equal to
-- any other integer which is equal to n—0, for instance 3 is equal
-- not only to 3—0, but also to 4—1, 5—2, etc.
_ : 3 ≃ 4 — 1
_ = ≃ᶻ-intro

_ : 3 ≃ 5 — 2
_ = ≃ᶻ-intro

-- We can now define incrementation on the integers by defining
-- step x ≔ x + 1 for any integer x; this is of course consistent with
-- our definition of the increment operation for natural
-- numbers. However, this is no longer an important operation for us,
-- as it has been now superceded by the more general notion of
-- addition.
step : ℤ → ℤ
step x = x + 1

ℤ⁺s≃sℤ⁺ : ∀ {a} → ℤ⁺ (step a) ≃ᴺ stepᴺ (ℤ⁺ a)
ℤ⁺s≃sℤ⁺ {a⁺ — _} = sym stepᴺ≃+

ℤ⁻s≃ℤ⁻ : ∀ {a} → ℤ⁻ (step a) ≃ᴺ ℤ⁻ a
ℤ⁻s≃ℤ⁻ {_ — a⁻} = +ᴺ-identityᴿ

-- Definition 4.1.4 (Negation of integers). If (a—b) is an integer, we
-- define the negation -(a—b) to be the integer (b—a).
_ : ℤ → ℤ
_ = -_

-- In particular if n = n—0 is a positive natural number, we can
-- define its negation -n = 0—n.
-- [note] Here we must use a conversion function since n is not a
-- literal.
_ : ℕ → ℤ
_ = ℤ.fromℕ

fromℕ-subst : ∀ {n₁ n₂} → n₁ ≃ᴺ n₂ → ℤ.fromℕ n₁ ≃ ℤ.fromℕ n₂
fromℕ-subst n₁≃n₂ = ≃ᶻ-intro {{+ᴺ-substᴸ n₁≃n₂}}

_ : ∀ {n} → - (ℤ.fromℕ n) ≃ 0 — n
_ = ≃ᶻ-intro

-- For instance -(3—5) = (5—3).
_ : -(3 — 5) ≃ 5 — 3
_ = ≃ᶻ-intro

-- One can check this definition is well-defined.
-- Exercise 4.1.2
neg-subst : ∀ {a₁ a₂} → a₁ ≃ a₂ → - a₁ ≃ - a₂
neg-subst {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} a₁≃a₂ = ≃ᶻ-intro {{eq′}}
  where
    a₁⁺+a₂⁻≃a₂⁺+a₁⁻ = ≃ᶻ-elim a₁≃a₂
    eq′ =
      begin
        a₁⁻ +ᴺ a₂⁺
      ≃⟨ +ᴺ-comm {a₁⁻} ⟩
        a₂⁺ +ᴺ a₁⁻
      ≃˘⟨ a₁⁺+a₂⁻≃a₂⁺+a₁⁻ ⟩
        a₁⁺ +ᴺ a₂⁻
      ≃⟨ +ᴺ-comm {a₁⁺} ⟩
        a₂⁻ +ᴺ a₁⁺
      ∎

-- Lemma 4.1.5 (Trichotomy of integers). Let x be an integer. Then
-- exactly one of the following three statements is true: (a) x is
-- zero; (b) x is equal to a positive natural number n; or (c) x is
-- the negation -n of a positive natural number n.
_ : ℤ → Set
_ = IsPositive

_ : ℤ → Set
_ = IsNegative

_ : ℤ → Set
_ = AtLeastOne

_ : ℤ → Set
_ = MoreThanOne

_ : ℤ → Set
_ = Trichotomy

_ : ∀ x → Trichotomy x
_ = trichotomy

-- Proposition 4.1.6 (Laws of algebra for integers).
-- Exercise 4.1.4
+-comm : ∀ {x y} → x + y ≃ y + x
+-comm {x} = ℤ.+-comm {x}

+-assoc : ∀ {x y z} → (x + y) + z ≃ x + (y + z)
+-assoc {x} = ℤ.+-assoc {x}

_ : ∀ {x} → 0 + x ≃ x
_ = ℤ.+-identityᴸ

_ : ∀ {x} → x + 0 ≃ x
_ = ℤ.+-identityᴿ

+-inverseᴸ : ∀ {x} → - x + x ≃ 0
+-inverseᴸ {x} = ℤ.+-inverseᴸ {x}

+-inverseᴿ : ∀ {x} → x + - x ≃ 0
+-inverseᴿ {x} = ℤ.+-inverseᴿ {x}

*-comm : ∀ {x y} → x * y ≃ y * x
*-comm {x} = ℤ.*-comm {x}

*-assoc : ∀ {x y z} → (x * y) * z ≃ x * (y * z)
*-assoc {x⁺ — x⁻} {y⁺ — y⁻} {z⁺ — z⁻} = ≃ᶻ-intro {{eq′}}
  where
    assoc-four :
      ∀ {a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃} →
        ((a₁ *ᴺ a₂) *ᴺ a₃ +ᴺ (b₁ *ᴺ b₂) *ᴺ b₃) +ᴺ
        ((c₁ *ᴺ c₂) *ᴺ c₃ +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃) ≃ᴺ
        (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃)) +ᴺ
        (c₁ *ᴺ (c₂ *ᴺ c₃) +ᴺ d₁ *ᴺ (d₂ *ᴺ d₃))
    assoc-four {a₁} {a₂} {a₃} {b₁} {b₂} {b₃} {c₁} {c₂} {c₃} {d₁} {d₂} {d₃} =
      begin
        ((a₁ *ᴺ a₂) *ᴺ a₃ +ᴺ (b₁ *ᴺ b₂) *ᴺ b₃) +ᴺ
        ((c₁ *ᴺ c₂) *ᴺ c₃ +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃)
      ≃⟨ +ᴺ-substᴸ (+ᴺ-substᴸ (*ᴺ-assoc {a₁})) ⟩
        (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ (b₁ *ᴺ b₂) *ᴺ b₃) +ᴺ
        ((c₁ *ᴺ c₂) *ᴺ c₃ +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃)
      ≃⟨ +ᴺ-substᴸ (+ᴺ-substᴿ {a₁ *ᴺ (a₂ *ᴺ a₃)} (*ᴺ-assoc {b₁})) ⟩
        (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃)) +ᴺ
        ((c₁ *ᴺ c₂) *ᴺ c₃ +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃)
      ≃⟨ +ᴺ-substᴿ
           {(a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃))}
           (+ᴺ-substᴸ (*ᴺ-assoc {c₁}))
       ⟩
        (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃)) +ᴺ
        (c₁ *ᴺ (c₂ *ᴺ c₃) +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃)
      ≃⟨ +ᴺ-substᴿ
           {(a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃))}
           (+ᴺ-substᴿ (*ᴺ-assoc {d₁}))
       ⟩
        (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃)) +ᴺ
        (c₁ *ᴺ (c₂ *ᴺ c₃) +ᴺ d₁ *ᴺ (d₂ *ᴺ d₃))
      ∎

    refactor :
      ∀ {b₁ b₂ a₁ a₂ a₃ a₄} →
        (a₁ *ᴺ a₃ +ᴺ a₂ *ᴺ a₄) *ᴺ b₁ +ᴺ (a₁ *ᴺ a₄ +ᴺ a₂ *ᴺ a₃) *ᴺ b₂ ≃ᴺ
          a₁ *ᴺ (a₃ *ᴺ b₁ +ᴺ a₄ *ᴺ b₂) +ᴺ a₂ *ᴺ (a₃ *ᴺ b₂ +ᴺ a₄ *ᴺ b₁)
    refactor {b₁} {b₂} {a₁} {a₂} {a₃} {a₄} =
      begin
        (a₁ *ᴺ a₃ +ᴺ a₂ *ᴺ a₄) *ᴺ b₁ +ᴺ (a₁ *ᴺ a₄ +ᴺ a₂ *ᴺ a₃) *ᴺ b₂
      ≃⟨ ℤ.distrib-twoᴿ {a = a₁ *ᴺ a₃} {d = a₁ *ᴺ a₄} ⟩
        ((a₁ *ᴺ a₃) *ᴺ b₁ +ᴺ (a₂ *ᴺ a₄) *ᴺ b₁) +ᴺ
        ((a₁ *ᴺ a₄) *ᴺ b₂ +ᴺ (a₂ *ᴺ a₃) *ᴺ b₂)
      ≃⟨ transpose {(a₁ *ᴺ a₃) *ᴺ b₁}⟩
        ((a₁ *ᴺ a₃) *ᴺ b₁ +ᴺ (a₁ *ᴺ a₄) *ᴺ b₂) +ᴺ
        ((a₂ *ᴺ a₄) *ᴺ b₁ +ᴺ (a₂ *ᴺ a₃) *ᴺ b₂)
      ≃⟨ +ᴺ-substᴿ
           {(a₁ *ᴺ a₃) *ᴺ b₁ +ᴺ (a₁ *ᴺ a₄) *ᴺ b₂}
           (+ᴺ-comm {(a₂ *ᴺ a₄) *ᴺ b₁})
       ⟩
        ((a₁ *ᴺ a₃) *ᴺ b₁ +ᴺ (a₁ *ᴺ a₄) *ᴺ b₂) +ᴺ
        ((a₂ *ᴺ a₃) *ᴺ b₂ +ᴺ (a₂ *ᴺ a₄) *ᴺ b₁)
      ≃⟨ assoc-four {a₁ = a₁} {b₁ = a₁} {c₁ = a₂} {d₁ = a₂} ⟩
        (a₁ *ᴺ (a₃ *ᴺ b₁) +ᴺ a₁ *ᴺ (a₄ *ᴺ b₂)) +ᴺ
        (a₂ *ᴺ (a₃ *ᴺ b₂) +ᴺ a₂ *ᴺ (a₄ *ᴺ b₁))
      ≃˘⟨ ℤ.distrib-twoᴸ {a = a₁} {d = a₂} ⟩
        a₁ *ᴺ (a₃ *ᴺ b₁ +ᴺ a₄ *ᴺ b₂) +ᴺ a₂ *ᴺ (a₃ *ᴺ b₂ +ᴺ a₄ *ᴺ b₁)
      ∎

    eq′ = a≃b+c≃d
           (refactor {z⁺} {z⁻} {x⁺} {x⁻})
           (sym (refactor {z⁻} {z⁺} {x⁺} {x⁻}))

*-identityᴸ : ∀ {x} → 1 * x ≃ x
*-identityᴸ {x⁺ — x⁻} = ≃ᶻ-intro {{eq′}}
  where
    eq′ =
      begin
        ((x⁺ +ᴺ 0) +ᴺ 0) +ᴺ x⁻
      ≃⟨ +ᴺ-assoc {x⁺ +ᴺ 0} ⟩
        (x⁺ +ᴺ 0) +ᴺ (0 +ᴺ x⁻)
      ≃⟨ +ᴺ-substᴿ {x⁺ +ᴺ 0} (+ᴺ-comm {0}) ⟩
        (x⁺ +ᴺ 0) +ᴺ (x⁻ +ᴺ 0)
      ≃⟨ +ᴺ-assoc {x⁺} ⟩
        x⁺ +ᴺ (0 +ᴺ (x⁻ +ᴺ 0))
      ≃⟨ +ᴺ-substᴿ {x⁺} (+ᴺ-comm {0}) ⟩
        x⁺ +ᴺ ((x⁻ +ᴺ 0) +ᴺ 0)
      ∎

*-identityᴿ : ∀ {x} → x * 1 ≃ x
*-identityᴿ {x} =
  begin
    x * 1
  ≃⟨ ℤ.*-comm {x} ⟩
    1 * x
  ≃⟨ *-identityᴸ ⟩
    x
  ∎

*-distrib-+ᴸ : ∀ {x y z} → x * (y + z) ≃ x * y + x * z
*-distrib-+ᴸ {x} = ℤ.*-distrib-+ᴸ {x}

*-distrib-+ᴿ : ∀ {x y z} → (y + z) * x ≃ y * x + z * x
*-distrib-+ᴿ {x} {y} = ℤ.*-distrib-+ᴿ {x} {y}

-- We now define the operation of _subtraction_ x - y of two integers
-- by the formula x - y ≔ x + (-y).
_ : ℤ → ℤ → ℤ
_ = _-_

-- One can easily check now that if a and b are natural numbers, then
-- a - b = a + -b = (a—0) + (0—b) = a—b, and so a—b is just the same
-- thing as a - b. Because of this we can now discard the — notation,
-- and use the familiar operation of subtraction instead.
natsub : ∀ {a b} → ℤ.fromℕ a - ℤ.fromℕ b ≃ a — b
natsub {a} = ≃ᶻ-intro {{+ᴺ-substᴸ (+ᴺ-identityᴿ {a})}}

-- Proposition 4.1.8 (Integers have no zero divisors). Let a and b be
-- integers such that ab = 0. Then either a = 0 or b = 0 (or both).
-- Exercise 4.1.5
_ : ∀ {a b} → a * b ≃ 0 → a ≃ 0 ∨ b ≃ 0
_ = ℤ.*-either-zero

-- Corollary 4.1.9 (Cancellation law for integers). If a, b, c are
-- integers such that ac = bc and c is non-zero, then a = b.
-- Exercise 4.1.6
_ : ∀ {a₁ a₂ b} → a₁ ≃ a₂ → a₁ - b ≃ a₂ - b
_ = ℤ.sub-substᴸ

sub-substᴿ : ∀ {a b₁ b₂} → b₁ ≃ b₂ → a - b₁ ≃ a - b₂
sub-substᴿ = ℤ.+-substᴿ ∘ neg-subst

*-negᴸ : ∀ {a b} → - a * b ≃ - (a * b)
*-negᴸ {a} = ℤ.*-negᴸ {a}

*-negᴿ : ∀ {a b} → a * - b ≃ - (a * b)
*-negᴿ {a} {b} =
  begin
    a * - b
  ≃⟨ *-comm {a} ⟩
    - b * a
  ≃⟨ *-negᴸ {b} ⟩
    - (b * a)
  ≃⟨ neg-subst (*-comm {b}) ⟩
    - (a * b)
  ∎

*-distrib-subᴸ : ∀ {a b c} → c * (a - b) ≃ c * a - c * b
*-distrib-subᴸ {a} {b} {c} =
  begin
    c * (a - b)
  ≃⟨⟩
    c * (a + - b)
  ≃⟨ *-distrib-+ᴸ {c} ⟩
    c * a + c * - b
  ≃⟨ ℤ.+-substᴿ {c * a} (*-negᴿ {c}) ⟩
    c * a + - (c * b)
  ≃⟨⟩
    c * a - c * b
  ∎

_ : ∀ {a b c} → c ≄ 0 → a * c ≃ b * c → a ≃ b
_ = ℤ.*-cancelᴿ

-- Definition 4.1.10 (Ordering of the integers). Let n and m be
-- integers. We say that n is _greater than or equal to_ m, and write
-- n ≥ m or m ≤ n, iff we have n = m + a for some natural number a. We
-- say that n is _strictly greater than_ m and write n > m or m < n,
-- iff n ≥ m and n ≠ m.
infix 4 _≤_
record _≤_ (n m : ℤ) : Set where
  constructor ≤-intro
  field
    a : ℕ
    n≃m+a : m ≃ n + ℤ.fromℕ a

infix 4 _<_
record _<_ (n m : ℤ) : Set where
  constructor <-intro
  field
    n≤m : n ≤ m
    n≄m : n ≄ m

infix 4 _>_
_>_ = flip _<_

_ : Negative ℤ
_ = ℤ.negative

_ : 5 > -3
_ = <-intro (≤-intro 8 ≃ᶻ-intro) λ ()

-- Lemma 4.1.11 (Properties of order).
-- Exercise 4.1.7
ℕ≃→ℤ≃ : ∀ {n m} → n ≃ᴺ m → ℤ.fromℕ n ≃ ℤ.fromℕ m
ℕ≃→ℤ≃ n≃m = ≃ᶻ-intro {{trans +ᴺ-identityᴿ (trans n≃m (sym +ᴺ-identityᴿ))}}

n≃0→n≃0 : ∀ {n} → ℤ.fromℕ n ≃ 0 → n ≃ᴺ 0
n≃0→n≃0 (≃ᶻ-intro {{n+0≃0}}) = trans (sym +ᴺ-identityᴿ) n+0≃0

≃ᴿ-+ᴸ-toᴿ : ∀ {a b c} → a ≃ b + c → a - b ≃ c
≃ᴿ-+ᴸ-toᴿ {a} {b} {c} a≃b+c =
  begin
    a - b
  ≃⟨ ℤ.sub-substᴸ a≃b+c ⟩
    b + c - b
  ≃⟨ ℤ.sub-substᴸ (+-comm {b}) ⟩
    c + b - b
  ≃⟨ +-assoc {c} ⟩
    c + (b - b)
  ≃⟨ ℤ.+-substᴿ (+-inverseᴿ {b}) ⟩
    c + 0
  ≃⟨ ℤ.+-identityᴿ ⟩
    c
  ∎

≃ᴸ-subᴿ-toᴸ : ∀ {a b c} → a - b ≃ c → a ≃ b + c
≃ᴸ-subᴿ-toᴸ {a} {b} {c} a-b≃c =
  begin
    a
  ≃˘⟨ ℤ.+-identityᴿ ⟩
    a + 0
  ≃˘⟨ ℤ.+-substᴿ (+-inverseᴿ {b}) ⟩
    a + (b - b)
  ≃⟨ ℤ.+-substᴿ {a} (+-comm {b}) ⟩
    a + (- b + b)
  ≃˘⟨ +-assoc {a} ⟩
    a - b + b
  ≃⟨ ℤ.+-substᴸ a-b≃c ⟩
    c + b
  ≃⟨ +-comm {c} ⟩
    b + c
  ∎

vanish : ∀ {x y} → x + y - y ≃ x
vanish {x} {y} =
  begin
    x + y - y
  ≃⟨ +-assoc {x} ⟩
    x + (y - y)
  ≃⟨ ℤ.+-substᴿ (+-inverseᴿ {y}) ⟩
    x + 0
  ≃⟨ ℤ.+-identityᴿ ⟩
    x
  ∎

+-cancelᴿ : ∀ {a b c} → a + c ≃ b + c → a ≃ b
+-cancelᴿ {a} {b} {c} a+c≃b+c =
    begin
      a
    ≃˘⟨ vanish ⟩
      a + c - c
    ≃⟨ ℤ.sub-substᴸ a+c≃b+c ⟩
      b + c - c
    ≃⟨ vanish ⟩
      b
    ∎

+ᴺ-to-+ : ∀ {n m} → ℤ.fromℕ (n +ᴺ m) ≃ ℤ.fromℕ n + ℤ.fromℕ m
+ᴺ-to-+ {n} {m} = ≃ᶻ-intro

*ᴺ-to-* : ∀ {n m} → ℤ.fromℕ (n *ᴺ m) ≃ ℤ.fromℕ n * ℤ.fromℕ m
*ᴺ-to-* {n} {m} = ≃ᶻ-intro {{eq′}}
  where
    eq′ =
      begin
        n *ᴺ m +ᴺ (n *ᴺ 0 +ᴺ 0)
      ≃⟨ +ᴺ-substᴿ (+ᴺ-substᴸ {m = 0} (*ᴺ-zeroᴿ {n})) ⟩
        n *ᴺ m +ᴺ (0 +ᴺ 0)
      ≃˘⟨ +ᴺ-assoc {n *ᴺ m} ⟩
        n *ᴺ m +ᴺ 0 +ᴺ 0
      ∎

IsPositive-subst : ∀ {a₁ a₂} → a₁ ≃ a₂ → IsPositive a₁ → IsPositive a₂
IsPositive-subst a₁≃a₂ record { n = n ; pos = n≄0 ; x≃n = a₁≃n } =
  record { n = n ; pos = n≄0 ; x≃n = trans (sym a₁≃a₂) a₁≃n }

-- Exercise 4.1.3
neg-mult : ∀ {a} → - a ≃ -1 * a
neg-mult {a⁺ — a⁻} = ≃ᶻ-intro {{eq′}}
  where
    eq′ =
      begin
        a⁻ +ᴺ (a⁺ +ᴺ 0)
      ≃⟨ +ᴺ-substᴿ {a⁻} (+ᴺ-comm {a⁺}) ⟩
        a⁻ +ᴺ (0 +ᴺ a⁺)
      ≃˘⟨ +ᴺ-assoc {a⁻} ⟩
        a⁻ +ᴺ 0 +ᴺ a⁺
      ∎

sub-distrib : ∀ {a b c} → a - (b + c) ≃ a - b - c
sub-distrib {a} {b} {c} =
  begin
    a - (b + c)
  ≃⟨⟩
    a + -(b + c)
  ≃⟨ ℤ.+-substᴿ {a} neg-mult ⟩
    a + -1 * (b + c)
  ≃⟨ ℤ.+-substᴿ {a} (*-distrib-+ᴸ { -1} {b}) ⟩
    a + (-1 * b + -1 * c)
  ≃˘⟨ ℤ.+-substᴿ {a} (ℤ.+-substᴸ (neg-mult {b})) ⟩
    a + (- b + -1 * c)
  ≃˘⟨ ℤ.+-substᴿ {a} (ℤ.+-substᴿ (neg-mult {c})) ⟩
    a + (- b + - c)
  ≃˘⟨ +-assoc {a} ⟩
    a - b - c
  ∎

sub-cancelᴿ : ∀ {a b c} → a + c - (b + c) ≃ a - b
sub-cancelᴿ {a} {b} {c} =
  begin
    a + c - (b + c)
  ≃⟨ sub-distrib {a + c} ⟩
    a + c - b - c
  ≃⟨⟩
    ((a + c) + - b) + - c
  ≃⟨ ℤ.+-substᴸ (+-assoc {a}) ⟩
    (a + (c + - b)) + - c
  ≃⟨ ℤ.+-substᴸ (ℤ.+-substᴿ {a} (+-comm {c})) ⟩
    (a + (- b + c)) + - c
  ≃˘⟨ ℤ.+-substᴸ (+-assoc {a}) ⟩
    ((a + - b) + c) + - c
  ≃⟨⟩
    a - b + c - c
  ≃⟨ vanish ⟩
    a - b
  ∎

+-preserves-pos : ∀ {a b} → IsPositive a → IsPositive b → IsPositive (a + b)
+-preserves-pos {a} {b}
  record { n = aᴺ ; pos = aᴺ≄0 ; x≃n = a≃aᴺ }
  record { n = bᴺ ; pos = bᴺ≄0 ; x≃n = b≃bᴺ } =
    record { n = aᴺ +ᴺ bᴺ ; pos = +ᴺ-positive aᴺ≄0 ; x≃n = a+b≃aᴺ+bᴺ }
  where
    a+b≃aᴺ+bᴺ =
      begin
        a + b
      ≃⟨ ℤ.+-substᴸ a≃aᴺ ⟩
        ℤ.fromℕ aᴺ + b
      ≃⟨ ℤ.+-substᴿ b≃bᴺ ⟩
        ℤ.fromℕ aᴺ + ℤ.fromℕ bᴺ
      ≃˘⟨ +ᴺ-to-+ {aᴺ} ⟩
        ℤ.fromℕ (aᴺ +ᴺ bᴺ)
      ∎

*-preserves-pos : ∀ {a b} → IsPositive a → IsPositive b → IsPositive (a * b)
*-preserves-pos {a} {b}
  record { n = aᴺ ; pos = aᴺ≄0 ; x≃n = a≃aᴺ }
  record { n = bᴺ ; pos = bᴺ≄0 ; x≃n = b≃bᴺ } =
    record { n = aᴺ *ᴺ bᴺ ; pos = *ᴺ-positive aᴺ≄0 bᴺ≄0 ; x≃n = ab≃aᴺbᴺ }
  where
    ab≃aᴺbᴺ =
      begin
        a * b
      ≃⟨ ℤ.*-substᴸ a≃aᴺ ⟩
        ℤ.fromℕ aᴺ * b
      ≃⟨ *-substᴿ {ℤ.fromℕ aᴺ} b≃bᴺ ⟩
        ℤ.fromℕ aᴺ * ℤ.fromℕ bᴺ
      ≃˘⟨ *ᴺ-to-* {aᴺ} ⟩
        ℤ.fromℕ (aᴺ *ᴺ bᴺ)
      ∎

neg-involutive : ∀ {a} → - (- a) ≃ a
neg-involutive {a⁺ — a⁻} = ≃ᶻ-intro

neg-sub-swap : ∀ {a b} → - (a - b) ≃ b - a
neg-sub-swap {a} {b} =
  begin
    - (a - b)
  ≃⟨ neg-mult ⟩
    -1 * (a - b)
  ≃⟨ *-distrib-subᴸ {a} {b} { -1} ⟩
    -1 * a - -1 * b
  ≃˘⟨ ℤ.+-substᴸ (neg-mult {a}) ⟩
    - a - -1 * b
  ≃˘⟨ ℤ.+-substᴿ (neg-subst (neg-mult {b})) ⟩
    - a - (- b)
  ≃⟨ ℤ.+-substᴿ (neg-involutive {b}) ⟩
    - a + b
  ≃˘⟨ +-comm {b} ⟩
    b - a
  ∎

sub-sign-swap : ∀ {a b} → IsNegative (a - b) → IsPositive (b - a)
sub-sign-swap {a} {b} record { n = n ; pos = n≄0 ; x≃-n = a-b≃-n } =
    record { n = n ; pos = n≄0 ; x≃n = b-a≃n }
  where
    b-a≃n =
      begin
        b - a
      ≃˘⟨ neg-sub-swap {a} ⟩
        - (a - b)
      ≃⟨ neg-subst a-b≃-n ⟩
        - (- ℤ.fromℕ n)
      ≃⟨ neg-involutive {ℤ.fromℕ n} ⟩
        ℤ.fromℕ n
      ∎

≤-antisym : ∀ {a b} → a ≤ b → b ≤ a → a ≃ b
≤-antisym {a} {b} (≤-intro n₁ b≃a+n₁) (≤-intro n₂ a≃b+n₂) =
  let n₁+ᴺn₂≃0 =
        begin
          ℤ.fromℕ (n₁ +ᴺ n₂)
        ≃⟨ +ᴺ-to-+ {n₁} ⟩
          ℤ.fromℕ n₁ + ℤ.fromℕ n₂
        ≃˘⟨ ℤ.+-identityᴸ ⟩
          0 + (ℤ.fromℕ n₁ + ℤ.fromℕ n₂)
        ≃˘⟨ ℤ.+-substᴸ (+-inverseᴸ {a}) ⟩
          (- a) + a + (ℤ.fromℕ n₁ + ℤ.fromℕ n₂)
        ≃⟨ +-assoc { - a} ⟩
          (- a) + (a + (ℤ.fromℕ n₁ + ℤ.fromℕ n₂))
        ≃˘⟨ ℤ.+-substᴿ { - a} (+-assoc {a}) ⟩
          (- a) + (a + ℤ.fromℕ n₁ + ℤ.fromℕ n₂)
        ≃˘⟨ ℤ.+-substᴿ { - a} (ℤ.+-substᴸ b≃a+n₁) ⟩
          (- a) + (b + ℤ.fromℕ n₂)
        ≃˘⟨ ℤ.+-substᴿ a≃b+n₂ ⟩
          (- a) + a
        ≃⟨ +-inverseᴸ {a} ⟩
          0
        ∎
      n₂≃0 = ∧-elimᴿ (+ᴺ-both-zero (n≃0→n≃0 n₁+ᴺn₂≃0))
   in trans (trans a≃b+n₂ (ℤ.+-substᴿ (fromℕ-subst n₂≃0))) ℤ.+-identityᴿ

-- (a)
<→pos : ∀ {x y} → x < y → IsPositive (y - x)
<→pos {x} {y} (<-intro (≤-intro a y≃x+a) x≄y) =
    record { n = a ; pos = a≄0 ; x≃n = ≃ᴿ-+ᴸ-toᴿ y≃x+a }
  where
    a≄0 : a ≄ 0
    a≄0 a≃0 = x≄y x≃y
      where
        x≃y =
          begin
            x
          ≃˘⟨ ℤ.+-identityᴿ ⟩
            x + 0
          ≃˘⟨ ℤ.+-substᴿ (ℕ≃→ℤ≃ a≃0) ⟩
            x + ℤ.fromℕ a
          ≃˘⟨ y≃x+a ⟩
            y
          ∎

pos→< : ∀ {x y} → IsPositive (y - x) → x < y
pos→< {x} {y} record { n = n ; pos = n≄0 ; x≃n = y-x≃n } =
    <-intro (≤-intro n (≃ᴸ-subᴿ-toᴸ y-x≃n)) x≄y
  where
    x≄y : x ≄ y
    x≄y x≃y = n≄0 (n≃0→n≃0 n≃0)
      where
        n≃0 =
          begin
            ℤ.fromℕ n
          ≃˘⟨ y-x≃n ⟩
            y - x
          ≃⟨ sub-substᴿ x≃y ⟩
            y - y
          ≃⟨ +-inverseᴿ {y} ⟩
            0
          ∎

pos-diff : ∀ {a b} → a < b ↔ IsPositive (b - a)
pos-diff = ↔-intro <→pos pos→<

-- (b) Addition preserves order
+-preserves-<ᴿ : ∀ {a b c} → a < b → a + c < b + c
+-preserves-<ᴿ {a} {b} {c} a<b =
  pos→< (IsPositive-subst (sym (sub-cancelᴿ {b})) (<→pos a<b))

-- (c) Positive multiplication preserves order
*⁺-preserves-<ᴿ : ∀ {a b c} → IsPositive c → a < b → a * c < b * c
*⁺-preserves-<ᴿ {a} {b} {c} c>0 a<b =
  let [b-a]c>0 = *-preserves-pos (<→pos a<b) c>0
   in pos→< (IsPositive-subst (ℤ.*-distrib-subᴿ {b}) [b-a]c>0)

-- (d) Negation reverses order
neg-reverses-< : ∀ {a b} → a < b → - b < - a
neg-reverses-< {a} {b} a<b = pos→< (IsPositive-subst b-a≃-a-[-b] (<→pos a<b))
  where
    b-a≃-a-[-b] =
      begin
        b - a
      ≃⟨ +-comm {b} ⟩
        - a + b
      ≃˘⟨ ℤ.+-substᴿ (neg-involutive {b}) ⟩
        - a - (- b)
      ∎

-- (e) Order is transitive
<-trans : ∀ {a b c} → a < b → b < c → a < c
<-trans {a} {b} {c} a<b b<c =
    let 0<b-a+c-b = +-preserves-pos (<→pos a<b) (<→pos b<c)
     in pos→< (IsPositive-subst b-a+c-b≃c-a 0<b-a+c-b)
  where
    b-a+c-b≃c-a =
      begin
        b - a + (c - b)
      ≃⟨ +-assoc {b} ⟩
        b + (- a + (c - b))
      ≃⟨ ℤ.+-substᴿ {b} (+-comm { - a}) ⟩
        b + (c - b - a)
      ≃⟨ ℤ.+-substᴿ {b} (ℤ.+-substᴸ (+-comm {c})) ⟩
        b + (- b + c - a)
      ≃⟨ ℤ.+-substᴿ {b} (+-assoc { - b}) ⟩
        b + (- b + (c - a))
      ≃˘⟨ +-assoc {b} ⟩
        b - b + (c - a)
      ≃⟨ ℤ.+-substᴸ (+-inverseᴿ {b}) ⟩
        0 + (c - a)
      ≃⟨ ℤ.+-identityᴸ ⟩
        c - a
      ∎

-- (f) Order trichotomy
data OneOfThree (A B C : Set) : Set where
  1st : A → OneOfThree A B C
  2nd : B → OneOfThree A B C
  3rd : C → OneOfThree A B C

data TwoOfThree (A B C : Set) : Set where
  1∧2 : A → B → TwoOfThree A B C
  1∧3 : A → C → TwoOfThree A B C
  2∧3 : B → C → TwoOfThree A B C

record ExactlyOneOf (A B C : Set) : Set where
  field
    at-least-one : OneOfThree A B C
    at-most-one : ¬ TwoOfThree A B C

order-trichotomy : ∀ {a b} → ExactlyOneOf (a < b) (a ≃ b) (a > b)
order-trichotomy {a} {b} = record { at-least-one = 1≤ ; at-most-one = ≤1 }
  where
    1≤ : OneOfThree (a < b) (a ≃ b) (a > b)
    1≤ with at-least (trichotomy (b - a))
    1≤ | nil b-a≃0 = 2nd (sym (trans (≃ᴸ-subᴿ-toᴸ b-a≃0) ℤ.+-identityᴿ))
    1≤ | pos b-a>0 = 1st (pos→< b-a>0)
    1≤ | neg b-a<0 = 3rd (pos→< (sub-sign-swap {b} b-a<0))

    ≤1 : ¬ TwoOfThree (a < b) (a ≃ b) (a > b)
    ≤1 (1∧2 (<-intro a≤b a≄b) a≃b) = a≄b a≃b
    ≤1 (1∧3 (<-intro a≤b a≄b) (<-intro b≤a b≄a)) = a≄b (≤-antisym a≤b b≤a)
    ≤1 (2∧3 a≃b (<-intro b≤a b≄a)) = b≄a (sym a≃b)

-- Exercise 4.1.8
no-ind : ¬ ((P : ℤ → Set) → P 0 → (∀ {b} → P b → P (step b)) → ∀ a → P a)
no-ind ind = ¬allP (ind P Pz Ps)
  where
    P : ℤ → Set
    P x = 0 ≤ x

    Pz : P 0
    Pz = ≤-intro 0 ≃ᶻ-intro

    Ps : ∀ {b} → P b → P (step b)
    Ps {b} (≤-intro n (≃ᶻ-intro {{b⁺+0≃n+b⁻}})) =
        ≤-intro (stepᴺ n) (≃ᶻ-intro {{sb⁺+0≃sn+sb⁻}})
      where
        sb⁺+0≃sn+sb⁻ =
          begin
            ℤ⁺ (step b) +ᴺ 0
          ≃⟨ +ᴺ-substᴸ (ℤ⁺s≃sℤ⁺ {b}) ⟩
            stepᴺ (ℤ⁺ b) +ᴺ 0
          ≃⟨⟩
            stepᴺ (ℤ⁺ b +ᴺ 0)
          ≃⟨ stepᴺ-subst b⁺+0≃n+b⁻ ⟩
            stepᴺ (n +ᴺ ℤ⁻ b)
          ≃˘⟨ +ᴺ-stepᴸ {n} ⟩
            stepᴺ n +ᴺ ℤ⁻ b
          ≃˘⟨ +ᴺ-substᴿ (ℤ⁻s≃ℤ⁻ {b}) ⟩
            stepᴺ n +ᴺ ℤ⁻ (step b)
          ∎

    ¬allP : ¬ (∀ a → P a)
    ¬allP 0≰a =
      let ≤-intro n (≃ᶻ-intro {{0≃n+1}}) = 0≰a -1
       in stepᴺ≄zero (trans stepᴺ≃+ (sym 0≃n+1))
