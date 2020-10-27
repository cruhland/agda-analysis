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
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Logic using
  (⊤; ⊤-intro; ∧-elimᴿ; _∨_; ∨-introᴸ; ∨-introᴿ; ⊥; ⊥-elim; ¬_; _↔_; ↔-intro)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)
open import net.cruhland.models.Setoid using (Setoid₀)

module ℕ = PeanoArithmetic peanoArithmetic
open ℕ using (ℕ) renaming (_*_ to _*ᴺ_)
import net.cruhland.models.Integers peanoArithmetic as ℤ
open ℤ using
  ( _—_; _*_; -_; _-_; _≤_; _<_; _>_; a≃b+c≃d; AtLeastOne; ExactlyOneOf
  ; ≃ᶻ-intro; IsNegative; IsPositive; MoreThanOne; neg; nil; pos; transpose
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
_ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → a₁ + b ≃ a₂ + b
_ = ℤ.+-substᴸ

_ : {a b₁ b₂ : ℤ} → b₁ ≃ b₂ → a + b₁ ≃ a + b₂
_ = ℤ.+-substᴿ

_ : ∀ {a₁ a₂ b} → a₁ ≃ a₂ → a₁ * b ≃ a₂ * b
_ = ℤ.*-substᴸ

*-substᴿ : ∀ {a b₁ b₂} → b₁ ≃ b₂ → a * b₁ ≃ a * b₂
*-substᴿ {a} = ℤ.*-substᴿ {a}

-- The integers n—0 behave in the same way as the natural numbers n;
-- indeed one can check that (n—0) + (m—0) = (n + m)—0 and
-- (n—0) × (m—0) = nm—0.
_ : ∀ {n m} → n — 0 + m — 0 ≃ (n + m) — 0
_ = ≃ᶻ-intro

*-compat-*ᴺ : ∀ {n m} → n — 0 * m — 0 ≃ (n *ᴺ m) — 0
*-compat-*ᴺ {n} {m} = ≃ᶻ-intro {{eq′}}
  where
    eq′ =
      begin
        n *ᴺ m + 0 + 0
      ≃⟨ ℕ.+-assoc {n *ᴺ m} ⟩
        n *ᴺ m + (0 + 0)
      ≃˘⟨ ℕ.+-substᴿ (ℕ.+-substᴸ {m = 0} (ℕ.*-zeroᴿ {n})) ⟩
        n *ᴺ m + (n *ᴺ 0 + 0)
      ∎

-- Furthermore, (n—0) is equal to (m—0) if and only if n = m.
_ : ∀ {n m} → n — 0 ≃ m — 0 ↔ n ≃ m
_ = ↔-intro (ℕ.+-cancelᴿ ∘ ≃ᶻ-elim) (λ n≃m → ≃ᶻ-intro {{ℕ.+-substᴸ n≃m}})

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

ℤ⁺s≃sℤ⁺ : ∀ {a} → ℤ⁺ (step a) ≃ ℕ.step (ℤ⁺ a)
ℤ⁺s≃sℤ⁺ {a⁺ — _} = sym ℕ.step≃+

ℤ⁻s≃ℤ⁻ : ∀ {a} → ℤ⁻ (step a) ≃ ℤ⁻ a
ℤ⁻s≃ℤ⁻ {_ — a⁻} = ℕ.+-zeroᴿ

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

_ : ∀ {n} → - (ℤ.fromℕ n) ≃ 0 — n
_ = ≃ᶻ-intro

-- For instance -(3—5) = (5—3).
_ : -(3 — 5) ≃ 5 — 3
_ = ≃ᶻ-intro

-- One can check this definition is well-defined.
-- Exercise 4.1.2
_ : ∀ {a₁ a₂} → a₁ ≃ a₂ → - a₁ ≃ - a₂
_ = ℤ.neg-subst

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

_ : {x : ℤ} → 0 + x ≃ x
_ = ℤ.+-identityᴸ

_ : {x : ℤ} → x + 0 ≃ x
_ = ℤ.+-identityᴿ

+-inverseᴸ : ∀ {x} → - x + x ≃ 0
+-inverseᴸ {x} = ℤ.+-inverseᴸ {x}

+-inverseᴿ : ∀ {x} → x + - x ≃ 0
+-inverseᴿ {x} = ℤ.+-inverseᴿ {x}

*-comm : ∀ {x y} → x * y ≃ y * x
*-comm {x} = ℤ.*-comm {x}

*-assoc : ∀ {x y z} → (x * y) * z ≃ x * (y * z)
*-assoc {x} = ℤ.*-assoc {x}

*-identityᴸ : ∀ {x} → 1 * x ≃ x
*-identityᴸ {x⁺ — x⁻} = ≃ᶻ-intro {{eq′}}
  where
    eq′ =
      begin
        ((x⁺ + 0) + 0) + x⁻
      ≃⟨ ℕ.+-assoc {x⁺ + 0} ⟩
        (x⁺ + 0) + (0 + x⁻)
      ≃⟨ ℕ.+-substᴿ {x⁺ + 0} (ℕ.+-comm {0}) ⟩
        (x⁺ + 0) + (x⁻ + 0)
      ≃⟨ ℕ.+-assoc {x⁺} ⟩
        x⁺ + (0 + (x⁻ + 0))
      ≃⟨ ℕ.+-substᴿ {x⁺} (ℕ.+-comm {0}) ⟩
        x⁺ + ((x⁻ + 0) + 0)
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
natsub {a} = ≃ᶻ-intro {{ℕ.+-substᴸ (ℕ.+-zeroᴿ {a})}}

-- Proposition 4.1.8 (Integers have no zero divisors). Let a and b be
-- integers such that ab = 0. Then either a = 0 or b = 0 (or both).
-- Exercise 4.1.5
_ : ∀ {a b} → a * b ≃ 0 → a ≃ 0 ∨ b ≃ 0
_ = ℤ.*-either-zero

-- Corollary 4.1.9 (Cancellation law for integers). If a, b, c are
-- integers such that ac = bc and c is non-zero, then a = b.
-- Exercise 4.1.6
_ : ∀ {a b c} → c ≄ 0 → a * c ≃ b * c → a ≃ b
_ = ℤ.*-cancelᴿ

-- Definition 4.1.10 (Ordering of the integers). Let n and m be
-- integers. We say that n is _greater than or equal to_ m, and write
-- n ≥ m or m ≤ n, iff we have n = m + a for some natural number a. We
-- say that n is _strictly greater than_ m and write n > m or m < n,
-- iff n ≥ m and n ≠ m.
_ : ℤ → ℤ → Set
_ = _≤_

_ : ℤ → ℤ → Set
_ = _<_

_ : ℤ → ℤ → Set
_ = _>_

_ : Negative ℤ
_ = ℤ.negative

_ : 5 > -3
_ = ℤ.<-intro (ℤ.≤-intro 8 ≃ᶻ-intro) λ ()

-- Lemma 4.1.11 (Properties of order).
-- Exercise 4.1.7
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

IsPositive-subst : ∀ {a₁ a₂} → a₁ ≃ a₂ → IsPositive a₁ → IsPositive a₂
IsPositive-subst a₁≃a₂ record { n = n ; pos = n≄0 ; x≃n = a₁≃n } =
  record { n = n ; pos = n≄0 ; x≃n = trans (sym a₁≃a₂) a₁≃n }

-- Exercise 4.1.3
_ : ∀ {a} → - a ≃ -1 * a
_ = ℤ.neg-mult

sub-distrib : ∀ {a b c} → a - (b + c) ≃ a - b - c
sub-distrib {a} {b} {c} =
  begin
    a - (b + c)
  ≃⟨⟩
    a + -(b + c)
  ≃⟨ ℤ.+-substᴿ {a} ℤ.neg-mult ⟩
    a + -1 * (b + c)
  ≃⟨ ℤ.+-substᴿ {a} (*-distrib-+ᴸ { -1} {b}) ⟩
    a + (-1 * b + -1 * c)
  ≃˘⟨ ℤ.+-substᴿ {a} (ℤ.+-substᴸ (ℤ.neg-mult {b})) ⟩
    a + (- b + -1 * c)
  ≃˘⟨ ℤ.+-substᴿ {a} (ℤ.+-substᴿ (ℤ.neg-mult {c})) ⟩
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
    record { n = aᴺ + bᴺ ; pos = ℕ.+-positive aᴺ≄0 ; x≃n = a+b≃aᴺ+bᴺ }
  where
    a+b≃aᴺ+bᴺ =
      begin
        a + b
      ≃⟨ ℤ.+-substᴸ a≃aᴺ ⟩
        ℤ.fromℕ aᴺ + b
      ≃⟨ ℤ.+-substᴿ b≃bᴺ ⟩
        ℤ.fromℕ aᴺ + ℤ.fromℕ bᴺ
      ≃˘⟨ ℤ.+-to-+ {aᴺ} ⟩
        ℤ.fromℕ (aᴺ + bᴺ)
      ∎

*-preserves-pos : ∀ {a b} → IsPositive a → IsPositive b → IsPositive (a * b)
*-preserves-pos {a} {b}
  record { n = aᴺ ; pos = aᴺ≄0 ; x≃n = a≃aᴺ }
  record { n = bᴺ ; pos = bᴺ≄0 ; x≃n = b≃bᴺ } =
    record { n = aᴺ *ᴺ bᴺ ; pos = ℕ.*-positive aᴺ≄0 bᴺ≄0 ; x≃n = ab≃aᴺbᴺ }
  where
    ab≃aᴺbᴺ =
      begin
        a * b
      ≃⟨ ℤ.*-substᴸ a≃aᴺ ⟩
        ℤ.fromℕ aᴺ * b
      ≃⟨ *-substᴿ {ℤ.fromℕ aᴺ} b≃bᴺ ⟩
        ℤ.fromℕ aᴺ * ℤ.fromℕ bᴺ
      ≃˘⟨ ℤ.*ᴺ-to-* {aᴺ} ⟩
        ℤ.fromℕ (aᴺ *ᴺ bᴺ)
      ∎

-- (a)
<→pos : ∀ {x y} → x < y → IsPositive (y - x)
<→pos {x} {y} (ℤ.<-intro (ℤ.≤-intro a y≃x+a) x≄y) =
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
          ≃˘⟨ ℤ.+-substᴿ (ℤ.ℕ≃→ℤ≃ a≃0) ⟩
            x + ℤ.fromℕ a
          ≃˘⟨ y≃x+a ⟩
            y
          ∎

pos-diff : ∀ {a b} → a < b ↔ IsPositive (b - a)
pos-diff = ↔-intro <→pos ℤ.pos→<

-- (b) Addition preserves order
+-preserves-<ᴿ : ∀ {a b c} → a < b → a + c < b + c
+-preserves-<ᴿ {a} {b} {c} a<b =
  ℤ.pos→< (IsPositive-subst (sym (sub-cancelᴿ {b})) (<→pos a<b))

-- (c) Positive multiplication preserves order
*⁺-preserves-<ᴿ : ∀ {a b c} → IsPositive c → a < b → a * c < b * c
*⁺-preserves-<ᴿ {a} {b} {c} c>0 a<b =
  let [b-a]c>0 = *-preserves-pos (<→pos a<b) c>0
   in ℤ.pos→< (IsPositive-subst (ℤ.*-distrib-subᴿ {b}) [b-a]c>0)

-- (d) Negation reverses order
neg-reverses-< : ∀ {a b} → a < b → - b < - a
neg-reverses-< {a} {b} a<b = ℤ.pos→< (IsPositive-subst b-a≃-a-[-b] (<→pos a<b))
  where
    b-a≃-a-[-b] =
      begin
        b - a
      ≃⟨ +-comm {b} ⟩
        - a + b
      ≃˘⟨ ℤ.+-substᴿ (ℤ.neg-involutive {b}) ⟩
        - a - (- b)
      ∎

-- (e) Order is transitive
<-trans : ∀ {a b c} → a < b → b < c → a < c
<-trans {a} {b} {c} a<b b<c =
    let 0<b-a+c-b = +-preserves-pos (<→pos a<b) (<→pos b<c)
     in ℤ.pos→< (IsPositive-subst b-a+c-b≃c-a 0<b-a+c-b)
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
_ : ∀ a b → ExactlyOneOf (a < b) (a ≃ b) (a > b)
_ = ℤ.order-trichotomy

-- Exercise 4.1.8
no-ind : ¬ ((P : ℤ → Set) → P 0 → (∀ {b} → P b → P (step b)) → ∀ a → P a)
no-ind ind = ¬allP (ind P Pz Ps)
  where
    P : ℤ → Set
    P x = 0 ≤ x

    Pz : P 0
    Pz = ℤ.≤-intro 0 ≃ᶻ-intro

    Ps : ∀ {b} → P b → P (step b)
    Ps {b} (ℤ.≤-intro n (≃ᶻ-intro {{b⁺+0≃n+b⁻}})) =
        ℤ.≤-intro (ℕ.step n) (≃ᶻ-intro {{sb⁺+0≃sn+sb⁻}})
      where
        sb⁺+0≃sn+sb⁻ =
          begin
            ℤ⁺ (step b) + 0
          ≃⟨ ℕ.+-substᴸ (ℤ⁺s≃sℤ⁺ {b}) ⟩
            ℕ.step (ℤ⁺ b) + 0
          ≃⟨⟩
            ℕ.step (ℤ⁺ b + 0)
          ≃⟨ ℕ.step-subst b⁺+0≃n+b⁻ ⟩
            ℕ.step (n + ℤ⁻ b)
          ≃˘⟨ ℕ.+-stepᴸ {n} ⟩
            ℕ.step n + ℤ⁻ b
          ≃˘⟨ ℕ.+-substᴿ (ℤ⁻s≃ℤ⁻ {b}) ⟩
            ℕ.step n + ℤ⁻ (step b)
          ∎

    ¬allP : ¬ (∀ a → P a)
    ¬allP 0≰a =
      let ℤ.≤-intro n (≃ᶻ-intro {{0≃n+1}}) = 0≰a -1
       in ℕ.step≄zero (trans ℕ.step≃+ (sym 0≃n+1))
