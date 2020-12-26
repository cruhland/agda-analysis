module net.cruhland.Analysis.Chapter4.Integers where

import Agda.Builtin.FromNeg as FromNeg
import Agda.Builtin.Nat as Nat
open import Function using (_∘_; const; flip)
open import Relation.Binary using (IsEquivalence)
open import Relation.Nullary.Decidable using (fromWitnessFalse)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.DecEq using (≃-derive ; ≄-derive)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; Eq; refl; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_; _*_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals as Literals
open import net.cruhland.models.Logic using
  (⊤; ∧-elimᴿ; _∨_; ∨-introᴸ; ∨-introᴿ; ⊥; ⊥-elim; ¬_; _↔_; ↔-intro)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)
open import net.cruhland.models.Setoid using (Setoid₀)

module ℕ = PeanoArithmetic peanoArithmetic
open ℕ using (ℕ)
import net.cruhland.models.Integers peanoArithmetic as ℤ
open ℤ using (_—_; _≤_; _<_; _>_; ≃ᶻ-intro; ℤ)

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
_ = ≃-derive

_ : 3 — 5 ≄ 2 — 3
_ = ≄-derive

-- Exercise 4.1.1
_ : Eq ℤ
_ = ℤ.eq

-- Definition 4.1.2. The sum of two integers, (a—b) + (c—d), is
-- defined by the formula (a—b) + (c—d) ≔ (a + c)—(b + d).
_ : ℤ → ℤ → ℤ
_ = _+_ {{ℤ.plus}}

-- The product of two integers, (a—b) × (c—d), is defined by
-- (a—b) × (c—d) ≔ (ac + bd)—(ad + bc).
_ : ℤ → ℤ → ℤ
_ = _*_ {{ℤ.star}}

-- Thus for instance, (3—5) + (1—4) is equal to (4—9).
_ : 3 — 5 + 1 — 4 ≃ 4 — 9
_ = ≃-derive

-- There is however one thing we have to check before we can accept
-- these definitions - we have to check that if we replace one of the
-- integers by an equal integer, that the sum or product does not
-- change. For instance (3—5) is equal to (2—4), so (3—5) + (1—4)
-- ought to have the same value as (2—4) + (1—4), otherwise this would
-- not give a consistent definition of addition.
_ : 3 — 5 + 1 — 4 ≃ 2 — 4 + 1 — 4
_ = ≃-derive

-- Lemma 4.1.3 (Addition and multiplication are well-defined).
_ : {a b₁ b₂ : ℤ} → b₁ ≃ b₂ → b₁ + a ≃ b₂ + a
_ = AA.subst {{r = ℤ.+-substitutiveᴸ}}

_ : {a b₁ b₂ : ℤ} → b₁ ≃ b₂ → a + b₁ ≃ a + b₂
_ = AA.subst {{r = ℤ.+-substitutiveᴿ}}

_ : {a b₁ b₂ : ℤ} → b₁ ≃ b₂ → b₁ * a ≃ b₂ * a
_ = AA.subst {{r = ℤ.*-substitutiveᴸ}}

*-substᴿ : {a b₁ b₂ : ℤ} → b₁ ≃ b₂ → a * b₁ ≃ a * b₂
*-substᴿ {a} = AA.subst {{r = ℤ.*-substitutiveᴿ {a}}}

-- The integers n—0 behave in the same way as the natural numbers n;
-- indeed one can check that (n—0) + (m—0) = (n + m)—0 and
-- (n—0) × (m—0) = nm—0.
_ : ∀ {n m} → n — 0 + m — 0 ≃ (n + m) — 0
_ = ≃ᶻ-intro refl

*-compat-* : ∀ {n m} → n — 0 * m — 0 ≃ (n * m) — 0
*-compat-* {n} {m} = ≃ᶻ-intro eq′
  where
    eq′ =
      begin
        n * m + 0 + 0
      ≃⟨ AA.assoc {a = n * m} ⟩
        n * m + (0 + 0)
      ≃˘⟨ AA.subst {f = n * m +_}
                   (AA.subst {{r = ℕ.+-substitutiveᴸ}} (AA.absorbᴿ {a = n})) ⟩
        n * m + (n * 0 + 0)
      ∎

-- Furthermore, (n—0) is equal to (m—0) if and only if n = m.
_ : ∀ {n m} → n — 0 ≃ m — 0 ↔ n ≃ m
_ = ↔-intro (AA.cancelᴿ ∘ ℤ._≃ᶻ_.elim)
            (≃ᶻ-intro ∘ AA.subst {{r = ℕ.+-substitutiveᴸ}})

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
_ : Literals.Number ℤ
_ = ℤ.number

-- For instance the natural number 3 is now considered to be the same
-- as the integer 3—0, thus 3 = 3—0.
_ : 3 ≃ 3 — 0
_ = ≃-derive

-- In particular 0 is equal to 0—0 and 1 is equal to 1—0.
_ : 0 ≃ 0 — 0
_ = ≃-derive

_ : 1 ≃ 1 — 0
_ = ≃-derive

-- Of course, if we set n equal to n—0, then it will also be equal to
-- any other integer which is equal to n—0, for instance 3 is equal
-- not only to 3—0, but also to 4—1, 5—2, etc.
_ : 3 ≃ 4 — 1
_ = ≃-derive

_ : 3 ≃ 5 — 2
_ = ≃-derive

-- We can now define incrementation on the integers by defining
-- step x ≔ x + 1 for any integer x; this is of course consistent with
-- our definition of the increment operation for natural
-- numbers. However, this is no longer an important operation for us,
-- as it has been now superceded by the more general notion of
-- addition.
step : ℤ → ℤ
step x = x + 1

ℤ⁺s≃sℤ⁺ : ∀ {a} → ℤ.ℤ.pos (step a) ≃ ℕ.step (ℤ.ℤ.pos a)
ℤ⁺s≃sℤ⁺ {a⁺ — _} = sym ℕ.sn≃n+1

ℤ⁻s≃ℤ⁻ : ∀ {a} → ℤ.ℤ.neg (step a) ≃ ℤ.ℤ.neg a
ℤ⁻s≃ℤ⁻ {_ — a⁻} = AA.identᴿ

-- Definition 4.1.4 (Negation of integers). If (a—b) is an integer, we
-- define the negation -(a—b) to be the integer (b—a).
_ : ℤ → ℤ
_ = -_ {{ℤ.neg-dash}}

-- In particular if n = n—0 is a positive natural number, we can
-- define its negation -n = 0—n.
-- [note] Here we must use a conversion function since n is not a
-- literal.
_ : ℕ → ℤ
_ = λ n → (n as ℤ) {{ℤ.from-ℕ}}

_ : ∀ {n} → - (n as ℤ) ≃ 0 — n
_ = ≃ᶻ-intro refl

-- For instance -(3—5) = (5—3).
_ : -(3 — 5) ≃ 5 — 3
_ = ≃-derive

-- One can check this definition is well-defined.
-- Exercise 4.1.2
_ : {a₁ a₂ : ℤ} → a₁ ≃ a₂ → - a₁ ≃ - a₂
_ = AA.subst {{r = ℤ.neg-substitutive}}

-- Lemma 4.1.5 (Trichotomy of integers). Let x be an integer. Then
-- exactly one of the following three statements is true: (a) x is
-- zero; (b) x is equal to a positive natural number n; or (c) x is
-- the negation -n of a positive natural number n.
_ : ∀ x → AA.ExactlyOneOfThree (ℤ.Negative x) (x ≃ 0) (ℤ.Positive x)
_ = ℤ.trichotomy

-- Proposition 4.1.6 (Laws of algebra for integers).
-- Exercise 4.1.4
+-comm : ∀ {x y} → x + y ≃ y + x
+-comm {x} = AA.comm {{r = ℤ.+-commutative}} {a = x}

+-assoc : ∀ {x y z} → (x + y) + z ≃ x + (y + z)
+-assoc {x} = AA.assoc {{r = ℤ.+-associative}} {a = x}

_ : {x : ℤ} → 0 + x ≃ x
_ = AA.identᴸ {{r = ℤ.+-identityᴸ}}

_ : {x : ℤ} → x + 0 ≃ x
_ = AA.identᴿ {{r = ℤ.+-identityᴿ}}

+-invᴸ : {x : ℤ} → - x + x ≃ 0
+-invᴸ {x} = AA.invᴸ {{r = ℤ.+-inverseᴸ}} {a = x}

+-invᴿ : {x : ℤ} → x + - x ≃ 0
+-invᴿ {x} = AA.invᴿ {{r = ℤ.+-inverseᴿ}} {a = x}

*-comm : {x y : ℤ} → x * y ≃ y * x
*-comm {x} = AA.comm {a = x}

*-assoc : {x y z : ℤ} → (x * y) * z ≃ x * (y * z)
*-assoc {x} = AA.assoc {a = x}

_ : {x : ℤ} → 1 * x ≃ x
_ = AA.identᴸ {{r = ℤ.*-identityᴸ}}

_ : {x : ℤ} → x * 1 ≃ x
_ = AA.identᴿ {{r = ℤ.*-identityᴿ}}

*-distrib-+ᴸ : {x y z : ℤ} → x * (y + z) ≃ x * y + x * z
*-distrib-+ᴸ {x} = AA.distribᴸ {{r = ℤ.*-distributive-+ᴸ}} {a = x}

*-distrib-+ᴿ : {x y z : ℤ} → (y + z) * x ≃ y * x + z * x
*-distrib-+ᴿ {x} {y} = AA.distribᴿ {{r = ℤ.*-distributive-+ᴿ}} {a = x} {b = y}

-- We now define the operation of _subtraction_ x - y of two integers
-- by the formula x - y ≔ x + (-y).
_ : ℤ → ℤ → ℤ
_ = _-_

-- One can easily check now that if a and b are natural numbers, then
-- a - b = a + -b = (a—0) + (0—b) = a—b, and so a—b is just the same
-- thing as a - b. Because of this we can now discard the — notation,
-- and use the familiar operation of subtraction instead.
natsub : ∀ {a b} → (a as ℤ) - (b as ℤ) ≃ a — b
natsub {a} = ≃ᶻ-intro (AA.subst (AA.identᴿ {a = a}))

-- Proposition 4.1.8 (Integers have no zero divisors). Let a and b be
-- integers such that ab = 0. Then either a = 0 or b = 0 (or both).
-- Exercise 4.1.5
_ : {a b : ℤ} → a * b ≃ 0 → a ≃ 0 ∨ b ≃ 0
_ = AA.zero-prod {{r = ℤ.zero-product}}

-- Corollary 4.1.9 (Cancellation law for integers). If a, b, c are
-- integers such that ac = bc and c is non-zero, then a = b.
-- Exercise 4.1.6
_ : {a b c : ℤ} → c ≄ 0 → a * c ≃ b * c → a ≃ b
_ = λ c≄0 → AA.cancelᴿ {{r = ℤ.*-cancellativeᴿ}} {{c = fromWitnessFalse c≄0}}

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

_ : FromNeg.Negative ℤ
_ = ℤ.negative

_ : 5 > -3
_ = ℤ.<-intro (ℤ.≤-intro 8 ≃-derive) λ ()

-- Lemma 4.1.11 (Properties of order).
-- Exercise 4.1.7
≃ᴿ-+ᴸ-toᴿ : {a b c : ℤ} → a ≃ b + c → a - b ≃ c
≃ᴿ-+ᴸ-toᴿ {a} {b} {c} a≃b+c =
  begin
    a - b
  ≃⟨ ℤ.sub-substᴸ a≃b+c ⟩
    b + c - b
  ≃⟨ ℤ.sub-substᴸ (AA.comm {a = b}) ⟩
    c + b - b
  ≃⟨ AA.assoc {a = c} ⟩
    c + (b - b)
  ≃⟨ AA.subst {{r = ℤ.+-substitutiveᴿ}} (AA.invᴿ {a = b}) ⟩
    c + 0
  ≃⟨ AA.identᴿ ⟩
    c
  ∎

vanish : {x y : ℤ} → x + y - y ≃ x
vanish {x} {y} =
  begin
    x + y - y
  ≃⟨ AA.assoc {a = x} ⟩
    x + (y - y)
  ≃⟨ AA.subst {{r = ℤ.+-substitutiveᴿ}} (AA.invᴿ {a = y}) ⟩
    x + 0
  ≃⟨ AA.identᴿ ⟩
    x
  ∎

Positive-subst : ∀ {a₁ a₂} → a₁ ≃ a₂ → ℤ.Positive a₁ → ℤ.Positive a₂
Positive-subst a₁≃a₂ record { n = n ; pos = n≄0 ; x≃n = a₁≃n } =
  record { n = n ; pos = n≄0 ; x≃n = trans (sym a₁≃a₂) a₁≃n }

-- Exercise 4.1.3
_ : {a : ℤ} → - a ≃ -1 * a
_ = ℤ.neg-mult

sub-distrib : ∀ {a b c} → a - (b + c) ≃ a - b - c
sub-distrib {a} {b} {c} =
  begin
    a - (b + c)
  ≃⟨⟩
    a + -(b + c)
  ≃⟨ AA.subst {{r = ℤ.+-substitutiveᴿ {a}}} ℤ.neg-mult ⟩
    a + -1 * (b + c)
  ≃⟨ AA.subst {{r = ℤ.+-substitutiveᴿ {a}}} (AA.distribᴸ {a = -1} {b}) ⟩
    a + (-1 * b + -1 * c)
  ≃˘⟨ AA.subst
        {{r = ℤ.+-substitutiveᴿ {a}}}
        (AA.subst {{r = ℤ.+-substitutiveᴸ}} (ℤ.neg-mult {b})) ⟩
    a + (- b + -1 * c)
  ≃˘⟨ AA.subst
        {{r = ℤ.+-substitutiveᴿ {a}}}
        (AA.subst {{r = ℤ.+-substitutiveᴿ}} (ℤ.neg-mult {c})) ⟩
    a + (- b + - c)
  ≃˘⟨ AA.assoc {a = a} ⟩
    a - b - c
  ∎

sub-cancelᴿ : {a b c : ℤ} → a + c - (b + c) ≃ a - b
sub-cancelᴿ {a} {b} {c} =
  begin
    a + c - (b + c)
  ≃⟨ sub-distrib {a + c} ⟩
    a + c - b - c
  ≃⟨⟩
    ((a + c) + - b) + - c
  ≃⟨ AA.subst {{r = ℤ.+-substitutiveᴸ { - c}}} (AA.assoc {a = a}) ⟩
    (a + (c + - b)) + - c
  ≃⟨ AA.subst
       {{r = ℤ.+-substitutiveᴸ { - c}}}
       (AA.subst {{r = ℤ.+-substitutiveᴿ {a}}} (AA.comm {a = c})) ⟩
    (a + (- b + c)) + - c
  ≃˘⟨ AA.subst {{r = ℤ.+-substitutiveᴸ { - c}}} (AA.assoc {a = a}) ⟩
    ((a + - b) + c) + - c
  ≃⟨⟩
    a - b + c - c
  ≃⟨ vanish ⟩
    a - b
  ∎

+-preserves-pos : ∀ {a b} → ℤ.Positive a → ℤ.Positive b → ℤ.Positive (a + b)
+-preserves-pos {a} {b}
  record { n = aᴺ ; pos = aᴺ≄0 ; x≃n = a≃aᴺ }
  record { n = bᴺ ; pos = bᴺ≄0 ; x≃n = b≃bᴺ } =
    record { n = aᴺ + bᴺ ; pos = ℕ.+-positive aᴺ≄0 ; x≃n = a+b≃aᴺ+bᴺ }
  where
    a+b≃aᴺ+bᴺ =
      begin
        a + b
      ≃⟨ AA.subst {{r = ℤ.+-substitutiveᴸ {b}}} a≃aᴺ ⟩
        (aᴺ as ℤ) + b
      ≃⟨ AA.subst {{r = ℤ.+-substitutiveᴿ {aᴺ as ℤ}}} b≃bᴺ ⟩
        (aᴺ as ℤ) + (bᴺ as ℤ)
      ≃˘⟨ AA.compat₂ {a = aᴺ} ⟩
        (aᴺ + bᴺ as ℤ)
      ∎

*-preserves-pos : ∀ {a b} → ℤ.Positive a → ℤ.Positive b → ℤ.Positive (a * b)
*-preserves-pos {a} {b}
  record { n = aᴺ ; pos = aᴺ≄0 ; x≃n = a≃aᴺ }
  record { n = bᴺ ; pos = bᴺ≄0 ; x≃n = b≃bᴺ } =
    record { n = aᴺ * bᴺ ; pos = AA.nonzero-prod aᴺ≄0 bᴺ≄0 ; x≃n = ab≃aᴺbᴺ }
  where
    ab≃aᴺbᴺ =
      begin
        a * b
      ≃⟨ AA.subst {{r = ℤ.*-substitutiveᴸ}} a≃aᴺ ⟩
        (aᴺ as ℤ) * b
      ≃⟨ AA.subst {{r = ℤ.*-substitutiveᴿ {aᴺ as ℤ}}} b≃bᴺ ⟩
        (aᴺ as ℤ) * (bᴺ as ℤ)
      ≃˘⟨ AA.compat₂ {a = aᴺ} ⟩
        (aᴺ * bᴺ as ℤ)
      ∎

-- (a)
<→pos : ∀ {x y} → x < y → ℤ.Positive (y - x)
<→pos {x} {y} (ℤ.<-intro (ℤ.≤-intro a y≃x+a) x≄y) =
    record { n = a ; pos = a≄0 ; x≃n = ≃ᴿ-+ᴸ-toᴿ y≃x+a }
  where
    a≄0 : a ≄ 0
    a≄0 a≃0 = x≄y x≃y
      where
        x≃y =
          begin
            x
          ≃˘⟨ AA.identᴿ ⟩
            x + 0
          ≃˘⟨ AA.subst {{r = ℤ.+-substitutiveᴿ}}
                (AA.subst {{r = ℤ.from-ℕ-substitutive₁}} a≃0) ⟩
            x + (a as ℤ)
          ≃˘⟨ y≃x+a ⟩
            y
          ∎

pos-diff : ∀ {a b} → a < b ↔ ℤ.Positive (b - a)
pos-diff = ↔-intro <→pos ℤ.pos→<

-- (b) Addition preserves order
+-preserves-<ᴿ : ∀ {a b c} → a < b → a + c < b + c
+-preserves-<ᴿ {a} {b} {c} a<b =
  ℤ.pos→< (Positive-subst (sym (sub-cancelᴿ {b})) (<→pos a<b))

-- (c) Positive multiplication preserves order
*⁺-preserves-<ᴿ : ∀ {a b c} → ℤ.Positive c → a < b → a * c < b * c
*⁺-preserves-<ᴿ {a} {b} {c} c>0 a<b =
  let [b-a]c>0 = *-preserves-pos (<→pos a<b) c>0
   in ℤ.pos→< (Positive-subst (ℤ.*-distrib-subᴿ {b}) [b-a]c>0)

-- (d) Negation reverses order
neg-reverses-< : ∀ {a b} → a < b → - b < - a
neg-reverses-< {a} {b} a<b = ℤ.pos→< (Positive-subst b-a≃-a-[-b] (<→pos a<b))
  where
    b-a≃-a-[-b] =
      begin
        b - a
      ≃⟨ AA.comm {a = b} ⟩
        - a + b
      ≃˘⟨ AA.subst {{r = ℤ.+-substitutiveᴿ}} (ℤ.neg-involutive {b}) ⟩
        - a - (- b)
      ∎

-- (e) Order is transitive
<-trans : ∀ {a b c} → a < b → b < c → a < c
<-trans {a} {b} {c} a<b b<c =
    let 0<b-a+c-b = +-preserves-pos (<→pos a<b) (<→pos b<c)
     in ℤ.pos→< (Positive-subst b-a+c-b≃c-a 0<b-a+c-b)
  where
    b-a+c-b≃c-a =
      begin
        b - a + (c - b)
      ≃⟨ AA.assoc {a = b} ⟩
        b + (- a + (c - b))
      ≃⟨ AA.subst {{r = ℤ.+-substitutiveᴿ {b}}} (AA.comm {a = - a}) ⟩
        b + (c - b - a)
      ≃⟨ AA.subst {{r = ℤ.+-substitutiveᴿ {b}}}
           (AA.subst {{r = ℤ.+-substitutiveᴸ { - a}}} (AA.comm {a = c})) ⟩
        b + (- b + c - a)
      ≃⟨ AA.subst {{r = ℤ.+-substitutiveᴿ {b}}} (AA.assoc {a = - b}) ⟩
        b + (- b + (c - a))
      ≃˘⟨ AA.assoc {a = b} ⟩
        b - b + (c - a)
      ≃⟨ AA.subst {{r = ℤ.+-substitutiveᴸ}} (AA.invᴿ {a = b}) ⟩
        0 + (c - a)
      ≃⟨ AA.identᴸ ⟩
        c - a
      ∎

-- (f) Order trichotomy
_ : ∀ a b → AA.ExactlyOneOfThree (a < b) (a ≃ b) (a > b)
_ = ℤ.order-trichotomy

-- Exercise 4.1.8
no-ind : ¬ ((P : ℤ → Set) → P 0 → (∀ {b} → P b → P (step b)) → ∀ a → P a)
no-ind ind = ¬allP (ind P Pz Ps)
  where
    P : ℤ → Set
    P x = 0 ≤ x

    Pz : P 0
    Pz = ℤ.≤-intro 0 ≃-derive

    Ps : ∀ {b} → P b → P (step b)
    Ps {b} (ℤ.≤-intro n (≃ᶻ-intro b⁺+0≃n+b⁻)) =
        ℤ.≤-intro (ℕ.step n) (≃ᶻ-intro sb⁺+0≃sn+sb⁻)
      where
        sb⁺+0≃sn+sb⁻ =
          begin
            ℤ.ℤ.pos (step b) + 0
          ≃⟨ AA.subst {{r = ℕ.+-substitutiveᴸ}} (ℤ⁺s≃sℤ⁺ {b}) ⟩
            ℕ.step (ℤ.ℤ.pos b) + 0
          ≃⟨⟩
            ℕ.step (ℤ.ℤ.pos b + 0)
          ≃⟨ AA.subst {{r = ℕ.step-substitutive}} b⁺+0≃n+b⁻ ⟩
            ℕ.step (n + ℤ.ℤ.neg b)
          ≃˘⟨ AA.commᴸ {a = n} ⟩
            ℕ.step n + ℤ.ℤ.neg b
          ≃˘⟨ AA.subst (ℤ⁻s≃ℤ⁻ {b}) ⟩
            ℕ.step n + ℤ.ℤ.neg (step b)
          ∎

    ¬allP : ¬ (∀ a → P a)
    ¬allP 0≰a =
      let ℤ.≤-intro n (≃ᶻ-intro 0≃n+1) = 0≰a -1
       in ℕ.step≄zero (trans ℕ.sn≃n+1 (sym 0≃n+1))
