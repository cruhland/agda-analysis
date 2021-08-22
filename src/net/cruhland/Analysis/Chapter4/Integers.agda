import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.DecEq using (DecEq_~_; ≃-derive; ≄-derive)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_; Eq)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_; _*_; -_; _-_)
open import net.cruhland.axioms.Ordering using (_≤_; _<_; _>_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Literals as Literals
open import net.cruhland.models.Logic
  using (_∨_; _↔_; ↔-intro; ¬_; ¬-intro; _↯_)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)

module net.cruhland.Analysis.Chapter4.Integers where

private
  open module ℕ = PeanoArithmetic peanoArithmetic using (ℕ)
open import net.cruhland.models.Integers.NatPairImpl peanoArithmetic as ℤ
  using (_—_; ℤ)

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
_ = DecEq_~_.eq ℤ.decEq

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
_ = AA.subst₂ {{r = AA.Substitutive²ᶜ.substitutiveᴸ ℤ.+-substitutive}}

_ : {a b₁ b₂ : ℤ} → b₁ ≃ b₂ → a + b₁ ≃ a + b₂
_ = AA.subst₂ {{r = AA.Substitutive²ᶜ.substitutiveᴿ ℤ.+-substitutive}}

_ : {a b₁ b₂ : ℤ} → b₁ ≃ b₂ → b₁ * a ≃ b₂ * a
_ = AA.subst₂ {{r = AA.Substitutive²ᶜ.substitutiveᴸ ℤ.*-substitutive}}

*-substᴿ : {a b₁ b₂ : ℤ} → b₁ ≃ b₂ → a * b₁ ≃ a * b₂
*-substᴿ {a} =
  AA.subst₂ {{r = AA.Substitutive²ᶜ.substitutiveᴿ ℤ.*-substitutive}} {b = a}

-- The integers n—0 behave in the same way as the natural numbers n;
-- indeed one can check that (n—0) + (m—0) = (n + m)—0 and
-- (n—0) × (m—0) = nm—0.
+-compat-ℕ : ∀ {n m} → n — 0 + m — 0 ≃ (n + m) — 0
+-compat-ℕ {n} = Eq.sym (AA.compat₂ {{r = ℤ.+-compatible-ℕ}} {n})

*-compat-ℕ : ∀ {n m} → n — 0 * m — 0 ≃ (n * m) — 0
*-compat-ℕ {n} = Eq.sym (AA.compat₂ {{r = ℤ.*-compatible-ℕ}} {n})

-- Furthermore, (n—0) is equal to (m—0) if and only if n = m.
_ : ∀ {n m} → n — 0 ≃ m — 0 ↔ n ≃ m
_ = ↔-intro (AA.cancel {{r = ℕ.+-cancellativeᴿ}} ∘ ℤ._≃₀_.elim)
            (ℤ.≃₀-intro ∘ AA.substᴸ)

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
_ : Literals.FromNatLiteral ℤ
_ = ℤ.nat-literal

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

ℤ⁺s≃sℤ⁺ : ∀ {a} → ℤ.pos (step a) ≃ ℕ.step (ℤ.pos a)
ℤ⁺s≃sℤ⁺ {a⁺ — _} = Eq.sym ℕ.sn≃n+1

ℤ⁻s≃ℤ⁻ : ∀ {a} → ℤ.neg (step a) ≃ ℤ.neg a
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
_ = ℤ.≃₀-intro Eq.refl

-- For instance -(3—5) = (5—3).
_ : -(3 — 5) ≃ 5 — 3
_ = ≃-derive

-- One can check this definition is well-defined.
-- Exercise 4.1.2
_ : {a₁ a₂ : ℤ} → a₁ ≃ a₂ → - a₁ ≃ - a₂
_ = AA.subst₁ {{r = ℤ.neg-substitutive}}

-- Lemma 4.1.5 (Trichotomy of integers). Let x be an integer. Then
-- exactly one of the following three statements is true: (a) x is
-- zero; (b) x is equal to a positive natural number n; or (c) x is
-- the negation -n of a positive natural number n.
_ : (x : ℤ) → AA.ExactlyOneOfThree (x ≃ 0) (S.Positive x) (S.Negative x)
_ = S.trichotomy {{r = ℤ.sign-trichotomy}}

-- Proposition 4.1.6 (Laws of algebra for integers).
-- Exercise 4.1.4
+-comm : ∀ {x y} → x + y ≃ y + x
+-comm {x} = AA.comm {{r = ℤ.+-commutative}} {a = x}

+-assoc : ∀ {x y z} → (x + y) + z ≃ x + (y + z)
+-assoc {x} = AA.assoc {{r = ℤ.+-associative}} {a = x}

_ : {x : ℤ} → 0 + x ≃ x
_ = AA.ident {{r = AA.Identity².identityᴸ ℤ.+-identity}}

_ : {x : ℤ} → x + 0 ≃ x
_ = AA.ident {{r = AA.Identity².identityᴿ ℤ.+-identity}}

+-invᴸ : {x : ℤ} → - x + x ≃ 0
+-invᴸ {x} = AA.inv {{r = AA.Inverse².inverseᴸ ℤ.neg-inverse}} {a = x}

+-invᴿ : {x : ℤ} → x + - x ≃ 0
+-invᴿ {x} = AA.inv {{r = AA.Inverse².inverseᴿ ℤ.neg-inverse}} {a = x}

*-comm : {x y : ℤ} → x * y ≃ y * x
*-comm {x} = AA.comm {a = x}

*-assoc : {x y z : ℤ} → (x * y) * z ≃ x * (y * z)
*-assoc {x} = AA.assoc {a = x}

_ : {x : ℤ} → 1 * x ≃ x
_ = AA.ident {{r = AA.Identity².identityᴸ ℤ.*-identity}}

_ : {x : ℤ} → x * 1 ≃ x
_ = AA.ident {{r = AA.Identity².identityᴿ ℤ.*-identity}}

*-distrib-+ᴸ : {x y z : ℤ} → x * (y + z) ≃ x * y + x * z
*-distrib-+ᴸ {x} =
  AA.distrib {{r = AA.Distributive².distributiveᴸ ℤ.*-distributive}} {a = x}

*-distrib-+ᴿ : {x y z : ℤ} → (y + z) * x ≃ y * x + z * x
*-distrib-+ᴿ {x} {y} =
  AA.distrib
    {{r = AA.Distributive².distributiveᴿ ℤ.*-distributive}} {a = x} {b = y}

-- We now define the operation of _subtraction_ x - y of two integers
-- by the formula x - y ≔ x + (-y).
_ : ℤ → ℤ → ℤ
_ = _-_

-- One can easily check now that if a and b are natural numbers, then
-- a - b = a + -b = (a—0) + (0—b) = a—b, and so a—b is just the same
-- thing as a - b. Because of this we can now discard the — notation,
-- and use the familiar operation of subtraction instead.
natsub : ∀ {a b} → (a as ℤ) - (b as ℤ) ≃ a — b
natsub {a} {b} =
  begin
    (a as ℤ) - (b as ℤ)
  ≃⟨⟩
    (a — 0) - (b — 0)
  ≃⟨⟩
    (a — 0) + -(b — 0)
  ≃⟨⟩
    (a — 0) + (0 — b)
  ≃⟨⟩
    (a + 0) — (0 + b)
  ≃⟨ AA.subst₂ {b = 0 + b} (AA.ident {_⊙_ = _+_}) ⟩
    a — (0 + b)
  ≃⟨ AA.subst₂ {b = a} AA.ident ⟩
    a — b
  ∎

-- Proposition 4.1.8 (Integers have no zero divisors). Let a and b be
-- integers such that ab = 0. Then either a = 0 or b = 0 (or both).
-- Exercise 4.1.5
_ : {a b : ℤ} → a * b ≃ 0 → a ≃ 0 ∨ b ≃ 0
_ = AA.zero-prod {{r = ℤ.zero-product}}

-- Corollary 4.1.9 (Cancellation law for integers). If a, b, c are
-- integers such that ac = bc and c is non-zero, then a = b.
-- Exercise 4.1.6
_ : {a b c : ℤ} {{_ : c ≄ 0}} → a * c ≃ b * c → a ≃ b
_ = AA.cancel {{r = AA.Cancellative²ᶜ.cancellativeᴿ ℤ.*-cancellative}}

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

_ : Literals.FromNegLiteral ℤ
_ = ℤ.neg-literal

_ : 5 > -3
_ = ℤ.<₀-intro (ℤ.≤₀-intro {d = 8} ≃-derive) ≄-derive

-- Lemma 4.1.11 (Properties of order).
-- Exercise 4.1.7
vanish : {x y : ℤ} → x + y - y ≃ x
vanish {x} {y} =
  begin
    x + y - y
  ≃⟨ AA.assoc {a = x} ⟩
    x + (y - y)
  ≃⟨ AA.subst₂ {b = x} (ℤ.sub-same≃zero {y}) ⟩
    x + 0
  ≃⟨ AA.ident ⟩
    x
  ∎

-- Exercise 4.1.3
_ : {a : ℤ} → - a ≃ -1 * a
_ = Eq.sym ℤ.neg-mult

sub-distrib : {a b c : ℤ} → a - (b + c) ≃ a - b - c
sub-distrib {a} {b} {c} =
  begin
    a - (b + c)
  ≃⟨⟩
    a + -(b + c)
  ≃˘⟨ AA.substᴿ {b = a} ℤ.neg-mult ⟩
    a + -1 * (b + c)
  ≃⟨ AA.substᴿ {b = a} (AA.distrib {_⊕_ = _+_} {a = -1} {b}) ⟩
    a + (-1 * b + -1 * c)
  ≃⟨ AA.substᴿ {b = a} (AA.substᴸ (ℤ.neg-mult {b})) ⟩
    a + (- b + -1 * c)
  ≃⟨ AA.substᴿ {b = a} (AA.substᴿ {b = - b} (ℤ.neg-mult {c})) ⟩
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
  ≃⟨ AA.substᴸ {A = ℤ} {_⊙_ = AA.tc₂ _+_} (AA.assoc {a = a}) ⟩
    (a + (c + - b)) + - c
  ≃⟨ AA.substᴸ
       {A = ℤ} {_⊙_ = AA.tc₂ _+_} (AA.substᴿ {b = a} (AA.comm {a = c})) ⟩
    (a + (- b + c)) + - c
  ≃˘⟨ AA.substᴸ {A = ℤ} {_⊙_ = AA.tc₂ _+_} (AA.assoc {a = a}) ⟩
    ((a + - b) + c) + - c
  ≃⟨⟩
    a - b + c - c
  ≃⟨ vanish ⟩
    a - b
  ∎

-- (a)
pos-diff : {a b : ℤ} → a < b ↔ S.Positive (b - a)
pos-diff = ↔-intro ℤ.pos-from-< ℤ.<-from-pos

-- (b) Addition preserves order
+-preserves-<ᴿ : ∀ {a b c} → a < b → a + c < b + c
+-preserves-<ᴿ {a} {b} {c} a<b =
  ℤ.<-from-pos (AA.subst₁ (Eq.sym (sub-cancelᴿ {b})) (ℤ.pos-from-< a<b))

-- (c) Positive multiplication preserves order
*⁺-preserves-<ᴿ : {a b c : ℤ} → S.Positive c → a < b → a * c < b * c
*⁺-preserves-<ᴿ {a} {b} {c} pos[c] a<b =
  let pos[b-a] = ℤ.pos-from-< a<b
      pos[[b-a]c] = AA.pres {P = S.Positive} {_⊙_ = _*_} pos[b-a] pos[c]
      pos[bc-ac] = AA.subst₁ (AA.distribᴿ {a = c} {b = b} {c = a}) pos[[b-a]c]
   in ℤ.<-from-pos pos[bc-ac]

-- (d) Negation reverses order
neg-reverses-< : {a b : ℤ} → a < b → - b < - a
neg-reverses-< {a} {b} a<b =
    ℤ.<-from-pos (AA.subst₁ b-a≃-a-[-b] (ℤ.pos-from-< a<b))
  where
    b-a≃-a-[-b] =
      begin
        b - a
      ≃⟨ AA.comm {a = b} ⟩
        - a + b
      ≃˘⟨ AA.substᴿ {b = - a} (ℤ.neg-involutive {b}) ⟩
        - a - (- b)
      ∎

-- (e) Order is transitive
<-trans : {a b c : ℤ} → a < b → b < c → a < c
<-trans {a} {b} {c} a<b b<c =
    let 0<b-a+c-b = AA.pres (ℤ.pos-from-< a<b) (ℤ.pos-from-< b<c)
     in ℤ.<-from-pos (AA.subst₁ b-a+c-b≃c-a 0<b-a+c-b)
  where
    b-a+c-b≃c-a =
      begin
        b - a + (c - b)
      ≃⟨ AA.assoc {a = b} ⟩
        b + (- a + (c - b))
      ≃⟨ AA.substᴿ {b = b} (AA.comm {a = - a}) ⟩
        b + (c - b - a)
      ≃⟨ AA.substᴿ
           {b = b} (AA.substᴸ {A = ℤ} {_⊙_ = AA.tc₂ _+_} (AA.comm {a = c})) ⟩
        b + (- b + c - a)
      ≃⟨ AA.substᴿ {b = b} (AA.assoc {a = - b}) ⟩
        b + (- b + (c - a))
      ≃˘⟨ AA.assoc {a = b} ⟩
        b - b + (c - a)
      ≃⟨ AA.substᴸ {A = ℤ} {_⊙_ = AA.tc₂ _+_} (AA.inv {a = b}) ⟩
        0 + (c - a)
      ≃⟨ AA.ident ⟩
        c - a
      ∎

-- (f) Order trichotomy
_ : ∀ a b → AA.ExactlyOneOfThree (a < b) (a ≃ b) (a > b)
_ = ℤ.order-trichotomy

-- Exercise 4.1.8
no-ind : ¬ ((P : ℤ → Set) → P 0 → (∀ {b} → P b → P (step b)) → ∀ a → P a)
no-ind = ¬-intro λ ind → ind P Pz Ps ↯ ¬allP
  where
    P : ℤ → Set
    P x = 0 ≤ x

    Pz : P 0
    Pz = ℤ.≤₀-intro {d = 0} ≃-derive

    Ps : ∀ {b} → P b → P (step b)
    Ps {b} (ℤ.≤₀-intro {d = n} 0+n≃b@(ℤ.≃₀-intro b⁺+0≃n+b⁻)) =
      let 0+sn≃sb =
            begin
              0 + (ℕ.step n as ℤ)
            ≃⟨⟩
              ℕ.step n — 0
            ≃⟨ AA.subst₂ ℕ.sn≃n+1 ⟩
              (n + 1) — 0
            ≃⟨ AA.compat₂ {a = n} ⟩
              (n — 0) + (1 — 0)
            ≃⟨ AA.subst₂ {b = 1 — 0} 0+n≃b ⟩
              b + 1
            ≃⟨⟩
              step b
            ∎
       in ℤ.≤₀-intro {d = ℕ.step n} 0+sn≃sb

    ¬allP : ¬ (∀ a → P a)
    ¬allP = ¬-intro λ 0≤a →
      let ℤ.≤₀-intro {n} (ℤ.≃₀-intro n+1≃0) = 0≤a -1
          sn≃0 = Eq.trans ℕ.sn≃n+1 n+1≃0
       in sn≃0 ↯ ℕ.step≄zero
