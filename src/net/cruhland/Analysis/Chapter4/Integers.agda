module net.cruhland.Analysis.Chapter4.Integers where

open import Agda.Builtin.FromNat using (Number)
import Agda.Builtin.Nat as Nat
open import Function using (const)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; refl; sym; trans; module ≡-Reasoning)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Logic using (⊤; ¬_; _↔_; ↔-intro)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)
open import net.cruhland.models.Setoid using (Setoid₀)

open ≡-Reasoning
open PeanoArithmetic peanoArithmetic using
  ( ℕ; <→<⁺; tri-<; tri-≡; tri->) renaming
  ( _+_ to _+ᴺ_; +-assoc to +ᴺ-assoc; +-cancelᴸ to +ᴺ-cancelᴸ
  ; +-cancelᴿ to +ᴺ-cancelᴿ; +-comm to +ᴺ-comm; +-zeroᴿ to +ᴺ-zeroᴿ
  ; +-positive to +ᴺ-positive; +-unchanged to +ᴺ-unchanged
  ; _*_ to _*ᴺ_; *-comm to *ᴺ-comm; *-distrib-+ᴿ to *ᴺ-distrib-+ᴺᴿ
  ; *-zeroᴿ to *ᴺ-zeroᴿ
  ; number to ℕ-number; Positive to Positiveᴺ; trichotomy to trichotomyᴺ
  )

{- 4.1 The integers -}

-- Definition 4.1.1 (Integers). An _integer_ is an expression of the
-- form a—b, where a and b are natural numbers. Two integers are
-- considered to be equal, a—b = c—d, if and only if a + d = c + b. We
-- let ℤ denote the set of all integers.
infix 9 _—_
data ℤ : Set where
  _—_ : ℕ → ℕ → ℤ

infix 4 _≃_
_≃_ : ℤ → ℤ → Set
a — b ≃ c — d = a +ᴺ d ≡ c +ᴺ b

infix 4 _≄_
_≄_ : ℤ → ℤ → Set
x ≄ y = ¬ (x ≃ y)

_ : ℤ
_ = 3 — 5

_ : 3 — 5 ≃ 2 — 4
_ = refl

_ : 3 — 5 ≄ 2 — 3
_ = λ ()

-- Exercise 4.1.1
≃-refl : ∀ {a} → a ≃ a
≃-refl {a⁺ — a⁻} = refl

≃-sym : ∀ {a b} → a ≃ b → b ≃ a
≃-sym {a⁺ — a⁻} {b⁺ — b⁻} = sym

a≡b+c≡d : ∀ {a b c d} → a ≡ b → c ≡ d → a +ᴺ c ≡ b +ᴺ d
a≡b+c≡d {b = b} {c = c} a≡b c≡d = trans (cong (_+ᴺ c) a≡b) (cong (b +ᴺ_) c≡d)

[ab][cd]≡a[[bc]d] : ∀ {a b c d} → (a +ᴺ b) +ᴺ (c +ᴺ d) ≡ a +ᴺ ((b +ᴺ c) +ᴺ d)
[ab][cd]≡a[[bc]d] {a} {b} {c} {d} =
  begin
    (a +ᴺ b) +ᴺ (c +ᴺ d)
  ≡⟨ +ᴺ-assoc {a} ⟩
    a +ᴺ (b +ᴺ (c +ᴺ d))
  ≡˘⟨ cong (a +ᴺ_) (+ᴺ-assoc {b}) ⟩
    a +ᴺ ((b +ᴺ c) +ᴺ d)
  ∎

swap-middle : ∀ {a b c d} → a +ᴺ ((b +ᴺ c) +ᴺ d) ≡ a +ᴺ ((c +ᴺ b) +ᴺ d)
swap-middle {a} {b} {c} {d} = cong (λ x → a +ᴺ (x +ᴺ d)) (+ᴺ-comm {b})

regroup : ∀ a b c d → (a +ᴺ b) +ᴺ (c +ᴺ d) ≡ a +ᴺ ((b +ᴺ d) +ᴺ c)
regroup a b c d =
  begin
    (a +ᴺ b) +ᴺ (c +ᴺ d)
  ≡⟨ cong ((a +ᴺ b) +ᴺ_) (+ᴺ-comm {c} {d}) ⟩
    (a +ᴺ b) +ᴺ (d +ᴺ c)
  ≡⟨ [ab][cd]≡a[[bc]d] {a} ⟩
    a +ᴺ ((b +ᴺ d) +ᴺ c)
  ∎

perm-adcb : ∀ {a b c d} → (a +ᴺ d) +ᴺ (c +ᴺ b) ≡ (a +ᴺ b) +ᴺ (c +ᴺ d)
perm-adcb {a} {b} {c} {d} =
  begin
    (a +ᴺ d) +ᴺ (c +ᴺ b)
  ≡⟨ regroup a d c b ⟩
    a +ᴺ ((d +ᴺ b) +ᴺ c)
  ≡⟨ swap-middle {a} {d} ⟩
    a +ᴺ ((b +ᴺ d) +ᴺ c)
  ≡˘⟨ regroup a b c d ⟩
    (a +ᴺ b) +ᴺ (c +ᴺ d)
  ∎

≃-trans : ∀ {a b c} → a ≃ b → b ≃ c → a ≃ c
≃-trans {a⁺ — a⁻} {b⁺ — b⁻} {c⁺ — c⁻} a⁺+b⁻≡b⁺+a⁻ b⁺+c⁻≡c⁺+b⁻ =
    +ᴺ-cancelᴿ [a⁺+c⁻]+[b⁺+b⁻]≡[c⁺+a⁻]+[b⁺+b⁻]
  where
    [a⁺+c⁻]+[b⁺+b⁻]≡[c⁺+a⁻]+[b⁺+b⁻] =
      begin
        (a⁺ +ᴺ c⁻) +ᴺ (b⁺ +ᴺ b⁻)
      ≡˘⟨ perm-adcb {a⁺} ⟩
        (a⁺ +ᴺ b⁻) +ᴺ (b⁺ +ᴺ c⁻)
      ≡⟨ a≡b+c≡d a⁺+b⁻≡b⁺+a⁻ b⁺+c⁻≡c⁺+b⁻ ⟩
        (b⁺ +ᴺ a⁻) +ᴺ (c⁺ +ᴺ b⁻)
      ≡⟨ perm-adcb {b⁺} ⟩
        (b⁺ +ᴺ b⁻) +ᴺ (c⁺ +ᴺ a⁻)
      ≡⟨ +ᴺ-comm {n = b⁺ +ᴺ b⁻} ⟩
        (c⁺ +ᴺ a⁻) +ᴺ (b⁺ +ᴺ b⁻)
      ∎

≃-IsEquivalence : IsEquivalence _≃_
≃-IsEquivalence = record { refl = ≃-refl ; sym = ≃-sym ; trans = ≃-trans }

ℤ-Setoid : Setoid₀
ℤ-Setoid = record { Carrier = ℤ ; _≈_ = _≃_ ; isEquivalence = ≃-IsEquivalence }

-- Definition 4.1.2. The sum of two integers, (a—b) + (c—d), is
-- defined by the formula (a—b) + (c—d) ≔ (a + c)—(b + d).
infixl 6 _+_
_+_ : ℤ → ℤ → ℤ
a⁺ — a⁻ + b⁺ — b⁻ = (a⁺ +ᴺ b⁺) — (a⁻ +ᴺ b⁻)

-- The product of two integers, (a—b) × (c—d), is defined by
-- (a—b) × (c—d) ≔ (ac + bd)—(ad + bc).
infixl 7 _*_
_*_ : ℤ → ℤ → ℤ
a⁺ — a⁻ * b⁺ — b⁻ = (a⁺ *ᴺ b⁺ +ᴺ a⁻ *ᴺ b⁻) — (a⁺ *ᴺ b⁻ +ᴺ a⁻ *ᴺ b⁺)

-- Thus for instance, (3—5) + (1—4) is equal to (4—9).
_ : 3 — 5 + 1 — 4 ≃ 4 — 9
_ = refl

-- There is however one thing we have to check before we can accept
-- these definitions - we have to check that if we replace one of the
-- integers by an equal integer, that the sum or product does not
-- change. For instance (3—5) is equal to (2—4), so (3—5) + (1—4)
-- ought to have the same value as (2—4) + (1—4), otherwise this would
-- not give a consistent definition of addition.
_ : 3 — 5 + 1 — 4 ≃ 2 — 4 + 1 — 4
_ = refl

-- Lemma 4.1.3 (Addition and multiplication are well-defined).
+-substᴸ : ∀ {a₁ a₂ b} → a₁ ≃ a₂ → a₁ + b ≃ a₂ + b
+-substᴸ {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} {b⁺ — b⁻} a₁⁺+a₂⁻≡a₂⁺+a₁⁻ =
  begin
    (a₁⁺ +ᴺ b⁺) +ᴺ (a₂⁻ +ᴺ b⁻)
  ≡⟨ rearr {a₁⁺} ⟩
    (a₁⁺ +ᴺ a₂⁻) +ᴺ (b⁺ +ᴺ b⁻)
  ≡⟨ cong (_+ᴺ (b⁺ +ᴺ b⁻)) a₁⁺+a₂⁻≡a₂⁺+a₁⁻ ⟩
    (a₂⁺ +ᴺ a₁⁻) +ᴺ (b⁺ +ᴺ b⁻)
  ≡⟨ rearr {a₂⁺} ⟩
    (a₂⁺ +ᴺ b⁺) +ᴺ (a₁⁻ +ᴺ b⁻)
  ∎
  where
    rearr : ∀ {w x y z} → (w +ᴺ x) +ᴺ (y +ᴺ z) ≡ (w +ᴺ y) +ᴺ (x +ᴺ z)
    rearr {w} {x} {y} {z} =
      begin
        (w +ᴺ x) +ᴺ (y +ᴺ z)
      ≡⟨ [ab][cd]≡a[[bc]d] {w} ⟩
        w +ᴺ ((x +ᴺ y) +ᴺ z)
      ≡⟨ swap-middle {w} {x} ⟩
        w +ᴺ ((y +ᴺ x) +ᴺ z)
      ≡˘⟨ [ab][cd]≡a[[bc]d] {w} ⟩
        (w +ᴺ y) +ᴺ (x +ᴺ z)
      ∎

+-comm : ∀ {a b} → a + b ≃ b + a
+-comm {a⁺ — a⁻} {b⁺ — b⁻} =
  begin
    (a⁺ +ᴺ b⁺) +ᴺ (b⁻ +ᴺ a⁻)
  ≡⟨ cong (_+ᴺ (b⁻ +ᴺ a⁻)) (+ᴺ-comm {a⁺}) ⟩
    (b⁺ +ᴺ a⁺) +ᴺ (b⁻ +ᴺ a⁻)
  ≡⟨ cong ((b⁺ +ᴺ a⁺) +ᴺ_) (+ᴺ-comm {b⁻}) ⟩
    (b⁺ +ᴺ a⁺) +ᴺ (a⁻ +ᴺ b⁻)
  ∎

+-substᴿ : ∀ {a b₁ b₂} → b₁ ≃ b₂ → a + b₁ ≃ a + b₂
+-substᴿ b₁≃b₂ = ≃-trans (≃-trans +-comm (+-substᴸ b₁≃b₂)) +-comm

*-substᴸ : ∀ {a₁ a₂ b} → a₁ ≃ a₂ → a₁ * b ≃ a₂ * b
*-substᴸ {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} {b⁺ — b⁻} a₁⁺a₂⁻≡a₂⁺a₁⁻ =
  begin
    (a₁⁺ *ᴺ b⁺ +ᴺ a₁⁻ *ᴺ b⁻) +ᴺ (a₂⁺ *ᴺ b⁻ +ᴺ a₂⁻ *ᴺ b⁺)
  ≡⟨ rearr {w = a₁⁺} {y = a₂⁺} ⟩
    (a₁⁺ +ᴺ a₂⁻) *ᴺ b⁺ +ᴺ (a₂⁺ +ᴺ a₁⁻) *ᴺ b⁻
  ≡⟨ cong (λ k → k *ᴺ b⁺ +ᴺ (a₂⁺ +ᴺ a₁⁻) *ᴺ b⁻) a₁⁺a₂⁻≡a₂⁺a₁⁻ ⟩
    (a₂⁺ +ᴺ a₁⁻) *ᴺ b⁺ +ᴺ (a₂⁺ +ᴺ a₁⁻) *ᴺ b⁻
  ≡˘⟨ cong (λ k → (a₂⁺ +ᴺ a₁⁻) *ᴺ b⁺ +ᴺ k *ᴺ b⁻) a₁⁺a₂⁻≡a₂⁺a₁⁻ ⟩
    (a₂⁺ +ᴺ a₁⁻) *ᴺ b⁺ +ᴺ (a₁⁺ +ᴺ a₂⁻) *ᴺ b⁻
  ≡˘⟨ rearr {w = a₂⁺} {y = a₁⁺} ⟩
    (a₂⁺ *ᴺ b⁺ +ᴺ a₂⁻ *ᴺ b⁻) +ᴺ (a₁⁺ *ᴺ b⁻ +ᴺ a₁⁻ *ᴺ b⁺)
  ∎
  where
    rearr :
      ∀ {u v w x y z} →
        (w *ᴺ u +ᴺ x *ᴺ v) +ᴺ (y *ᴺ v +ᴺ z *ᴺ u) ≡
          (w +ᴺ z) *ᴺ u +ᴺ (y +ᴺ x) *ᴺ v
    rearr {u} {v} {w} {x} {y} {z} =
      begin
        (w *ᴺ u +ᴺ x *ᴺ v) +ᴺ (y *ᴺ v +ᴺ z *ᴺ u)
      ≡⟨ perm-adcb {w *ᴺ u} ⟩
        (w *ᴺ u +ᴺ z *ᴺ u) +ᴺ (y *ᴺ v +ᴺ x *ᴺ v)
      ≡˘⟨ cong (_+ᴺ (y *ᴺ v +ᴺ x *ᴺ v)) (*ᴺ-distrib-+ᴺᴿ {w}) ⟩
        (w +ᴺ z) *ᴺ u +ᴺ (y *ᴺ v +ᴺ x *ᴺ v)
      ≡˘⟨ cong ((w +ᴺ z) *ᴺ u +ᴺ_) (*ᴺ-distrib-+ᴺᴿ {y}) ⟩
        (w +ᴺ z) *ᴺ u +ᴺ (y +ᴺ x) *ᴺ v
      ∎

*-comm : ∀ {a b} → a * b ≃ b * a
*-comm {a⁺ — a⁻} {b⁺ — b⁻} =
  begin
    (a⁺ *ᴺ b⁺ +ᴺ a⁻ *ᴺ b⁻) +ᴺ (b⁺ *ᴺ a⁻ +ᴺ b⁻ *ᴺ a⁺)
  ≡⟨ cong (λ x → (x +ᴺ a⁻ *ᴺ b⁻) +ᴺ (b⁺ *ᴺ a⁻ +ᴺ b⁻ *ᴺ a⁺)) (*ᴺ-comm {a⁺}) ⟩
    (b⁺ *ᴺ a⁺ +ᴺ a⁻ *ᴺ b⁻) +ᴺ (b⁺ *ᴺ a⁻ +ᴺ b⁻ *ᴺ a⁺)
  ≡⟨ cong (λ x → (b⁺ *ᴺ a⁺ +ᴺ x) +ᴺ (b⁺ *ᴺ a⁻ +ᴺ b⁻ *ᴺ a⁺)) (*ᴺ-comm {a⁻}) ⟩
    (b⁺ *ᴺ a⁺ +ᴺ b⁻ *ᴺ a⁻) +ᴺ (b⁺ *ᴺ a⁻ +ᴺ b⁻ *ᴺ a⁺)
  ≡⟨ cong ((b⁺ *ᴺ a⁺ +ᴺ b⁻ *ᴺ a⁻) +ᴺ_) (+ᴺ-comm {b⁺ *ᴺ a⁻}) ⟩
    (b⁺ *ᴺ a⁺ +ᴺ b⁻ *ᴺ a⁻) +ᴺ (b⁻ *ᴺ a⁺ +ᴺ b⁺ *ᴺ a⁻)
  ≡⟨ cong (λ x → (b⁺ *ᴺ a⁺ +ᴺ b⁻ *ᴺ a⁻) +ᴺ (x +ᴺ b⁺ *ᴺ a⁻)) (*ᴺ-comm {b⁻}) ⟩
    (b⁺ *ᴺ a⁺ +ᴺ b⁻ *ᴺ a⁻) +ᴺ (a⁺ *ᴺ b⁻ +ᴺ b⁺ *ᴺ a⁻)
  ≡⟨ cong (λ x → (b⁺ *ᴺ a⁺ +ᴺ b⁻ *ᴺ a⁻) +ᴺ (a⁺ *ᴺ b⁻ +ᴺ x)) (*ᴺ-comm {b⁺}) ⟩
    (b⁺ *ᴺ a⁺ +ᴺ b⁻ *ᴺ a⁻) +ᴺ (a⁺ *ᴺ b⁻ +ᴺ a⁻ *ᴺ b⁺)
  ∎

*-substᴿ : ∀ {a b₁ b₂} → b₁ ≃ b₂ → a * b₁ ≃ a * b₂
*-substᴿ b₁≃b₂ = ≃-trans (≃-trans *-comm (*-substᴸ b₁≃b₂)) *-comm

-- The integers n—0 behave in the same way as the natural numbers n;
-- indeed one can check that (n—0) + (m—0) = (n + m)—0 and
-- (n—0) × (m—0) = nm—0.
_ : ∀ {n m} → n — 0 + m — 0 ≃ (n +ᴺ m) — 0
_ = refl

*-compat-*ᴺ : ∀ {n m} → n — 0 * m — 0 ≃ (n *ᴺ m) — 0
*-compat-*ᴺ {n} {m} =
  begin
    n *ᴺ m +ᴺ 0 +ᴺ 0
  ≡⟨ +ᴺ-assoc {n *ᴺ m} ⟩
    n *ᴺ m +ᴺ (0 +ᴺ 0)
  ≡˘⟨ cong (λ x → n *ᴺ m +ᴺ (x +ᴺ 0)) (*ᴺ-zeroᴿ {n}) ⟩
    n *ᴺ m +ᴺ (n *ᴺ 0 +ᴺ 0)
  ∎

-- Furthermore, (n—0) is equal to (m—0) if and only if n = m.
_ : ∀ {n m} → n — 0 ≃ m — 0 ↔ n ≡ m
_ = ↔-intro +ᴺ-cancelᴿ (cong (_+ᴺ 0))

-- Thus we may _identify_ the natural numbers with integers by setting
-- n ≡ n—0; this does not affect our definitions of addition or
-- multiplication or equality since they are consistent with each
-- other.
-- [note] We can't make this identification in type theory because
-- both propositional equality and setoid equality require that their
-- associated values belong to the same type. However, we can use the
-- Number typeclass to interpret numeric literals as elements of
-- ℤ. And we can define a function to convert natural numbers to their
-- integer equivalent.
fromNat : Nat.Nat → {{_ : ⊤}} → ℤ
fromNat Nat.zero = 0 — 0
fromNat (Nat.suc n) = 1 — 0 + fromNat n

instance
  ℤ-number : Number ℤ
  ℤ-number = record { Constraint = const ⊤ ; fromNat = fromNat }

-- For instance the natural number 3 is now considered to be the same
-- as the integer 3—0, thus 3 = 3—0.
_ : 3 ≃ 3 — 0
_ = refl

-- In particular 0 is equal to 0—0 and 1 is equal to 1—0.
_ : 0 ≃ 0 — 0
_ = refl

_ : 1 ≃ 1 — 0
_ = refl

-- Of course, if we set n equal to n—0, then it will also be equal to
-- any other integer which is equal to n—0, for instance 3 is equal
-- not only to 3—0, but also to 4—1, 5—2, etc.
_ : 3 ≃ 4 — 1
_ = refl

_ : 3 ≃ 5 — 2
_ = refl

-- We can now define incrementation on the integers by defining
-- step x ≔ x + 1 for any integer x; this is of course consistent with
-- our definition of the increment operation for natural
-- numbers. However, this is no longer an important operation for us,
-- as it has been now superceded by the more general notion of
-- addition.
step : ℤ → ℤ
step x = x + 1

-- Definition 4.1.4 (Negation of integers). If (a—b) is an integer, we
-- define the negation -(a—b) to be the integer (b—a).
infix 8 -_
-_ : ℤ → ℤ
- a — b = b — a

-- In particular if n = n—0 is a positive natural number, we can
-- define its negation -n = 0—n.
-- [note] Here we must use a conversion function since n is not a
-- literal.
fromℕ : ℕ → ℤ
fromℕ n = n — 0

_ : ∀ {n} → - (fromℕ n) ≃ 0 — n
_ = refl

-- For instance -(3—5) = (5—3).
_ : -(3 — 5) ≃ 5 — 3
_ = refl

-- One can check this definition is well-defined.
-- Exercise 4.1.2
neg-subst : ∀ {a₁ a₂} → a₁ ≃ a₂ → - a₁ ≃ - a₂
neg-subst {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} a₁⁺+a₂⁻≡a₂⁺+a₁⁻ =
  begin
    a₁⁻ +ᴺ a₂⁺
  ≡⟨ +ᴺ-comm {a₁⁻} ⟩
    a₂⁺ +ᴺ a₁⁻
  ≡˘⟨ a₁⁺+a₂⁻≡a₂⁺+a₁⁻ ⟩
    a₁⁺ +ᴺ a₂⁻
  ≡⟨ +ᴺ-comm {a₁⁺} ⟩
    a₂⁻ +ᴺ a₁⁺
  ∎

-- Lemma 4.1.5 (Trichotomy of integers). Let x be an integer. Then
-- exactly one of the following three statements is true: (a) x is
-- zero; (b) x is equal to a positive natural number n; or (c) x is
-- the negation -n of a positive natural number n.
record IsPositive (x : ℤ) : Set where
  field
    n : ℕ
    pos : Positiveᴺ n
    eq : x ≃ fromℕ n

record IsNegative (x : ℤ) : Set where
  field
    n : ℕ
    pos : Positiveᴺ n
    eq : x ≃ - fromℕ n

data AtLeastOne (x : ℤ) : Set where
  nil : x ≃ 0 → AtLeastOne x
  pos : IsPositive x → AtLeastOne x
  neg : IsNegative x → AtLeastOne x

data MoreThanOne (x : ℤ) : Set where
  nil∧pos : x ≃ 0 → IsPositive x → MoreThanOne x
  nil∧neg : x ≃ 0 → IsNegative x → MoreThanOne x
  pos∧neg : IsPositive x → IsNegative x → MoreThanOne x

record Trichotomy (x : ℤ) : Set where
  field
    at-least : AtLeastOne x
    at-most : ¬ MoreThanOne x

trichotomy : ∀ {x} → Trichotomy x
trichotomy {x⁺ — x⁻} = record { at-least = at-least ; at-most = at-most }
  where
    at-least : AtLeastOne (x⁺ — x⁻)
    at-least with trichotomyᴺ {x⁺} {x⁻}
    at-least | tri-< x⁺<x⁻ =
      let record { d = n ; d≢z = pos-n ; n+d≡m = x⁺+n≡x⁻ } = <→<⁺ x⁺<x⁻
       in neg (record { n = n ; pos = pos-n ; eq = x⁺+n≡x⁻ })
    at-least | tri-≡ x⁺≡x⁻ = nil (trans +ᴺ-zeroᴿ x⁺≡x⁻)
    at-least | tri-> x⁺>x⁻ =
      let record { d = n ; d≢z = pos-n ; n+d≡m = x⁻+n≡x⁺ } = <→<⁺ x⁺>x⁻
          x⁺—x⁻≃n =
            begin
              x⁺ +ᴺ 0
            ≡⟨ +ᴺ-zeroᴿ ⟩
              x⁺
            ≡˘⟨ x⁻+n≡x⁺ ⟩
              x⁻ +ᴺ n
            ≡⟨ +ᴺ-comm {x⁻} ⟩
              n +ᴺ x⁻
            ∎
       in pos (record { n = n ; pos = pos-n ; eq = x⁺—x⁻≃n })

    at-most : ¬ MoreThanOne (x⁺ — x⁻)
    at-most (nil∧pos x⁺+0≡x⁻ record { n = n ; pos = n≢0 ; eq = x⁺+0≡n+x⁻ }) =
      let x⁻+n≡x⁻ = trans (+ᴺ-comm {x⁻}) (trans (sym x⁺+0≡n+x⁻) x⁺+0≡x⁻)
       in n≢0 (+ᴺ-unchanged x⁻+n≡x⁻)
    at-most (nil∧neg x⁺+0≡x⁻ record { n = n ; pos = n≢0 ; eq = x⁺+n≡x⁻ }) =
      n≢0 (+ᴺ-cancelᴸ (trans x⁺+n≡x⁻ (sym x⁺+0≡x⁻)))
    at-most (pos∧neg record { n = n₁ ; pos = n₁≢0 ; eq = x⁺+0≡n₁+x⁻ }
                     record { n = n₂ ; pos = n₂≢0 ; eq = x⁺+n₂≡x⁻ }) =
      let x⁺+[n₂+n₁]≡x⁺+0 =
            begin
              x⁺ +ᴺ (n₂ +ᴺ n₁)
            ≡˘⟨ +ᴺ-assoc {x⁺} ⟩
              (x⁺ +ᴺ n₂) +ᴺ n₁
            ≡⟨ cong (_+ᴺ n₁) x⁺+n₂≡x⁻ ⟩
              x⁻ +ᴺ n₁
            ≡⟨ +ᴺ-comm {x⁻} ⟩
              n₁ +ᴺ x⁻
            ≡˘⟨ x⁺+0≡n₁+x⁻ ⟩
              x⁺ +ᴺ 0
            ∎
       in +ᴺ-positive n₂≢0 (+ᴺ-cancelᴸ x⁺+[n₂+n₁]≡x⁺+0)
