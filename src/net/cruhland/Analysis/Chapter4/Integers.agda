module net.cruhland.Analysis.Chapter4.Integers where

open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; refl; sym; trans; module ≡-Reasoning)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Logic using (¬_)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)
open import net.cruhland.models.Setoid using (Setoid₀)

open ≡-Reasoning
open PeanoArithmetic peanoArithmetic using (ℕ) renaming
  ( _+_ to _+ᴺ_; +-assoc to +ᴺ-assoc; +-cancelᴿ to +ᴺ-cancelᴿ; +-comm to +ᴺ-comm
  ; _*_ to _*ᴺ_
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

perm-adcb : ∀ a b c d → (a +ᴺ d) +ᴺ (c +ᴺ b) ≡ (a +ᴺ b) +ᴺ (c +ᴺ d)
perm-adcb a b c d =
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
      ≡˘⟨ perm-adcb a⁺ c⁻ b⁺ b⁻ ⟩
        (a⁺ +ᴺ b⁻) +ᴺ (b⁺ +ᴺ c⁻)
      ≡⟨ a≡b+c≡d a⁺+b⁻≡b⁺+a⁻ b⁺+c⁻≡c⁺+b⁻ ⟩
        (b⁺ +ᴺ a⁻) +ᴺ (c⁺ +ᴺ b⁻)
      ≡⟨ perm-adcb b⁺ b⁻ c⁺ a⁻ ⟩
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
