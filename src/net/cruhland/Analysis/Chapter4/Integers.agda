module net.cruhland.Analysis.Chapter4.Integers where

open import Agda.Builtin.FromNat using (Number)
import Agda.Builtin.Nat as Nat
open import Function using (const)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; refl; sym; trans; module ≡-Reasoning)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Logic using
  (⊤; _∨_; ∨-introᴸ; ∨-introᴿ; ¬_; _↔_; ↔-intro)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)
open import net.cruhland.models.Setoid using (Setoid₀)

open ≡-Reasoning
open PeanoArithmetic peanoArithmetic using
  ( ℕ; <→<⁺; tri-<; tri-≡; tri->) renaming
  ( _+_ to _+ᴺ_; +-assoc to +ᴺ-assoc; +-cancelᴸ to +ᴺ-cancelᴸ
  ; +-cancelᴿ to +ᴺ-cancelᴿ; +-comm to +ᴺ-comm; +-zeroᴿ to +ᴺ-identityᴿ
  ; +-positive to +ᴺ-positive; +-unchanged to +ᴺ-unchanged
  ; _*_ to _*ᴺ_; *-assoc to *ᴺ-assoc; *-cancelᴸ to *ᴺ-cancelᴸ; *-comm to *ᴺ-comm
  ; *-distrib-+ᴸ to *ᴺ-distrib-+ᴺᴸ; *-distrib-+ᴿ to *ᴺ-distrib-+ᴺᴿ
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
transpose : ∀ {w x y z} → (w +ᴺ x) +ᴺ (y +ᴺ z) ≡ (w +ᴺ y) +ᴺ (x +ᴺ z)
transpose {w} {x} {y} {z} =
  begin
    (w +ᴺ x) +ᴺ (y +ᴺ z)
  ≡⟨ [ab][cd]≡a[[bc]d] {w} ⟩
    w +ᴺ ((x +ᴺ y) +ᴺ z)
  ≡⟨ swap-middle {w} {x} ⟩
    w +ᴺ ((y +ᴺ x) +ᴺ z)
  ≡˘⟨ [ab][cd]≡a[[bc]d] {w} ⟩
    (w +ᴺ y) +ᴺ (x +ᴺ z)
  ∎

+-substᴸ : ∀ {a₁ a₂ b} → a₁ ≃ a₂ → a₁ + b ≃ a₂ + b
+-substᴸ {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} {b⁺ — b⁻} a₁⁺+a₂⁻≡a₂⁺+a₁⁻ =
  begin
    (a₁⁺ +ᴺ b⁺) +ᴺ (a₂⁻ +ᴺ b⁻)
  ≡⟨ transpose {a₁⁺} ⟩
    (a₁⁺ +ᴺ a₂⁻) +ᴺ (b⁺ +ᴺ b⁻)
  ≡⟨ cong (_+ᴺ (b⁺ +ᴺ b⁻)) a₁⁺+a₂⁻≡a₂⁺+a₁⁻ ⟩
    (a₂⁺ +ᴺ a₁⁻) +ᴺ (b⁺ +ᴺ b⁻)
  ≡⟨ transpose {a₂⁺} ⟩
    (a₂⁺ +ᴺ b⁺) +ᴺ (a₁⁻ +ᴺ b⁻)
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

distrib-twoᴸ :
  ∀ {a b c d e f} →
    a *ᴺ (b +ᴺ c) +ᴺ d *ᴺ (e +ᴺ f) ≡
      (a *ᴺ b +ᴺ a *ᴺ c) +ᴺ (d *ᴺ e +ᴺ d *ᴺ f)
distrib-twoᴸ {a} {b} {c} {d} {e} {f} =
  begin
    a *ᴺ (b +ᴺ c) +ᴺ d *ᴺ (e +ᴺ f)
  ≡⟨ cong (_+ᴺ d *ᴺ (e +ᴺ f)) (*ᴺ-distrib-+ᴺᴸ {a}) ⟩
    (a *ᴺ b +ᴺ a *ᴺ c) +ᴺ d *ᴺ (e +ᴺ f)
  ≡⟨ cong ((a *ᴺ b +ᴺ a *ᴺ c) +ᴺ_) (*ᴺ-distrib-+ᴺᴸ {d}) ⟩
    (a *ᴺ b +ᴺ a *ᴺ c) +ᴺ (d *ᴺ e +ᴺ d *ᴺ f)
  ∎

distrib-twoᴿ :
  ∀ {a b c d e f} →
    (a +ᴺ b) *ᴺ c +ᴺ (d +ᴺ e) *ᴺ f ≡
      (a *ᴺ c +ᴺ b *ᴺ c) +ᴺ (d *ᴺ f +ᴺ e *ᴺ f)
distrib-twoᴿ {a} {b} {c} {d} {e} {f} =
  begin
    (a +ᴺ b) *ᴺ c +ᴺ (d +ᴺ e) *ᴺ f
  ≡⟨ cong (_+ᴺ (d +ᴺ e) *ᴺ f) (*ᴺ-distrib-+ᴺᴿ {a}) ⟩
    (a *ᴺ c +ᴺ b *ᴺ c) +ᴺ (d +ᴺ e) *ᴺ f
  ≡⟨ cong ((a *ᴺ c +ᴺ b *ᴺ c) +ᴺ_) (*ᴺ-distrib-+ᴺᴿ {d}) ⟩
    (a *ᴺ c +ᴺ b *ᴺ c) +ᴺ (d *ᴺ f +ᴺ e *ᴺ f)
  ∎

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
      ≡˘⟨ distrib-twoᴿ {a = w} {d = y} ⟩
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

open Trichotomy

trichotomy : ∀ {x} → Trichotomy x
trichotomy {x⁺ — x⁻} = record { at-least = one≤ ; at-most = one≮ }
  where
    one≤ : AtLeastOne (x⁺ — x⁻)
    one≤ with trichotomyᴺ {x⁺} {x⁻}
    one≤ | tri-< x⁺<x⁻ =
      let record { d = n ; d≢z = pos-n ; n+d≡m = x⁺+n≡x⁻ } = <→<⁺ x⁺<x⁻
       in neg (record { n = n ; pos = pos-n ; eq = x⁺+n≡x⁻ })
    one≤ | tri-≡ x⁺≡x⁻ = nil (trans +ᴺ-identityᴿ x⁺≡x⁻)
    one≤ | tri-> x⁺>x⁻ =
      let record { d = n ; d≢z = pos-n ; n+d≡m = x⁻+n≡x⁺ } = <→<⁺ x⁺>x⁻
          x⁺—x⁻≃n =
            begin
              x⁺ +ᴺ 0
            ≡⟨ +ᴺ-identityᴿ ⟩
              x⁺
            ≡˘⟨ x⁻+n≡x⁺ ⟩
              x⁻ +ᴺ n
            ≡⟨ +ᴺ-comm {x⁻} ⟩
              n +ᴺ x⁻
            ∎
       in pos (record { n = n ; pos = pos-n ; eq = x⁺—x⁻≃n })

    one≮ : ¬ MoreThanOne (x⁺ — x⁻)
    one≮ (nil∧pos x⁺+0≡x⁻ record { n = n ; pos = n≢0 ; eq = x⁺+0≡n+x⁻ }) =
      let x⁻+n≡x⁻ = trans (+ᴺ-comm {x⁻}) (trans (sym x⁺+0≡n+x⁻) x⁺+0≡x⁻)
       in n≢0 (+ᴺ-unchanged x⁻+n≡x⁻)
    one≮ (nil∧neg x⁺+0≡x⁻ record { n = n ; pos = n≢0 ; eq = x⁺+n≡x⁻ }) =
      n≢0 (+ᴺ-cancelᴸ (trans x⁺+n≡x⁻ (sym x⁺+0≡x⁻)))
    one≮ (pos∧neg record { n = n₁ ; pos = n₁≢0 ; eq = x⁺+0≡n₁+x⁻ }
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

-- Proposition 4.1.6 (Laws of algebra for integers).
-- Exercise 4.1.4
_ : ∀ {x y} → x + y ≃ y + x
_ = +-comm

+-assoc : ∀ {x y z} → (x + y) + z ≃ x + (y + z)
+-assoc {x⁺ — x⁻} {y⁺ — y⁻} {z⁺ — z⁻} =
  begin
    ((x⁺ +ᴺ y⁺) +ᴺ z⁺) +ᴺ (x⁻ +ᴺ (y⁻ +ᴺ z⁻))
  ≡⟨ cong (_+ᴺ (x⁻ +ᴺ (y⁻ +ᴺ z⁻))) (+ᴺ-assoc {x⁺}) ⟩
    (x⁺ +ᴺ (y⁺ +ᴺ z⁺)) +ᴺ (x⁻ +ᴺ (y⁻ +ᴺ z⁻))
  ≡˘⟨ cong ((x⁺ +ᴺ (y⁺ +ᴺ z⁺)) +ᴺ_) (+ᴺ-assoc {x⁻}) ⟩
    (x⁺ +ᴺ (y⁺ +ᴺ z⁺)) +ᴺ ((x⁻ +ᴺ y⁻) +ᴺ z⁻)
  ∎

+-identityᴸ : ∀ {x} → 0 + x ≃ x
+-identityᴸ {x⁺ — x⁻} = refl

+-identityᴿ : ∀ {x} → x + 0 ≃ x
+-identityᴿ = ≃-trans +-comm +-identityᴸ

+-inverseᴸ : ∀ {x} → - x + x ≃ 0
+-inverseᴸ {x⁺ — x⁻} =
  begin
    (x⁻ +ᴺ x⁺) +ᴺ 0
  ≡⟨ +ᴺ-identityᴿ ⟩
    x⁻ +ᴺ x⁺
  ≡⟨ +ᴺ-comm {x⁻} ⟩
    x⁺ +ᴺ x⁻
  ∎

+-inverseᴿ : ∀ {x} → x + - x ≃ 0
+-inverseᴿ = ≃-trans +-comm +-inverseᴸ

_ : ∀ {x y} → x * y ≃ y * x
_ = *-comm

*-assoc : ∀ {x y z} → (x * y) * z ≃ x * (y * z)
*-assoc {x⁺ — x⁻} {y⁺ — y⁻} {z⁺ — z⁻} =
    a≡b+c≡d (refactor {z⁺} {z⁻} {x⁺} {x⁻}) (sym (refactor {z⁻} {z⁺} {x⁺} {x⁻}))
  where
    assoc-four :
      ∀ {a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃} →
        ((a₁ *ᴺ a₂) *ᴺ a₃ +ᴺ (b₁ *ᴺ b₂) *ᴺ b₃) +ᴺ
        ((c₁ *ᴺ c₂) *ᴺ c₃ +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃) ≡
        (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃)) +ᴺ
        (c₁ *ᴺ (c₂ *ᴺ c₃) +ᴺ d₁ *ᴺ (d₂ *ᴺ d₃))
    assoc-four {a₁} {a₂} {a₃} {b₁} {b₂} {b₃} {c₁} {c₂} {c₃} {d₁} {d₂} {d₃} =
      begin
        ((a₁ *ᴺ a₂) *ᴺ a₃ +ᴺ (b₁ *ᴺ b₂) *ᴺ b₃) +ᴺ
        ((c₁ *ᴺ c₂) *ᴺ c₃ +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃)
      ≡⟨ cong
           (λ x → (x +ᴺ (b₁ *ᴺ b₂) *ᴺ b₃) +ᴺ
                  ((c₁ *ᴺ c₂) *ᴺ c₃ +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃))
           (*ᴺ-assoc {a₁}) ⟩
        (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ (b₁ *ᴺ b₂) *ᴺ b₃) +ᴺ
        ((c₁ *ᴺ c₂) *ᴺ c₃ +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃)
      ≡⟨ cong
           (λ x → (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ x) +ᴺ
                  ((c₁ *ᴺ c₂) *ᴺ c₃ +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃))
           (*ᴺ-assoc {b₁}) ⟩
        (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃)) +ᴺ
        ((c₁ *ᴺ c₂) *ᴺ c₃ +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃)
      ≡⟨ cong
           (λ x → (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃)) +ᴺ
                  (x +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃))
           (*ᴺ-assoc {c₁}) ⟩
        (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃)) +ᴺ
        (c₁ *ᴺ (c₂ *ᴺ c₃) +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃)
      ≡⟨ cong
            (λ x → (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃)) +ᴺ
                   (c₁ *ᴺ (c₂ *ᴺ c₃) +ᴺ x))
            (*ᴺ-assoc {d₁}) ⟩
        (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃)) +ᴺ
        (c₁ *ᴺ (c₂ *ᴺ c₃) +ᴺ d₁ *ᴺ (d₂ *ᴺ d₃))
      ∎

    refactor :
      ∀ {b₁ b₂ a₁ a₂ a₃ a₄} →
        (a₁ *ᴺ a₃ +ᴺ a₂ *ᴺ a₄) *ᴺ b₁ +ᴺ (a₁ *ᴺ a₄ +ᴺ a₂ *ᴺ a₃) *ᴺ b₂ ≡
          a₁ *ᴺ (a₃ *ᴺ b₁ +ᴺ a₄ *ᴺ b₂) +ᴺ a₂ *ᴺ (a₃ *ᴺ b₂ +ᴺ a₄ *ᴺ b₁)
    refactor {b₁} {b₂} {a₁} {a₂} {a₃} {a₄} =
      begin
        (a₁ *ᴺ a₃ +ᴺ a₂ *ᴺ a₄) *ᴺ b₁ +ᴺ (a₁ *ᴺ a₄ +ᴺ a₂ *ᴺ a₃) *ᴺ b₂
      ≡⟨ distrib-twoᴿ {a = a₁ *ᴺ a₃} {d = a₁ *ᴺ a₄} ⟩
        ((a₁ *ᴺ a₃) *ᴺ b₁ +ᴺ (a₂ *ᴺ a₄) *ᴺ b₁) +ᴺ
        ((a₁ *ᴺ a₄) *ᴺ b₂ +ᴺ (a₂ *ᴺ a₃) *ᴺ b₂)
      ≡⟨ transpose {(a₁ *ᴺ a₃) *ᴺ b₁}⟩
        ((a₁ *ᴺ a₃) *ᴺ b₁ +ᴺ (a₁ *ᴺ a₄) *ᴺ b₂) +ᴺ
        ((a₂ *ᴺ a₄) *ᴺ b₁ +ᴺ (a₂ *ᴺ a₃) *ᴺ b₂)
      ≡⟨ cong (((a₁ *ᴺ a₃) *ᴺ b₁ +ᴺ (a₁ *ᴺ a₄) *ᴺ b₂) +ᴺ_)
              (+ᴺ-comm {(a₂ *ᴺ a₄) *ᴺ b₁}) ⟩
        ((a₁ *ᴺ a₃) *ᴺ b₁ +ᴺ (a₁ *ᴺ a₄) *ᴺ b₂) +ᴺ
        ((a₂ *ᴺ a₃) *ᴺ b₂ +ᴺ (a₂ *ᴺ a₄) *ᴺ b₁)
      ≡⟨ assoc-four {a₁ = a₁} {b₁ = a₁} {c₁ = a₂} {d₁ = a₂} ⟩
        (a₁ *ᴺ (a₃ *ᴺ b₁) +ᴺ a₁ *ᴺ (a₄ *ᴺ b₂)) +ᴺ
        (a₂ *ᴺ (a₃ *ᴺ b₂) +ᴺ a₂ *ᴺ (a₄ *ᴺ b₁))
      ≡˘⟨ distrib-twoᴸ {a = a₁} {d = a₂} ⟩
        a₁ *ᴺ (a₃ *ᴺ b₁ +ᴺ a₄ *ᴺ b₂) +ᴺ a₂ *ᴺ (a₃ *ᴺ b₂ +ᴺ a₄ *ᴺ b₁)
      ∎

*-identityᴸ : ∀ {x} → 1 * x ≃ x
*-identityᴸ {x⁺ — x⁻} =
  begin
    ((x⁺ +ᴺ 0) +ᴺ 0) +ᴺ x⁻
  ≡⟨ +ᴺ-assoc {x⁺ +ᴺ 0} ⟩
    (x⁺ +ᴺ 0) +ᴺ (0 +ᴺ x⁻)
  ≡⟨ cong ((x⁺ +ᴺ 0) +ᴺ_) (+ᴺ-comm {0}) ⟩
    (x⁺ +ᴺ 0) +ᴺ (x⁻ +ᴺ 0)
  ≡⟨ +ᴺ-assoc {x⁺} ⟩
    x⁺ +ᴺ (0 +ᴺ (x⁻ +ᴺ 0))
  ≡⟨ cong (x⁺ +ᴺ_) (+ᴺ-comm {0}) ⟩
    x⁺ +ᴺ ((x⁻ +ᴺ 0) +ᴺ 0)
  ∎

*-identityᴿ : ∀ {x} → x * 1 ≃ x
*-identityᴿ = ≃-trans *-comm *-identityᴸ

*-distrib-+ᴸ : ∀ {x y z} → x * (y + z) ≃ x * y + x * z
*-distrib-+ᴸ {x⁺ — x⁻} {y⁺ — y⁻} {z⁺ — z⁻} =
    a≡b+c≡d (refactor {x⁺} {x⁻}) (sym (refactor {x⁺} {x⁻}))
  where
    refactor :
      ∀ {b₁ b₂ a₁ a₂ a₃ a₄} →
        b₁ *ᴺ (a₁ +ᴺ a₃) +ᴺ b₂ *ᴺ (a₂ +ᴺ a₄) ≡
          (b₁ *ᴺ a₁ +ᴺ b₂ *ᴺ a₂) +ᴺ (b₁ *ᴺ a₃ +ᴺ b₂ *ᴺ a₄)
    refactor {b₁} {b₂} {a₁} {a₂} {a₃} {a₄} =
      begin
        b₁ *ᴺ (a₁ +ᴺ a₃) +ᴺ b₂ *ᴺ (a₂ +ᴺ a₄)
      ≡⟨ distrib-twoᴸ {a = b₁} {d = b₂} ⟩
        (b₁ *ᴺ a₁ +ᴺ b₁ *ᴺ a₃) +ᴺ (b₂ *ᴺ a₂ +ᴺ b₂ *ᴺ a₄)
      ≡⟨ transpose {b₁ *ᴺ a₁} ⟩
        (b₁ *ᴺ a₁ +ᴺ b₂ *ᴺ a₂) +ᴺ (b₁ *ᴺ a₃ +ᴺ b₂ *ᴺ a₄)
      ∎

module ≃-Reasoning where

  private
    variable
      a b c : ℤ

  infix 3 _≃-∎
  infixr 2 _≃⟨⟩_ step-≃ step-≃˘
  infix 1 ≃-begin_

  ≃-begin_ : a ≃ b → a ≃ b
  ≃-begin a≃b = a≃b

  _≃⟨⟩_ : ∀ a → a ≃ b → a ≃ b
  _ ≃⟨⟩ a≃b = a≃b

  step-≃ : ∀ a → b ≃ c → a ≃ b → a ≃ c
  step-≃ _ b≃c a≃b = ≃-trans a≃b b≃c

  step-≃˘ : ∀ a → b ≃ c → b ≃ a → a ≃ c
  step-≃˘ _ b≃c b≃a = ≃-trans (≃-sym b≃a) b≃c

  _≃-∎ : ∀ a → a ≃ a
  _ ≃-∎ = ≃-refl

  syntax step-≃ a b≃c a≃b = a ≃⟨ a≃b ⟩ b≃c
  syntax step-≃˘ a b≃c b≃a = a ≃˘⟨ b≃a ⟩ b≃c

open ≃-Reasoning

*-distrib-+ᴿ : ∀ {x y z} → (y + z) * x ≃ y * x + z * x
*-distrib-+ᴿ {x} {y} {z} =
  ≃-begin
    (y + z) * x
  ≃⟨ *-comm ⟩
    x * (y + z)
  ≃⟨ *-distrib-+ᴸ ⟩
    x * y + x * z
  ≃⟨ +-substᴸ *-comm ⟩
    y * x + x * z
  ≃⟨ +-substᴿ *-comm ⟩
    y * x + z * x
  ≃-∎

-- We now define the operation of _subtraction_ x - y of two integers
-- by the formula x - y ≔ x + (-y).
infixl 6 _-_
_-_ : ℤ → ℤ → ℤ
x - y = x + (- y)

-- One can easily check now that if a and b are natural numbers, then
-- a - b = a + -b = (a—0) + (0—b) = a—b, and so a—b is just the same
-- thing as a - b. Because of this we can now discard the — notation,
-- and use the familiar operation of subtraction instead.
natsub : ∀ {a b} → fromℕ a - fromℕ b ≃ a — b
natsub {a} {b} = cong (_+ᴺ b) +ᴺ-identityᴿ

-- Proposition 4.1.8 (Integers have no zero divisors). Let a and b be
-- integers such that ab = 0. Then either a = 0 or b = 0 (or both).
-- Exercise 4.1.5
*-both-zero : ∀ {a b} → a * b ≃ 0 → a ≃ 0 ∨ b ≃ 0
*-both-zero {a} {b} ab≃0 with at-least (trichotomy {a})
*-both-zero {a} {b} ab≃0 | nil a≃0 =
  ∨-introᴸ a≃0
*-both-zero {a} {b⁺ — b⁻} ab≃0 | pos record { n = n ; pos = n≢0 ; eq = a≃n—0 } =
  let nb⁺+0+0≡nb⁻+0 = ≃-trans (*-substᴸ {b = b⁺ — b⁻} (≃-sym a≃n—0)) ab≃0
      nb⁺+0≡nb⁻ = +ᴺ-cancelᴿ {n = n *ᴺ b⁺ +ᴺ 0} nb⁺+0+0≡nb⁻+0
      nb⁺≡nb⁻ = trans (sym +ᴺ-identityᴿ) nb⁺+0≡nb⁻
      b⁺≡b⁻ = *ᴺ-cancelᴸ n≢0 nb⁺≡nb⁻
      b⁺+0≡b⁻ = trans +ᴺ-identityᴿ b⁺≡b⁻
   in ∨-introᴿ b⁺+0≡b⁻
*-both-zero {a} {b⁺ — b⁻} ab≃0 | neg record { n = n ; pos = n≢0 ; eq = a≃0—n } =
  let ab≃[0—n]b = *-substᴸ {b = b⁺ — b⁻} a≃0—n
      nb⁺≡nb⁻+0 = ≃-trans (≃-sym ab≃0) ab≃[0—n]b
      nb⁺≡nb⁻ = trans nb⁺≡nb⁻+0 +ᴺ-identityᴿ
      b⁺≡b⁻ = *ᴺ-cancelᴸ n≢0 nb⁺≡nb⁻
      b⁺+0≡b⁻ = trans +ᴺ-identityᴿ b⁺≡b⁻
   in ∨-introᴿ b⁺+0≡b⁻
