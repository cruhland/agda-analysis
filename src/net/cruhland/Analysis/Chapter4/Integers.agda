module net.cruhland.Analysis.Chapter4.Integers where

open import Agda.Builtin.FromNat using (Number)
open import Agda.Builtin.FromNeg using (Negative)
import Agda.Builtin.Nat as Nat
open import Function using (_∘_; const; flip)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; refl; subst; sym; trans; module ≡-Reasoning)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Logic using
  (⊤; ⊤-intro; ∧-elimᴿ; _∨_; ∨-introᴸ; ∨-introᴿ; ⊥; ⊥-elim; ¬_; _↔_; ↔-intro)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)
open import net.cruhland.models.Setoid using (Setoid₀)

open ≡-Reasoning
open PeanoArithmetic peanoArithmetic using
  ( ℕ; <→<⁺; tri-<; tri-≡; tri->) renaming
  ( step to stepᴺ; step≢zero to stepᴺ≢zero; step≡+ to stepᴺ≡+
  ; _+_ to _+ᴺ_; +-assoc to +ᴺ-assoc; +-both-zero to +ᴺ-both-zero
  ; +-cancelᴸ to +ᴺ-cancelᴸ; +-cancelᴿ to +ᴺ-cancelᴿ; +-comm to +ᴺ-comm
  ; +-zeroᴿ to +ᴺ-identityᴿ; +-positive to +ᴺ-positive; +-stepᴸ to +ᴺ-stepᴸ
  ; +-unchanged to +ᴺ-unchanged
  ; _*_ to _*ᴺ_; *-assoc to *ᴺ-assoc; *-cancelᴸ to *ᴺ-cancelᴸ; *-comm to *ᴺ-comm
  ; *-distrib-+ᴸ to *ᴺ-distrib-+ᴺᴸ; *-distrib-+ᴿ to *ᴺ-distrib-+ᴺᴿ
  ; *-positive to *ᴺ-positive; *-zeroᴿ to *ᴺ-zeroᴿ
  ; number to ℕ-number; Positive to Positiveᴺ; trichotomy to trichotomyᴺ
  )
open import net.cruhland.models.Integers peanoArithmetic
  using (_—_; _≃_; _≄_; _+_; _*_; -_; fromNat; ≃-intro; ≃-refl; ℤ; ℤ⁺; ℤ⁻)
  renaming (number to ℤ-number; negative to ℤ-negative)

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
_ = ≃-intro refl

_ : 3 — 5 ≄ 2 — 3
_ = λ ()

-- Exercise 4.1.1
_ : ∀ {a} → a ≃ a
_ = ≃-refl

open _≃_ using (≃-elim)

≃-sym : ∀ {a b} → a ≃ b → b ≃ a
≃-sym {a⁺ — a⁻} {b⁺ — b⁻} = ≃-intro ∘ sym ∘ ≃-elim

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
≃-trans {a⁺ — a⁻} {b⁺ — b⁻} {c⁺ — c⁻} a≃b b≃c =
    ≃-intro (+ᴺ-cancelᴿ [a⁺+c⁻]+[b⁺+b⁻]≡[c⁺+a⁻]+[b⁺+b⁻])
  where
    a⁺+b⁻≡b⁺+a⁻ = ≃-elim a≃b
    b⁺+c⁻≡c⁺+b⁻ = ≃-elim b≃c
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
_ : ℤ → ℤ → ℤ
_ = _+_

-- The product of two integers, (a—b) × (c—d), is defined by
-- (a—b) × (c—d) ≔ (ac + bd)—(ad + bc).
_ : ℤ → ℤ → ℤ
_ = _*_

-- Thus for instance, (3—5) + (1—4) is equal to (4—9).
_ : 3 — 5 + 1 — 4 ≃ 4 — 9
_ = ≃-intro refl

-- There is however one thing we have to check before we can accept
-- these definitions - we have to check that if we replace one of the
-- integers by an equal integer, that the sum or product does not
-- change. For instance (3—5) is equal to (2—4), so (3—5) + (1—4)
-- ought to have the same value as (2—4) + (1—4), otherwise this would
-- not give a consistent definition of addition.
_ : 3 — 5 + 1 — 4 ≃ 2 — 4 + 1 — 4
_ = ≃-intro refl

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
+-substᴸ {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} {b⁺ — b⁻} a₁≃a₂ = ≃-intro eq
  where
    a₁⁺+a₂⁻≡a₂⁺+a₁⁻ = ≃-elim a₁≃a₂
    eq =
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
+-comm {a⁺ — a⁻} {b⁺ — b⁻} = ≃-intro eq
  where
    eq =
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
*-substᴸ {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} {b⁺ — b⁻} a₁≃a₂ = ≃-intro eq
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

    a₁⁺a₂⁻≡a₂⁺a₁⁻ = ≃-elim a₁≃a₂
    eq =
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

*-comm : ∀ {a b} → a * b ≃ b * a
*-comm {a⁺ — a⁻} {b⁺ — b⁻} = ≃-intro eq
  where
    eq =
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
_ = ≃-intro refl

*-compat-*ᴺ : ∀ {n m} → n — 0 * m — 0 ≃ (n *ᴺ m) — 0
*-compat-*ᴺ {n} {m} = ≃-intro eq
  where
    eq =
      begin
        n *ᴺ m +ᴺ 0 +ᴺ 0
      ≡⟨ +ᴺ-assoc {n *ᴺ m} ⟩
        n *ᴺ m +ᴺ (0 +ᴺ 0)
      ≡˘⟨ cong (λ x → n *ᴺ m +ᴺ (x +ᴺ 0)) (*ᴺ-zeroᴿ {n}) ⟩
        n *ᴺ m +ᴺ (n *ᴺ 0 +ᴺ 0)
      ∎

-- Furthermore, (n—0) is equal to (m—0) if and only if n = m.
_ : ∀ {n m} → n — 0 ≃ m — 0 ↔ n ≡ m
_ = ↔-intro (+ᴺ-cancelᴿ ∘ ≃-elim) (≃-intro ∘ cong (_+ᴺ 0))

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
_ : Number ℤ
_ = ℤ-number

-- For instance the natural number 3 is now considered to be the same
-- as the integer 3—0, thus 3 = 3—0.
_ : 3 ≃ 3 — 0
_ = ≃-intro refl

-- In particular 0 is equal to 0—0 and 1 is equal to 1—0.
_ : 0 ≃ 0 — 0
_ = ≃-intro refl

_ : 1 ≃ 1 — 0
_ = ≃-intro refl

-- Of course, if we set n equal to n—0, then it will also be equal to
-- any other integer which is equal to n—0, for instance 3 is equal
-- not only to 3—0, but also to 4—1, 5—2, etc.
_ : 3 ≃ 4 — 1
_ = ≃-intro refl

_ : 3 ≃ 5 — 2
_ = ≃-intro refl

-- We can now define incrementation on the integers by defining
-- step x ≔ x + 1 for any integer x; this is of course consistent with
-- our definition of the increment operation for natural
-- numbers. However, this is no longer an important operation for us,
-- as it has been now superceded by the more general notion of
-- addition.
step : ℤ → ℤ
step x = x + 1

ℤ⁺s≡sℤ⁺ : ∀ {a} → ℤ⁺ (step a) ≡ stepᴺ (ℤ⁺ a)
ℤ⁺s≡sℤ⁺ {a⁺ — _} = sym stepᴺ≡+

ℤ⁻s≡ℤ⁻ : ∀ {a} → ℤ⁻ (step a) ≡ ℤ⁻ a
ℤ⁻s≡ℤ⁻ {_ — a⁻} = +ᴺ-identityᴿ

-- Definition 4.1.4 (Negation of integers). If (a—b) is an integer, we
-- define the negation -(a—b) to be the integer (b—a).
_ : ℤ → ℤ
_ = -_

-- In particular if n = n—0 is a positive natural number, we can
-- define its negation -n = 0—n.
-- [note] Here we must use a conversion function since n is not a
-- literal.
fromℕ : ℕ → ℤ
fromℕ n = n — 0

_ : ∀ {n} → - (fromℕ n) ≃ 0 — n
_ = ≃-intro refl

-- For instance -(3—5) = (5—3).
_ : -(3 — 5) ≃ 5 — 3
_ = ≃-intro refl

-- One can check this definition is well-defined.
-- Exercise 4.1.2
neg-subst : ∀ {a₁ a₂} → a₁ ≃ a₂ → - a₁ ≃ - a₂
neg-subst {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} a₁≃a₂ = ≃-intro eq
  where
    a₁⁺+a₂⁻≡a₂⁺+a₁⁻ = ≃-elim a₁≃a₂
    eq =
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

trichotomy : ∀ x → Trichotomy x
trichotomy (x⁺ — x⁻) = record { at-least = one≤ ; at-most = one≮ }
  where
    one≤ : AtLeastOne (x⁺ — x⁻)
    one≤ with trichotomyᴺ {x⁺} {x⁻}
    one≤ | tri-< x⁺<x⁻ =
      let record { d = n ; d≢z = pos-n ; n+d≡m = x⁺+n≡x⁻ } = <→<⁺ x⁺<x⁻
       in neg (record { n = n ; pos = pos-n ; eq = ≃-intro x⁺+n≡x⁻ })
    one≤ | tri-≡ x⁺≡x⁻ = nil (≃-intro (trans +ᴺ-identityᴿ x⁺≡x⁻))
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
       in pos (record { n = n ; pos = pos-n ; eq = ≃-intro x⁺—x⁻≃n })

    one≮ : ¬ MoreThanOne (x⁺ — x⁻)
    one≮ (nil∧pos (≃-intro x⁺+0≡x⁻)
                  record { n = n ; pos = n≢0 ; eq = ≃-intro x⁺+0≡n+x⁻ }) =
      let x⁻+n≡x⁻ = trans (+ᴺ-comm {x⁻}) (trans (sym x⁺+0≡n+x⁻) x⁺+0≡x⁻)
       in n≢0 (+ᴺ-unchanged x⁻+n≡x⁻)
    one≮ (nil∧neg (≃-intro x⁺+0≡x⁻)
                  record { n = n ; pos = n≢0 ; eq = ≃-intro x⁺+n≡x⁻ }) =
      n≢0 (+ᴺ-cancelᴸ (trans x⁺+n≡x⁻ (sym x⁺+0≡x⁻)))
    one≮ (pos∧neg record { n = n₁ ; pos = n₁≢0 ; eq = ≃-intro x⁺+0≡n₁+x⁻ }
                     record { n = n₂ ; pos = n₂≢0 ; eq = ≃-intro x⁺+n₂≡x⁻ }) =
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
+-assoc {x⁺ — x⁻} {y⁺ — y⁻} {z⁺ — z⁻} = ≃-intro eq
  where
    eq =
      begin
        ((x⁺ +ᴺ y⁺) +ᴺ z⁺) +ᴺ (x⁻ +ᴺ (y⁻ +ᴺ z⁻))
      ≡⟨ cong (_+ᴺ (x⁻ +ᴺ (y⁻ +ᴺ z⁻))) (+ᴺ-assoc {x⁺}) ⟩
        (x⁺ +ᴺ (y⁺ +ᴺ z⁺)) +ᴺ (x⁻ +ᴺ (y⁻ +ᴺ z⁻))
      ≡˘⟨ cong ((x⁺ +ᴺ (y⁺ +ᴺ z⁺)) +ᴺ_) (+ᴺ-assoc {x⁻}) ⟩
        (x⁺ +ᴺ (y⁺ +ᴺ z⁺)) +ᴺ ((x⁻ +ᴺ y⁻) +ᴺ z⁻)
      ∎

+-identityᴸ : ∀ {x} → 0 + x ≃ x
+-identityᴸ {x⁺ — x⁻} = ≃-intro refl

+-identityᴿ : ∀ {x} → x + 0 ≃ x
+-identityᴿ = ≃-trans +-comm +-identityᴸ

+-inverseᴸ : ∀ {x} → - x + x ≃ 0
+-inverseᴸ {x⁺ — x⁻} = ≃-intro eq
  where
    eq =
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
*-assoc {x⁺ — x⁻} {y⁺ — y⁻} {z⁺ — z⁻} = ≃-intro eq
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

    eq = a≡b+c≡d
           (refactor {z⁺} {z⁻} {x⁺} {x⁻})
           (sym (refactor {z⁻} {z⁺} {x⁺} {x⁻}))

*-identityᴸ : ∀ {x} → 1 * x ≃ x
*-identityᴸ {x⁺ — x⁻} = ≃-intro eq
  where
    eq =
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
    ≃-intro (a≡b+c≡d (refactor {x⁺} {x⁻}) (sym (refactor {x⁺} {x⁻})))
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
natsub {a} {b} = ≃-intro (cong (_+ᴺ b) +ᴺ-identityᴿ)

-- Proposition 4.1.8 (Integers have no zero divisors). Let a and b be
-- integers such that ab = 0. Then either a = 0 or b = 0 (or both).
-- Exercise 4.1.5
*-either-zero : ∀ {a b} → a * b ≃ 0 → a ≃ 0 ∨ b ≃ 0
*-either-zero {a} {b} ab≃0 with at-least (trichotomy a)
*-either-zero {a} {b} ab≃0 | nil a≃0 =
  ∨-introᴸ a≃0
*-either-zero {a} {b⁺ — b⁻} ab≃0
    | pos record { n = n ; pos = n≢0 ; eq = a≃n—0 } =
  let nb≃0 = ≃-trans (*-substᴸ {b = b⁺ — b⁻} (≃-sym a≃n—0)) ab≃0
      nb⁺+0+0≡nb⁻+0 = ≃-elim nb≃0
      nb⁺+0≡nb⁻ = +ᴺ-cancelᴿ {n = n *ᴺ b⁺ +ᴺ 0} nb⁺+0+0≡nb⁻+0
      nb⁺≡nb⁻ = trans (sym +ᴺ-identityᴿ) nb⁺+0≡nb⁻
      b⁺≡b⁻ = *ᴺ-cancelᴸ n≢0 nb⁺≡nb⁻
      b⁺+0≡b⁻ = trans +ᴺ-identityᴿ b⁺≡b⁻
   in ∨-introᴿ (≃-intro b⁺+0≡b⁻)
*-either-zero {a} {b⁺ — b⁻} ab≃0
    | neg record { n = n ; pos = n≢0 ; eq = a≃0—n } =
  let ab≃[0—n]b = *-substᴸ {b = b⁺ — b⁻} a≃0—n
      0≃-nb = ≃-trans (≃-sym ab≃0) ab≃[0—n]b
      nb⁺≡nb⁻+0 = ≃-elim 0≃-nb
      nb⁺≡nb⁻ = trans nb⁺≡nb⁻+0 +ᴺ-identityᴿ
      b⁺≡b⁻ = *ᴺ-cancelᴸ n≢0 nb⁺≡nb⁻
      b⁺+0≡b⁻ = trans +ᴺ-identityᴿ b⁺≡b⁻
   in ∨-introᴿ (≃-intro b⁺+0≡b⁻)

-- Corollary 4.1.9 (Cancellation law for integers). If a, b, c are
-- integers such that ac = bc and c is non-zero, then a = b.
-- Exercise 4.1.6
sub-substᴸ : ∀ {a₁ a₂ b} → a₁ ≃ a₂ → a₁ - b ≃ a₂ - b
sub-substᴸ = +-substᴸ

sub-substᴿ : ∀ {a b₁ b₂} → b₁ ≃ b₂ → a - b₁ ≃ a - b₂
sub-substᴿ = +-substᴿ ∘ neg-subst

*-negᴸ : ∀ {a b} → - a * b ≃ - (a * b)
*-negᴸ {a⁺ — a⁻} {b⁺ — b⁻} = ≃-intro eq
  where
    eq =
      begin
        (a⁻ *ᴺ b⁺ +ᴺ a⁺ *ᴺ b⁻) +ᴺ (a⁺ *ᴺ b⁺ +ᴺ a⁻ *ᴺ b⁻)
      ≡⟨ cong (_+ᴺ (a⁺ *ᴺ b⁺ +ᴺ a⁻ *ᴺ b⁻)) (+ᴺ-comm {a⁻ *ᴺ b⁺}) ⟩
        (a⁺ *ᴺ b⁻ +ᴺ a⁻ *ᴺ b⁺) +ᴺ (a⁺ *ᴺ b⁺ +ᴺ a⁻ *ᴺ b⁻)
      ≡⟨ cong ((a⁺ *ᴺ b⁻ +ᴺ a⁻ *ᴺ b⁺) +ᴺ_) (+ᴺ-comm {a⁺ *ᴺ b⁺}) ⟩
        (a⁺ *ᴺ b⁻ +ᴺ a⁻ *ᴺ b⁺) +ᴺ (a⁻ *ᴺ b⁻ +ᴺ a⁺ *ᴺ b⁺)
      ∎

*-negᴿ : ∀ {a b} → a * - b ≃ - (a * b)
*-negᴿ = ≃-trans *-comm (≃-trans *-negᴸ (neg-subst *-comm))

*-distrib-subᴸ : ∀ {a b c} → c * (a - b) ≃ c * a - c * b
*-distrib-subᴸ = ≃-trans *-distrib-+ᴸ (+-substᴿ *-negᴿ)

*-distrib-subᴿ : ∀ {a b c} → (a - b) * c ≃ a * c - b * c
*-distrib-subᴿ = ≃-trans *-distrib-+ᴿ (+-substᴿ *-negᴸ)

a-a≃0 : ∀ {a} → a - a ≃ 0
a-a≃0 {a⁺ — a⁻} = ≃-intro (trans +ᴺ-identityᴿ (+ᴺ-comm {a⁺}))

*-cancelᴿ : ∀ {a b c} → c ≄ 0 → a * c ≃ b * c → a ≃ b
*-cancelᴿ {a} {b} {c} c≄0 ac≃bc with
  let ac-bc≃0 = ≃-trans (sub-substᴸ {b = b * c} ac≃bc) a-a≃0
      [a-b]c≃0 = ≃-trans (*-distrib-subᴿ {a}) ac-bc≃0
   in *-either-zero [a-b]c≃0
*-cancelᴿ {a} {b} {c} c≄0 ac≃bc | ∨-introᴸ a-b≃0 =
  ≃-begin
    a
  ≃˘⟨ +-identityᴿ ⟩
    a + 0
  ≃˘⟨ +-substᴿ +-inverseᴸ ⟩
    a + (- b + b)
  ≃˘⟨ +-assoc ⟩
    a - b + b
  ≃⟨ +-substᴸ a-b≃0 ⟩
    0 + b
  ≃⟨ +-identityᴸ ⟩
    b
  ≃-∎
*-cancelᴿ {a} {b} {c} c≄0 ac≃bc | ∨-introᴿ c≃0 =
  ⊥-elim (c≄0 c≃0)

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
    n≃m+a : m ≃ n + fromℕ a

infix 4 _<_
record _<_ (n m : ℤ) : Set where
  constructor <-intro
  field
    n≤m : n ≤ m
    n≄m : n ≄ m

infix 4 _>_
_>_ = flip _<_

_ : Negative ℤ
_ = ℤ-negative

_ : 5 > -3
_ = <-intro (≤-intro 8 (≃-intro refl)) λ ()

-- Lemma 4.1.11 (Properties of order).
-- Exercise 4.1.7
ℕ≡→ℤ≃ : ∀ {n m} → n ≡ m → fromℕ n ≃ fromℕ m
ℕ≡→ℤ≃ refl = ≃-intro refl

n≃0→n≡0 : ∀ {n} → fromℕ n ≃ 0 → n ≡ 0
n≃0→n≡0 (≃-intro n+0≡0) = trans (sym +ᴺ-identityᴿ) n+0≡0

≃ᴿ-+ᴸ-toᴿ : ∀ {a b c} → a ≃ b + c → a - b ≃ c
≃ᴿ-+ᴸ-toᴿ {a} {b} {c} a≃b+c =
  ≃-begin
    a - b
  ≃⟨ sub-substᴸ a≃b+c ⟩
    b + c - b
  ≃⟨ sub-substᴸ +-comm ⟩
    c + b - b
  ≃⟨ +-assoc ⟩
    c + (b - b)
  ≃⟨ +-substᴿ +-inverseᴿ ⟩
    c + 0
  ≃⟨ +-identityᴿ ⟩
    c
  ≃-∎

≃ᴸ-subᴿ-toᴸ : ∀ {a b c} → a - b ≃ c → a ≃ b + c
≃ᴸ-subᴿ-toᴸ {a} {b} {c} a-b≃c =
  ≃-begin
    a
  ≃˘⟨ +-identityᴿ ⟩
    a + 0
  ≃˘⟨ +-substᴿ +-inverseᴿ ⟩
    a + (b - b)
  ≃⟨ +-substᴿ +-comm ⟩
    a + (- b + b)
  ≃˘⟨ +-assoc ⟩
    a - b + b
  ≃⟨ +-substᴸ a-b≃c ⟩
    c + b
  ≃⟨ +-comm ⟩
    b + c
  ≃-∎

vanish : ∀ {x y} → x + y - y ≃ x
vanish {x} {y} =
  ≃-begin
    x + y - y
  ≃⟨ +-assoc ⟩
    x + (y - y)
  ≃⟨ +-substᴿ +-inverseᴿ ⟩
    x + 0
  ≃⟨ +-identityᴿ ⟩
    x
  ≃-∎

+-cancelᴿ : ∀ {a b c} → a + c ≃ b + c → a ≃ b
+-cancelᴿ {a} {b} {c} a+c≃b+c =
    ≃-begin
      a
    ≃˘⟨ vanish ⟩
      a + c - c
    ≃⟨ sub-substᴸ a+c≃b+c ⟩
      b + c - c
    ≃⟨ vanish ⟩
      b
    ≃-∎

+ᴺ-to-+ : ∀ {n m} → fromℕ (n +ᴺ m) ≃ fromℕ n + fromℕ m
+ᴺ-to-+ {n} {m} = ≃-intro refl

*ᴺ-to-* : ∀ {n m} → fromℕ (n *ᴺ m) ≃ fromℕ n * fromℕ m
*ᴺ-to-* {n} {m} = ≃-intro eq
  where
    eq =
      begin
        n *ᴺ m +ᴺ (n *ᴺ 0 +ᴺ 0)
      ≡⟨ cong (λ x → n *ᴺ m +ᴺ (x +ᴺ 0)) (*ᴺ-zeroᴿ {n}) ⟩
        n *ᴺ m +ᴺ (0 +ᴺ 0)
      ≡˘⟨ +ᴺ-assoc {n *ᴺ m} ⟩
        n *ᴺ m +ᴺ 0 +ᴺ 0
      ∎

IsPositive-subst : ∀ {a₁ a₂} → a₁ ≃ a₂ → IsPositive a₁ → IsPositive a₂
IsPositive-subst a₁≃a₂ record { n = n ; pos = n≢0 ; eq = a₁≃n } =
  record { n = n ; pos = n≢0 ; eq = ≃-trans (≃-sym a₁≃a₂) a₁≃n }

-- Exercise 4.1.3
neg-mult : ∀ {a} → - a ≃ -1 * a
neg-mult {a⁺ — a⁻} = ≃-intro eq
  where
    eq =
      begin
        a⁻ +ᴺ (a⁺ +ᴺ 0)
      ≡⟨ cong (a⁻ +ᴺ_) (+ᴺ-comm {a⁺}) ⟩
        a⁻ +ᴺ (0 +ᴺ a⁺)
      ≡˘⟨ +ᴺ-assoc {a⁻} ⟩
        a⁻ +ᴺ 0 +ᴺ a⁺
      ∎

sub-distrib : ∀ {a b c} → a - (b + c) ≃ a - b - c
sub-distrib {a} {b} {c} =
  ≃-begin
    a - (b + c)
  ≃⟨⟩
    a + -(b + c)
  ≃⟨ +-substᴿ neg-mult ⟩
    a + -1 * (b + c)
  ≃⟨ +-substᴿ *-distrib-+ᴸ ⟩
    a + (-1 * b + -1 * c)
  ≃˘⟨ +-substᴿ (+-substᴸ neg-mult) ⟩
    a + (- b + -1 * c)
  ≃˘⟨ +-substᴿ (+-substᴿ neg-mult) ⟩
    a + (- b + - c)
  ≃˘⟨ +-assoc ⟩
    a - b - c
  ≃-∎

sub-cancelᴿ : ∀ {a b c} → a + c - (b + c) ≃ a - b
sub-cancelᴿ {a} {b} {c} =
  ≃-begin
    a + c - (b + c)
  ≃⟨ sub-distrib ⟩
    a + c - b - c
  ≃⟨⟩
    ((a + c) + - b) + - c
  ≃⟨ +-substᴸ +-assoc ⟩
    (a + (c + - b)) + - c
  ≃⟨ +-substᴸ (+-substᴿ +-comm) ⟩
    (a + (- b + c)) + - c
  ≃˘⟨ +-substᴸ +-assoc ⟩
    ((a + - b) + c) + - c
  ≃⟨⟩
    a - b + c - c
  ≃⟨ vanish ⟩
    a - b
  ≃-∎

+-preserves-pos : ∀ {a b} → IsPositive a → IsPositive b → IsPositive (a + b)
+-preserves-pos {a} {b}
  record { n = aᴺ ; pos = aᴺ≢0 ; eq = a≃aᴺ }
  record { n = bᴺ ; pos = bᴺ≢0 ; eq = b≃bᴺ } =
    record { n = aᴺ +ᴺ bᴺ ; pos = +ᴺ-positive aᴺ≢0 ; eq = a+b≃aᴺ+bᴺ }
  where
    a+b≃aᴺ+bᴺ =
      ≃-begin
        a + b
      ≃⟨ +-substᴸ a≃aᴺ ⟩
        fromℕ aᴺ + b
      ≃⟨ +-substᴿ b≃bᴺ ⟩
        fromℕ aᴺ + fromℕ bᴺ
      ≃˘⟨ +ᴺ-to-+ {aᴺ} ⟩
        fromℕ (aᴺ +ᴺ bᴺ)
      ≃-∎

*-preserves-pos : ∀ {a b} → IsPositive a → IsPositive b → IsPositive (a * b)
*-preserves-pos {a} {b}
  record { n = aᴺ ; pos = aᴺ≢0 ; eq = a≃aᴺ }
  record { n = bᴺ ; pos = bᴺ≢0 ; eq = b≃bᴺ } =
    record { n = aᴺ *ᴺ bᴺ ; pos = *ᴺ-positive aᴺ≢0 bᴺ≢0 ; eq = ab≃aᴺbᴺ }
  where
    ab≃aᴺbᴺ =
      ≃-begin
        a * b
      ≃⟨ *-substᴸ a≃aᴺ ⟩
        fromℕ aᴺ * b
      ≃⟨ *-substᴿ b≃bᴺ ⟩
        fromℕ aᴺ * fromℕ bᴺ
      ≃˘⟨ *ᴺ-to-* {aᴺ} ⟩
        fromℕ (aᴺ *ᴺ bᴺ)
      ≃-∎

neg-involutive : ∀ {a} → - (- a) ≃ a
neg-involutive {a⁺ — a⁻} = ≃-intro refl

neg-sub-swap : ∀ {a b} → - (a - b) ≃ b - a
neg-sub-swap {a} {b} =
  ≃-begin
    - (a - b)
  ≃⟨ neg-mult ⟩
    -1 * (a - b)
  ≃⟨ *-distrib-subᴸ ⟩
    -1 * a - -1 * b
  ≃˘⟨ +-substᴸ neg-mult ⟩
    - a - -1 * b
  ≃˘⟨ +-substᴿ (neg-subst neg-mult) ⟩
    - a - (- b)
  ≃⟨ +-substᴿ neg-involutive ⟩
    - a + b
  ≃⟨ +-comm ⟩
    b - a
  ≃-∎

sub-sign-swap : ∀ {a b} → IsNegative (a - b) → IsPositive (b - a)
sub-sign-swap {a} {b} record { n = n ; pos = n≢0 ; eq = a-b≃-n } =
    record { n = n ; pos = n≢0 ; eq = b-a≃n }
  where
    b-a≃n =
      ≃-begin
        b - a
      ≃˘⟨ neg-sub-swap ⟩
        - (a - b)
      ≃⟨ neg-subst a-b≃-n ⟩
        - (- fromℕ n)
      ≃⟨ neg-involutive {fromℕ n} ⟩
        fromℕ n
      ≃-∎

≤-antisym : ∀ {a b} → a ≤ b → b ≤ a → a ≃ b
≤-antisym {a} {b} (≤-intro n₁ b≃a+n₁) (≤-intro n₂ a≃b+n₂) =
  let n₁+ᴺn₂≃0 =
        ≃-begin
          fromℕ (n₁ +ᴺ n₂)
        ≃⟨ +ᴺ-to-+ {n₁} ⟩
          fromℕ n₁ + fromℕ n₂
        ≃˘⟨ +-identityᴸ ⟩
          0 + (fromℕ n₁ + fromℕ n₂)
        ≃˘⟨ +-substᴸ +-inverseᴸ ⟩
          (- a) + a + (fromℕ n₁ + fromℕ n₂)
        ≃⟨ +-assoc ⟩
          (- a) + (a + (fromℕ n₁ + fromℕ n₂))
        ≃˘⟨ +-substᴿ +-assoc ⟩
          (- a) + (a + fromℕ n₁ + fromℕ n₂)
        ≃˘⟨ +-substᴿ (+-substᴸ b≃a+n₁) ⟩
          (- a) + (b + fromℕ n₂)
        ≃˘⟨ +-substᴿ a≃b+n₂ ⟩
          (- a) + a
        ≃⟨ +-inverseᴸ ⟩
          0
        ≃-∎
      n₂≡0 = ∧-elimᴿ (+ᴺ-both-zero (n≃0→n≡0 n₁+ᴺn₂≃0))
   in ≃-trans (subst (λ x → a ≃ b + fromℕ x) n₂≡0 a≃b+n₂) +-identityᴿ

-- (a)
<→pos : ∀ {x y} → x < y → IsPositive (y - x)
<→pos (<-intro (≤-intro a y≃x+a) x≄y) = record
  { n = a
  ; pos = λ { refl → x≄y (≃-sym (≃-trans y≃x+a +-identityᴿ)) }
  ; eq = ≃ᴿ-+ᴸ-toᴿ y≃x+a
  }

pos→< : ∀ {x y} → IsPositive (y - x) → x < y
pos→< {x} {y} record { n = n ; pos = n≢0 ; eq = y-x≃n } =
    <-intro (≤-intro n (≃ᴸ-subᴿ-toᴸ y-x≃n)) x≄y
  where
    x≄y : x ≄ y
    x≄y x≃y =
      let n≃y-y = ≃-trans (≃-sym y-x≃n) (sub-substᴿ x≃y)
          n≃0 = ≃-trans n≃y-y +-inverseᴿ
          n≡0 = n≃0→n≡0 n≃0
       in n≢0 n≡0

pos-diff : ∀ {a b} → a < b ↔ IsPositive (b - a)
pos-diff = ↔-intro <→pos pos→<

-- (b) Addition preserves order
+-preserves-<ᴿ : ∀ {a b c} → a < b → a + c < b + c
+-preserves-<ᴿ a<b = pos→< (IsPositive-subst (≃-sym sub-cancelᴿ) (<→pos a<b))

-- (c) Positive multiplication preserves order
*⁺-preserves-<ᴿ : ∀ {a b c} → IsPositive c → a < b → a * c < b * c
*⁺-preserves-<ᴿ c>0 a<b =
  pos→< (IsPositive-subst *-distrib-subᴿ (*-preserves-pos (<→pos a<b) c>0))

-- (d) Negation reverses order
neg-reverses-< : ∀ {a b} → a < b → - b < - a
neg-reverses-< {a} {b} a<b = pos→< (IsPositive-subst b-a≃-a-[-b] (<→pos a<b))
  where
    b-a≃-a-[-b] =
      ≃-begin
        b - a
      ≃⟨ +-comm ⟩
        - a + b
      ≃˘⟨ +-substᴿ neg-involutive ⟩
        - a - (- b)
      ≃-∎

-- (e) Order is transitive
<-trans : ∀ {a b c} → a < b → b < c → a < c
<-trans {a} {b} {c} a<b b<c =
    let 0<b-a+c-b = +-preserves-pos (<→pos a<b) (<→pos b<c)
     in pos→< (IsPositive-subst b-a+c-b≃c-a 0<b-a+c-b)
  where
    b-a+c-b≃c-a =
      ≃-begin
        b - a + (c - b)
      ≃⟨ +-assoc ⟩
        b + (- a + (c - b))
      ≃⟨ +-substᴿ +-comm ⟩
        b + (c - b - a)
      ≃⟨ +-substᴿ (+-substᴸ +-comm) ⟩
        b + (- b + c - a)
      ≃⟨ +-substᴿ +-assoc ⟩
        b + (- b + (c - a))
      ≃˘⟨ +-assoc ⟩
        b - b + (c - a)
      ≃⟨ +-substᴸ +-inverseᴿ ⟩
        0 + (c - a)
      ≃⟨ +-identityᴸ ⟩
        c - a
      ≃-∎

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
    1≤ | nil b-a≃0 = 2nd (≃-sym (≃-trans (≃ᴸ-subᴿ-toᴸ b-a≃0) +-identityᴿ))
    1≤ | pos b-a>0 = 1st (pos→< b-a>0)
    1≤ | neg b-a<0 = 3rd (pos→< (sub-sign-swap b-a<0))

    ≤1 : ¬ TwoOfThree (a < b) (a ≃ b) (a > b)
    ≤1 (1∧2 (<-intro a≤b a≄b) a≃b) = a≄b a≃b
    ≤1 (1∧3 (<-intro a≤b a≄b) (<-intro b≤a b≄a)) = a≄b (≤-antisym a≤b b≤a)
    ≤1 (2∧3 a≃b (<-intro b≤a b≄a)) = b≄a (≃-sym a≃b)

-- Exercise 4.1.8
no-ind : ¬ ((P : ℤ → Set) → P 0 → (∀ {b} → P b → P (step b)) → ∀ a → P a)
no-ind ind = ¬allP (ind P Pz Ps)
  where
    P : ℤ → Set
    P x = 0 ≤ x

    Pz : P 0
    Pz = ≤-intro 0 (≃-intro refl)

    Ps : ∀ {b} → P b → P (step b)
    Ps {b} (≤-intro n (≃-intro b⁺+0≡n+b⁻)) =
        ≤-intro (stepᴺ n) (≃-intro sb⁺+0≡sn+sb⁻)
      where
        sb⁺+0≡sn+sb⁻ =
          begin
            ℤ⁺ (step b) +ᴺ 0
          ≡⟨ cong (_+ᴺ 0) (ℤ⁺s≡sℤ⁺ {b}) ⟩
            stepᴺ (ℤ⁺ b) +ᴺ 0
          ≡⟨⟩
            stepᴺ (ℤ⁺ b +ᴺ 0)
          ≡⟨ cong stepᴺ b⁺+0≡n+b⁻ ⟩
            stepᴺ (n +ᴺ ℤ⁻ b)
          ≡˘⟨ +ᴺ-stepᴸ {n} ⟩
            stepᴺ n +ᴺ ℤ⁻ b
          ≡˘⟨ cong (stepᴺ n +ᴺ_) (ℤ⁻s≡ℤ⁻ {b}) ⟩
            stepᴺ n +ᴺ ℤ⁻ (step b)
          ∎

    ¬allP : ¬ (∀ a → P a)
    ¬allP 0≰a =
      let ≤-intro n (≃-intro 0≡n+1) = 0≰a -1
       in stepᴺ≢zero (trans stepᴺ≡+ (sym 0≡n+1))
