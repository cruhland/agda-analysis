module net.cruhland.Analysis.Chapter4.Rationals where

open import Agda.Builtin.FromNat using (Number)
-- Needed for resolving instance arguments
open import Relation.Binary.PropositionalEquality
  using () renaming (refl to ≡-refl)
open import net.cruhland.axioms.DecEq using (_≃?_)
open import net.cruhland.axioms.Eq using
  ( _≃_; _≄_; _≄ⁱ_; ≄ⁱ-elim; Eq; ≃-intro; ≄-intro
  ; sym; trans; module ≃-Reasoning
  )
open ≃-Reasoning
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Logic using (⊤; ⊥; ∨-forceᴸ; ¬_; yes; no)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)

import net.cruhland.models.Integers peanoArithmetic as ℤ
open ℤ using (ℤ; number; negative; ≃ᶻ-refl) renaming (_*_ to _*ᶻ_; eq to eq-ℤ)

[ab][cd]≃a[[bc]d] : ∀ {a b c d} → (a *ᶻ b) *ᶻ (c *ᶻ d) ≃ a *ᶻ ((b *ᶻ c) *ᶻ d)
[ab][cd]≃a[[bc]d] {a} {b} {c} {d} =
  begin
    (a *ᶻ b) *ᶻ (c *ᶻ d)
  ≃⟨ ℤ.*-assoc {a} ⟩
    a *ᶻ (b *ᶻ (c *ᶻ d))
  ≃˘⟨ ℤ.*-substᴿ {a} (ℤ.*-assoc {b}) ⟩
    a *ᶻ ((b *ᶻ c) *ᶻ d)
  ∎

swap-middle : ∀ {a b c d} → a *ᶻ ((b *ᶻ c) *ᶻ d) ≃ a *ᶻ ((c *ᶻ b) *ᶻ d)
swap-middle {a} {b} {c} {d} = ℤ.*-substᴿ {a} (ℤ.*-substᴸ (ℤ.*-comm {b}))

regroup : ∀ a b c d → (a *ᶻ b) *ᶻ (c *ᶻ d) ≃ a *ᶻ ((b *ᶻ d) *ᶻ c)
regroup a b c d =
  begin
    (a *ᶻ b) *ᶻ (c *ᶻ d)
  ≃⟨ ℤ.*-substᴿ {a *ᶻ b} (ℤ.*-comm {c}) ⟩
    (a *ᶻ b) *ᶻ (d *ᶻ c)
  ≃⟨ [ab][cd]≃a[[bc]d] {a} ⟩
    a *ᶻ ((b *ᶻ d) *ᶻ c)
  ∎

perm-adcb : ∀ {a b c d} → (a *ᶻ d) *ᶻ (c *ᶻ b) ≃ (a *ᶻ b) *ᶻ (c *ᶻ d)
perm-adcb {a} {b} {c} {d} =
  begin
    (a *ᶻ d) *ᶻ (c *ᶻ b)
  ≃⟨ regroup a d c b ⟩
    a *ᶻ ((d *ᶻ b) *ᶻ c)
  ≃⟨ swap-middle {a} {d} ⟩
    a *ᶻ ((b *ᶻ d) *ᶻ c)
  ≃˘⟨ regroup a b c d ⟩
    (a *ᶻ b) *ᶻ (c *ᶻ d)
  ∎

a≃b*c≃d : ∀ {a b c d} → a ≃ b → c ≃ d → a *ᶻ c ≃ b *ᶻ d
a≃b*c≃d {a} {b} {c} {d} a≃b c≃d =
  begin
    a *ᶻ c
  ≃⟨ ℤ.*-substᴸ a≃b ⟩
    b *ᶻ c
  ≃⟨ ℤ.*-substᴿ {b} c≃d ⟩
    b *ᶻ d
  ∎

{- 4.2 The rationals -}

-- Definition 4.2.1. A _rational number_ is an expression of the form
-- a//b, where a and b are integers and b is non-zero; a//0 is not
-- considered to be a rational number. Two rational numbers are
-- considered to be equal, a//b = c//d, if and only if ad = cb. The
-- set of all rational numbers is denoted ℚ.
infixl 8 _//_
record ℚ : Set where
  constructor _//_
  field
    n d : ℤ
    {{d≄ⁱ0}} : d ≄ⁱ 0

infix 4 _≃₀_
record _≃₀_ (p q : ℚ) : Set where
  instance constructor ≃₀-intro
  field
    {{elim}} : let p↑ // p↓ = p ; q↑ // q↓ = q in p↑ *ᶻ q↓ ≃ q↑ *ᶻ p↓

-- Exercise 4.2.1
≃₀-refl : ∀ {q} → q ≃₀ q
≃₀-refl {q↑ // q↓} = ≃₀-intro

≃₀-sym : ∀ {p q} → p ≃₀ q → q ≃₀ p
≃₀-sym (≃₀-intro {{≃-ℤ}}) = ≃₀-intro {{sym ≃-ℤ}}

≃₀-trans : ∀ {p q r} → p ≃₀ q → q ≃₀ r → p ≃₀ r
≃₀-trans
  {p↑ // p↓} {(q↑ // q↓) {{q↓≄ⁱ0}}} {r↑ // r↓}
  (≃₀-intro {{p↑q↓≃q↑p↓}}) (≃₀-intro {{q↑r↓≃r↑q↓}}) with q↑ ≃? 0
... | yes q↑≃0 =
  let p↑q↓≃0 =
        begin
          p↑ *ᶻ q↓
        ≃⟨ p↑q↓≃q↑p↓ ⟩
          q↑ *ᶻ p↓
        ≃⟨ ℤ.*-substᴸ q↑≃0 ⟩
          0 *ᶻ p↓
        ≃⟨ ℤ.*-zeroᴸ {p↓} ⟩
          0
        ∎
      r↑q↓≃0 =
        begin
          r↑ *ᶻ q↓
        ≃˘⟨ q↑r↓≃r↑q↓ ⟩
          q↑ *ᶻ r↓
        ≃⟨ ℤ.*-substᴸ q↑≃0 ⟩
          0 *ᶻ r↓
        ≃⟨ ℤ.*-zeroᴸ {r↓} ⟩
          0
        ∎
      p↑≃0 = ∨-forceᴸ (≄ⁱ-elim {{i = q↓≄ⁱ0}}) (ℤ.*-either-zero {p↑} p↑q↓≃0)
      r↑≃0 = ∨-forceᴸ (≄ⁱ-elim {{i = q↓≄ⁱ0}}) (ℤ.*-either-zero {r↑} r↑q↓≃0)
      p↑r↓≃r↑p↓ =
        begin
          p↑ *ᶻ r↓
        ≃⟨ ℤ.*-substᴸ p↑≃0 ⟩
          0 *ᶻ r↓
        ≃⟨ ℤ.*-zeroᴸ {r↓} ⟩
          0
        ≃˘⟨ ℤ.*-zeroᴸ {p↓} ⟩
          0 *ᶻ p↓
        ≃˘⟨ ℤ.*-substᴸ r↑≃0 ⟩
          r↑ *ᶻ p↓
        ∎
   in ≃₀-intro {{p↑r↓≃r↑p↓}}
... | no q↑≄0 =
  let p↑r↓[q↑q↓]≃r↑p↓[q↑q↓] =
        begin
          (p↑ *ᶻ r↓) *ᶻ (q↑ *ᶻ q↓)
        ≃⟨ perm-adcb {a = p↑} {c = q↑} ⟩
          (p↑ *ᶻ q↓) *ᶻ (q↑ *ᶻ r↓)
        ≃⟨ a≃b*c≃d p↑q↓≃q↑p↓ q↑r↓≃r↑q↓ ⟩
          (q↑ *ᶻ p↓) *ᶻ (r↑ *ᶻ q↓)
        ≃⟨ perm-adcb {a = q↑} {c = r↑} ⟩
          (q↑ *ᶻ q↓) *ᶻ (r↑ *ᶻ p↓)
        ≃⟨ ℤ.*-comm {q↑ *ᶻ q↓} ⟩
          (r↑ *ᶻ p↓) *ᶻ (q↑ *ᶻ q↓)
        ∎
      q↑q↓≄0 = ℤ.*-neither-zero q↑≄0 (≄ⁱ-elim {{i = q↓≄ⁱ0}})
      p↑r↓≃r↑p↓ = ℤ.*-cancelᴿ q↑q↓≄0 p↑r↓[q↑q↓]≃r↑p↓[q↑q↓]
   in ≃₀-intro {{p↑r↓≃r↑p↓}}

infix 4 _≄₀ⁱ_
record _≄₀ⁱ_ (p q : ℚ) : Set where
  instance constructor ≄₀ⁱ-intro
  field
    {{elim}} : let p↑ // p↓ = p ; q↑ // q↓ = q in p↑ *ᶻ q↓ ≄ⁱ q↑ *ᶻ p↓

≄₀ⁱ-elim : ∀ {p q} {{i : p ≄₀ⁱ q}} → ¬ (p ≃₀ q)
≄₀ⁱ-elim {{≄₀ⁱ-intro {{≄ⁱ-ℤ}}}} (≃₀-intro {{≃-ℤ}}) = ≄ⁱ-elim {{i = ≄ⁱ-ℤ}} ≃-ℤ

instance
  eq : Eq ℚ
  eq = record
    { _≃_ = _≃₀_
    ; refl = ≃₀-refl
    ; sym = ≃₀-sym
    ; trans = ≃₀-trans
    ; _≄ⁱ_ = _≄₀ⁱ_
    ; ≄ⁱ-elim = λ {{i}} → ≄₀ⁱ-elim {{i}}
    }

_ : 3 // 4 ≃ 6 // 8
_ = ≃-intro

_ : 6 // 8 ≃ -3 // -4
_ = ≃-intro

_ : 3 // 4 ≄ 4 // 3
_ = ≄-intro
