module net.cruhland.Analysis.Chapter4.Rationals where

-- Needed for positive integer literals
import Agda.Builtin.FromNat as FromNat
-- Needed for resolving instance arguments
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Nullary.Decidable using (False)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.DecEq using (_≃?_; DecEq; ≃-derive; ≄-derive)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; Eq; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators using (_*_)
open import net.cruhland.models.Logic using
  (⊤; ∨-forceᴸ; ¬_; Dec; dec-map; yes; no)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)

import net.cruhland.models.Integers peanoArithmetic as ℤ
open ℤ using (ℤ)
open import net.cruhland.models.Rationals peanoArithmetic using (_//_; ℚ)

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

infix 4 _≃₀_
record _≃₀_ (p q : ℚ) : Set where
  instance constructor ≃₀-intro
  field
    {{elim}} : ℚ.n p * ℚ.d q ≃ ℚ.n q * ℚ.d p

-- Exercise 4.2.1
≃₀-refl : ∀ {q} → q ≃₀ q
≃₀-refl = ≃₀-intro

≃₀-sym : ∀ {p q} → p ≃₀ q → q ≃₀ p
≃₀-sym (≃₀-intro {{≃-ℤ}}) = ≃₀-intro {{sym ≃-ℤ}}

≃₀-trans : ∀ {p q r} → p ≃₀ q → q ≃₀ r → p ≃₀ r
≃₀-trans
  {record { n = p↑ ; d = p↓ }}
  {record { n = q↑ ; d = q↓ ; d≄0 = q↓≄0 }}
  {record { n = r↑ ; d = r↓ }}
  (≃₀-intro {{p↑q↓≃q↑p↓}}) (≃₀-intro {{q↑r↓≃r↑q↓}}) with q↑ ≃? 0
... | yes q↑≃0 =
  let p↑q↓≃0 =
        begin
          p↑ * q↓
        ≃⟨ p↑q↓≃q↑p↓ ⟩
          q↑ * p↓
        ≃⟨ AA.substᴸ q↑≃0 ⟩
          0 * p↓
        ≃⟨ ℤ.*-zeroᴸ {p↓} ⟩
          0
        ∎
      r↑q↓≃0 =
        begin
          r↑ * q↓
        ≃˘⟨ q↑r↓≃r↑q↓ ⟩
          q↑ * r↓
        ≃⟨ AA.substᴸ q↑≃0 ⟩
          0 * r↓
        ≃⟨ ℤ.*-zeroᴸ {r↓} ⟩
          0
        ∎
      p↑≃0 = ∨-forceᴸ q↓≄0 (ℤ.*-either-zero {p↑} p↑q↓≃0)
      r↑≃0 = ∨-forceᴸ q↓≄0 (ℤ.*-either-zero {r↑} r↑q↓≃0)
      p↑r↓≃r↑p↓ =
        begin
          p↑ * r↓
        ≃⟨ AA.substᴸ p↑≃0 ⟩
          0 * r↓
        ≃⟨ ℤ.*-zeroᴸ {r↓} ⟩
          0
        ≃˘⟨ ℤ.*-zeroᴸ {p↓} ⟩
          0 * p↓
        ≃˘⟨ AA.substᴸ r↑≃0 ⟩
          r↑ * p↓
        ∎
   in ≃₀-intro {{p↑r↓≃r↑p↓}}
... | no q↑≄0 =
  let p↑r↓[q↑q↓]≃r↑p↓[q↑q↓] =
        begin
          (p↑ * r↓) * (q↑ * q↓)
        ≃⟨ AA.perm-adcb {a = p↑} {c = q↑} ⟩
          (p↑ * q↓) * (q↑ * r↓)
        ≃⟨ AA.[a≃b][c≃d] p↑q↓≃q↑p↓ q↑r↓≃r↑q↓ ⟩
          (q↑ * p↓) * (r↑ * q↓)
        ≃⟨ AA.perm-adcb {a = q↑} {c = r↑} ⟩
          (q↑ * q↓) * (r↑ * p↓)
        ≃⟨ AA.comm {a = q↑ * q↓} ⟩
          (r↑ * p↓) * (q↑ * q↓)
        ∎
      q↑q↓≄0 = ℤ.*-neither-zero q↑≄0 q↓≄0
      p↑r↓≃r↑p↓ = ℤ.*-cancelᴿ q↑q↓≄0 p↑r↓[q↑q↓]≃r↑p↓[q↑q↓]
   in ≃₀-intro {{p↑r↓≃r↑p↓}}

instance
  eq : Eq ℚ
  eq = record
    { _≃_ = _≃₀_
    ; refl = ≃₀-refl
    ; sym = ≃₀-sym
    ; trans = ≃₀-trans
    }

  decEq : DecEq ℚ
  decEq = record { Constraint = λ _ _ → ⊤ ; _≃?_ = _≃?₀_ }
    where
      _≃?₀_ : (x y : ℚ) {{_ : ⊤}} → Dec (x ≃ y)
      p ≃?₀ q = dec-map (λ x → ≃₀-intro {{x}}) _≃₀_.elim ℤ≃?
        where
          ℤ≃? = ℚ.n p * ℚ.d q ≃? ℚ.n q * ℚ.d p

_ : 3 // 4 ≃ 6 // 8
_ = ≃-derive

_ : 6 // 8 ≃ -3 // -4
_ = ≃-derive

_ : 3 // 4 ≄ 4 // 3
_ = ≄-derive
