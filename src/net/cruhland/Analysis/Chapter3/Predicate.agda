open import Function using (id; _∘_; const)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import net.cruhland.axiomatic.Logic using (LogicBundle)

module net.cruhland.Analysis.Chapter3.Predicate (LB : LogicBundle) where

open LogicBundle LB

{-= Chapter 3: Set theory (type theory predicate approach) =-}

{- 3.1 Fundamentals -}

PSet : Set → Set₁
PSet 𝒰 = 𝒰 → Set

record Eq (A : Set) : Set₁ where
  field
    _≡_ : A → A → Set

  infix 4 _≡_

  field
    sym : {x y : A} → x ≡ y → y ≡ x

module _ {𝒰} {eq : Eq 𝒰} where
  open Eq eq

  _∈_ : (x : 𝒰) → PSet 𝒰 → Set
  _∈_ x P = P x

  _∉_ : (x : 𝒰) → PSet 𝒰 → Set
  x ∉ P = ¬ (x ∈ P)

  infix 9 _∈_ _∉_

  _≗_ : PSet 𝒰 → PSet 𝒰 → Set
  A ≗ B = {x : 𝒰} → (x ∈ A → x ∈ B) ∧ (x ∈ B → x ∈ A)

  _≗̸_ : PSet 𝒰 → PSet 𝒰 → Set
  A ≗̸ B = ¬ (A ≗ B)

  infix 4 _≗_ _≗̸_

  ≗-refl : ∀ {A} → A ≗ A
  ≗-refl {_} = ∧-intro id id

  ≗-sym : ∀ {A B} → A ≗ B → B ≗ A
  ≗-sym A≗B {_} = ∧-intro (∧-elimᴿ A≗B) (∧-elimᴸ A≗B)

  ≗-trans : ∀ {A B C} → A ≗ B → B ≗ C → A ≗ C
  ≗-trans A≗B B≗C {_} =
    ∧-intro (∧-elimᴸ B≗C ∘ ∧-elimᴸ A≗B) (∧-elimᴿ A≗B ∘ ∧-elimᴿ B≗C)

  ∈-subst : ∀ {A B} {x : 𝒰} → A ≗ B → x ∈ A → x ∈ B
  ∈-subst A≗B x∈A = ∧-elimᴸ A≗B x∈A

  -- Axiom 3.2 (Empty set)
  ∅ : PSet 𝒰
  ∅ = const ⊥

  x∉∅ : {x : 𝒰} → x ∉ ∅
  x∉∅ = id

  ∅-unique : ∀ {∅′} → (∀ {x} → x ∉ ∅′) → ∅ ≗ ∅′
  ∅-unique x∉∅′ {x} =
    ∧-intro (λ x∈∅ → ⊥-elim (x∉∅ {x = x} x∈∅)) (λ x∈∅′ → ⊥-elim (x∉∅′ x∈∅′))

  -- Lemma 3.1.6 (Single choice)
  -- This is not provable in Agda because it's nonconstructive.
  -- Instead of using evidence that a set is not equal to the empty set,
  -- we will need to use direct evidence that an element of a set exists.

  -- Axiom 3.3 (Singleton sets and pair sets)
  singleton : 𝒰 → PSet 𝒰
  singleton x y = y ≡ x

  is-singleton-of : PSet 𝒰 → 𝒰 → Set
  is-singleton-of S a = ∀ x → x ∈ S ↔ x ≡ a

  singleton-exists : ∀ {a} → is-singleton-of (singleton a) a
  singleton-exists x = ∧-intro id id

  singleton-unique :
    ∀ {S S′ a} → is-singleton-of S a → is-singleton-of S′ a → S ≗ S′
  singleton-unique pS pS′ {x} =
    ∧-intro
      (∧-elimᴿ (pS′ x) ∘ ∧-elimᴸ (pS x))
      (∧-elimᴿ (pS x) ∘ ∧-elimᴸ (pS′ x))

  pair : 𝒰 → 𝒰 → PSet 𝒰
  pair x y z = z ≡ x ∨ z ≡ y

  is-pair-of : PSet 𝒰 → 𝒰 → 𝒰 → Set
  is-pair-of P a b = ∀ x → x ∈ P ↔ x ≡ a ∨ x ≡ b

  pair-exists : ∀ {a b} → is-pair-of (pair a b) a b
  pair-exists x = ∧-intro id id

  pair-unique : ∀ {P P′ a b} → is-pair-of P a b → is-pair-of P′ a b → P ≗ P′
  pair-unique pP pP′ {x} =
      ∧-intro
        (∧-elimᴿ (pP′ x) ∘ ∧-elimᴸ (pP x))
        (∧-elimᴿ (pP x) ∘ ∧-elimᴸ (pP′ x))
