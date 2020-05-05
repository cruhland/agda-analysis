open import Function using (id; _∘_; const)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import net.cruhland.axiomatic.Logic using (LogicBundle)

module net.cruhland.Analysis.Chapter3.Predicate (LB : LogicBundle) where

open LogicBundle LB

{-= Chapter 3: Set theory (type theory predicate approach) =-}

{- 3.1 Fundamentals -}

PSet : Set → Set₁
PSet 𝒰 = 𝒰 → Set

_∈_ : ∀ {𝒰} (x : 𝒰) → PSet 𝒰 → Set
_∈_ x P = P x

_∉_ : ∀ {𝒰 : Set} (x : 𝒰) → PSet 𝒰 → Set
x ∉ P = ¬ (x ∈ P)

infix 9 _∈_ _∉_

_≗_ : ∀ {𝒰} → PSet 𝒰 → PSet 𝒰 → Set
_≗_ {𝒰} A B = {x : 𝒰} → (x ∈ A → x ∈ B) ∧ (x ∈ B → x ∈ A)

_≗̸_ : ∀ {𝒰} → PSet 𝒰 → PSet 𝒰 → Set
_≗̸_ {𝒰} A B = ¬ (A ≗ B)

infix 4 _≗_ _≗̸_

≗-refl : ∀ {𝒰} {A : PSet 𝒰} → A ≗ A
≗-refl {_} = ∧-intro id id

≗-sym : ∀ {𝒰} {A B : PSet 𝒰} → A ≗ B → B ≗ A
≗-sym A≗B {_} = ∧-intro (∧-elimᴿ A≗B) (∧-elimᴸ A≗B)

≗-trans : ∀ {𝒰} {A B C : PSet 𝒰} → A ≗ B → B ≗ C → A ≗ C
≗-trans A≗B B≗C {_} =
  ∧-intro (∧-elimᴸ B≗C ∘ ∧-elimᴸ A≗B) (∧-elimᴿ A≗B ∘ ∧-elimᴿ B≗C)

∈-subst : ∀ {𝒰} {A B : PSet 𝒰} {x : 𝒰} → A ≗ B → x ∈ A → x ∈ B
∈-subst A≗B x∈A = ∧-elimᴸ A≗B x∈A

-- Axiom 3.2 (Empty set)
∅ : ∀ {𝒰} → PSet 𝒰
∅ = const ⊥

x∉∅ : ∀ {𝒰} {x : 𝒰} → x ∉ ∅
x∉∅ = id

∅-unique : ∀ {𝒰} {∅′ : PSet 𝒰} → (∀ {x} → x ∉ ∅′) → ∅ ≗ ∅′
∅-unique x∉∅′ {x} =
  ∧-intro (λ x∈∅ → ⊥-elim (x∉∅ {x = x} x∈∅)) (λ x∈∅′ → ⊥-elim (x∉∅′ x∈∅′))

-- Lemma 3.1.6 (Single choice)
-- This is not provable in Agda because it's nonconstructive.
-- Instead of using evidence that a set is not equal to the empty set,
-- we will need to use direct evidence that an element of a set exists.

record Eq (A : Set) : Set₁ where
  field
    _≡_ : A → A → Set

  infix 4 _≡_

  field
    sym : {x y : A} → x ≡ y → y ≡ x

-- Axiom 3.3 (Singleton sets and pair sets)
singleton : ∀ {𝒰} {eq : Eq 𝒰} (x : 𝒰) → PSet 𝒰
singleton {eq = eq} x y = x ≡ y
  where open Eq eq

pair : ∀ {𝒰} {eq : Eq 𝒰} (x y : 𝒰) → PSet 𝒰
pair {eq = eq} x y z = x ≡ z ∨ y ≡ z
  where open Eq eq

is-singleton-of : ∀ {𝒰} {eq : Eq 𝒰} (S : PSet 𝒰) (a : 𝒰) → Set
is-singleton-of {eq = eq} S a = ∀ x → x ∈ S ↔ x ≡ a
  where open Eq eq

singleton-exists :
  ∀ {𝒰} {eq : Eq 𝒰} {a : 𝒰} →
    let open Eq eq in Σ (PSet 𝒰) λ S → is-singleton-of {eq = eq} S a
singleton-exists {eq = eq} {a} =
  Σ-intro (singleton {eq = eq} a) λ x → ∧-intro sym sym
    where open Eq eq

singleton-unique :
  ∀ {𝒰} {eq : Eq 𝒰} {a : 𝒰} {S S′ : PSet 𝒰} →
  is-singleton-of {eq = eq} S a → is-singleton-of {eq = eq} S′ a → S ≗ S′
singleton-unique {eq = eq} pS pS′ {x} =
    ∧-intro
      (∧-elimᴿ (pS′ x) ∘ ∧-elimᴸ (pS x))
      (∧-elimᴿ (pS x) ∘ ∧-elimᴸ (pS′ x))
  where open Eq eq
