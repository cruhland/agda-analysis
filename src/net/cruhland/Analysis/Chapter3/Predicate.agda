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

  _∈_ : 𝒰 → PSet 𝒰 → Set
  _∈_ x P = P x

  _∉_ : 𝒰 → PSet 𝒰 → Set
  x ∉ P = ¬ (x ∈ P)

  infix 9 _∈_ _∉_

  record _≗_ (A : PSet 𝒰) (B : PSet 𝒰) : Set where
    constructor mk≗
    field
      prf : ∀ {x} → x ∈ A ↔ x ∈ B

  open _≗_

  _≗̸_ : PSet 𝒰 → PSet 𝒰 → Set
  A ≗̸ B = ¬ (A ≗ B)

  infix 4 _≗_ _≗̸_

  ≗-refl : ∀ {A} → A ≗ A
  ≗-refl = mk≗ (∧-intro id id)

  ≗-sym : ∀ {A B} → A ≗ B → B ≗ A
  ≗-sym A≗B = mk≗ (∧-intro (∧-elimᴿ A↔B) (∧-elimᴸ A↔B))
    where
      A↔B = prf A≗B

  ≗-trans : ∀ {A B C} → A ≗ B → B ≗ C → A ≗ C
  ≗-trans A≗B B≗C =
    mk≗ (∧-intro (∧-elimᴸ B↔C ∘ ∧-elimᴸ A↔B) (∧-elimᴿ A↔B ∘ ∧-elimᴿ B↔C))
      where
        A↔B = prf A≗B
        B↔C = prf B≗C

  ≗-same : ∀ {A B C} → A ≗ C → B ≗ C → A ≗ B
  ≗-same A≗C B≗C = ≗-trans A≗C (≗-sym B≗C)

  ∈-subst : ∀ {A B x} → A ≗ B → x ∈ A → x ∈ B
  ∈-subst A≗B x∈A = ∧-elimᴸ (prf A≗B) x∈A

  -- Axiom 3.2 (Empty set)
  ∅ : PSet 𝒰
  ∅ = const ⊥

  x∉∅ : ∀ {x} → x ∉ ∅
  x∉∅ = id

  ∅-unique : ∀ {∅′} → (∀ {x} → x ∉ ∅′) → ∅ ≗ ∅′
  ∅-unique x∉∅′ =
    mk≗ (λ {x} →
      ∧-intro (λ x∈∅ → ⊥-elim (x∉∅ {x} x∈∅)) (λ x∈∅′ → ⊥-elim (x∉∅′ x∈∅′)))

  -- Lemma 3.1.6 (Single choice)
  -- This is not provable in Agda because it's nonconstructive.
  -- Instead of using evidence that a set is not equal to the empty set,
  -- we will need to use direct evidence that an element of a set exists.

  -- Axiom 3.3 (Singleton sets and pair sets)
  singleton : 𝒰 → PSet 𝒰
  singleton x y = y ≡ x

  singleton-unique :
    ∀ {S S′ a} → S ≗ singleton a → S′ ≗ singleton a → S ≗ S′
  singleton-unique = ≗-same

  pair : 𝒰 → 𝒰 → PSet 𝒰
  pair x y z = z ≡ x ∨ z ≡ y

  pair-unique : ∀ {P P′ a b} → P ≗ pair a b → P′ ≗ pair a b → P ≗ P′
  pair-unique = ≗-same
