open import Function using (id; _∘_; const)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import net.cruhland.axiomatic.Logic using (LogicBundle)

module net.cruhland.Analysis.Chapter3.Predicate (LB : LogicBundle) where

open LogicBundle LB

{-= Chapter 3: Set theory (type theory predicate approach) =-}

{- 3.1 Fundamentals -}

-- [note] We need some preliminary definitions that aren't in the
-- book, in order to define set theory concepts inside type theory.
-- These are taken from the paper "Setoids in type theory" by Gilles
-- Barthe, Venanzio Capretta, and Olivier Pons.

record IsEquivRel {α β} (A : Set α) (_≅_ : A → A → Set β) : Set (α ⊔ β) where
  field
    refl : ∀ {x} → x ≅ x
    sym : ∀ {x y} → x ≅ y → y ≅ x
    trans : ∀ {x y z} → x ≅ y → y ≅ z → x ≅ z

record SetoidOn β {α} (el : Set α) : Set (lsuc α ⊔ lsuc β) where
  field
    _≗_ : el → el → Set β
    isEquivRel : IsEquivRel el _≗_

record Setoid α β : Set (lsuc α ⊔ lsuc β) where
  field
    el : Set α
    setoidOn : SetoidOn β el

  open SetoidOn setoidOn public

open Setoid using (el)

mkSetoid :
  ∀ {α β} → (e : Set α) → (r : e → e → Set β) → IsEquivRel e r → Setoid α β
mkSetoid e r eqv =
  record { el = e; setoidOn = record { _≗_ = r; isEquivRel = eqv } }

_≐_ : ∀ {A : Set} → A → A → Set₁
_≐_ {A = A} x y = (P : A → Set) → P x → P y

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

≡-IsEquivRel : ∀ {A} → IsEquivRel A _≡_
≡-IsEquivRel = record
  { refl = refl
  ; sym = λ { refl → refl }
  ; trans = λ { refl refl → refl }
  }

≡-setoid : Set → Setoid lzero lzero
≡-setoid A = mkSetoid A _≡_ ≡-IsEquivRel

↔-IsEquivRel : ∀ {α} → IsEquivRel (Set α) _↔_
↔-IsEquivRel = record
  { refl = ↔-refl
  ; sym = ↔-sym
  ; trans = ↔-trans
  }

Set-setoid : ∀ {α} → Setoid (lsuc α) α
Set-setoid {α} = mkSetoid (Set α) _↔_ ↔-IsEquivRel

record _⇒_ {α₁ α₂ β₁ β₂} (A : Setoid α₁ α₂) (B : Setoid β₁ β₂)
    : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂) where
  open Setoid A renaming (_≗_ to _≗ᴬ_)
  open Setoid B renaming (_≗_ to _≗ᴮ_)

  field
    ap : el A → el B
    cong : ∀ {x y} → x ≗ᴬ y → ap x ≗ᴮ ap y

open _⇒_ using (ap)

record _>_⇒_
  {α₁ α₂ β₁ β₂} (elᴬ : Set α₁) (A : SetoidOn α₂ elᴬ) (B : Setoid β₁ β₂)
    : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂) where
  open SetoidOn A renaming (_≗_ to _≗ᴬ_)
  open Setoid B renaming (_≗_ to _≗ᴮ_)

  field
    app : elᴬ → el B
    congg : ∀ {x y} → x ≗ᴬ y → app x ≗ᴮ app y

open _>_⇒_ using (app; congg)

⇒-setoid :
  ∀ {α₁ α₂ β₁ β₂} → Setoid α₁ α₂ → Setoid β₁ β₂ →
  Setoid (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂) (α₁ ⊔ β₂)
⇒-setoid A B = mkSetoid (A ⇒ B) rel eqvRel
  where
    open Setoid B renaming (_≗_ to _≗ᴮ_; isEquivRel to eqvᴮ)
    open IsEquivRel eqvᴮ renaming (refl to reflᴮ; sym to symᴮ; trans to transᴮ)

    rel = λ f g → ∀ x → ap f x ≗ᴮ ap g x
    eqvRel = record
      { refl = λ {f} x → reflᴮ
      ; sym = λ {f g} f≗g x → symᴮ (f≗g x)
      ; trans = λ {f g h} f≗g g≗h x → transᴮ (f≗g x) (g≗h x)
      }

>⇒-setoid :
  ∀ {α₁ α₂ β₁ β₂} {𝒜 : Set α₁} → (A : SetoidOn α₂ 𝒜) → (B : Setoid β₁ β₂) →
  SetoidOn (α₁ ⊔ β₂) (𝒜 > A ⇒ B)
>⇒-setoid A B = record { _≗_ = rel ; isEquivRel = eqvRel }
  where
    open Setoid B renaming (_≗_ to _≗ᴮ_; isEquivRel to eqvᴮ)
    open IsEquivRel eqvᴮ renaming (refl to reflᴮ; sym to symᴮ; trans to transᴮ)

    rel = λ f g → ∀ x → app f x ≗ᴮ app g x
    eqvRel = record
      { refl = λ {f} x → reflᴮ
      ; sym = λ {f g} f≗g x → symᴮ (f≗g x)
      ; trans = λ {f g h} f≗g g≗h x → transᴮ (f≗g x) (g≗h x)
      }

SP : ∀ {α₁ α₂} → Setoid α₁ α₂ → Set (α₁ ⊔ α₂ ⊔ lsuc lzero)
SP A = A ⇒ Set-setoid {lzero}

SubSetoid : ∀ {α₁ α₂} (A : Setoid α₁ α₂) → SP A → Setoid α₁ α₂
SubSetoid A P = mkSetoid (Σ (Setoid.el A) (ap P)) rel eqvRel
  where
    open Setoid A renaming (_≗_ to _≗ᴬ_; isEquivRel to eqvᴬ)
    open IsEquivRel eqvᴬ renaming (refl to reflᴬ; sym to symᴬ; trans to transᴬ)

    rel = λ (x y : Σ (Setoid.el A) (ap P)) → fst x ≗ᴬ fst y
    eqvRel = record
      { refl = reflᴬ
      ; sym = symᴬ
      ; trans = transᴬ
      }
-- [note] End preliminary definitions, back to the book

-- Definition 3.1.1
-- We define a set A to be any unordered collection of objects.

-- [note] A set is defined as a setoid-predicate on some setoid
-- "universe" of objects 𝒰.
PSet : ∀ {υ₁ υ₂} → Setoid υ₁ υ₂ → Set (υ₁ ⊔ υ₂ ⊔ lsuc lzero)
PSet 𝒰 = SP 𝒰

QSet : ∀ {υ₁ υ₂} (el𝒰 : Set υ₁) → SetoidOn υ₂ el𝒰 → Set (υ₁ ⊔ υ₂ ⊔ lsuc lzero)
QSet el𝒰 𝒰 = el𝒰 > 𝒰 ⇒ Set-setoid {lzero}

-- [todo] e.g. {3,8,5,2} is a set

-- If x is an object, we say that x is an element of A or x ∈ A if x
-- lies in the collection
_∈_ : ∀ {υ₁ υ₂} {𝒰 : Setoid υ₁ υ₂} → el 𝒰 → PSet 𝒰 → Set
x ∈ P = ap P x

_∈*_ : ∀ {υ₁ υ₂} {elᵁ : Set υ₁} {𝒰 : SetoidOn υ₂ elᵁ} → elᵁ → QSet elᵁ 𝒰 → Set
x ∈* Q = app Q x

-- Otherwise we say that x ∉ A
_∉_ : ∀ {υ₁ υ₂} {𝒰 : Setoid υ₁ υ₂} → el 𝒰 → PSet 𝒰 → Set
x ∉ P = ¬ (x ∈ P)

_∉*_ : ∀ {υ₁ υ₂} {elᵁ : Set υ₁} {𝒰 : SetoidOn υ₂ elᵁ} → elᵁ → QSet elᵁ 𝒰 → Set
x ∉* Q = ¬ (x ∈* Q)

infix 9 _∈_ _∈*_ _∉_ _∉*_

-- [todo] For instance, 3 ∈ {1,2,3,4,5} but 7 ∉ {1,2,3,4,5}

-- Axiom 3.1 (Sets are objects). If A is a set, then A is also an
-- object. In particular, given two sets A and B, it is meaningful to
-- ask whether A is also an element of B.
set-in-set? :
  ∀ {υ₁ υ₂ α₂} {el𝒰 : Set υ₁} {𝒰 : SetoidOn υ₂ el𝒰}
    (el𝒜 : QSet el𝒰 𝒰) {𝒜 : SetoidOn α₂ (QSet el𝒰 𝒰)} →
  QSet (QSet el𝒰 𝒰) 𝒜 → Set
set-in-set? A B = A ∈* B

-- [todo] The set {3, {3,4}, 4} is a set of three distinct elements,
-- one of which happens to itself be a set of two elements.

PSetoid : ∀ {α} → Set α → Set (lsuc (lsuc lzero) ⊔ lsuc α)
PSetoid {α} A = SetoidOn α (A → Set)

module _ {υ₁ υ₂} {el𝒰 : Set υ₁} {𝒰 : SetoidOn υ₂ el𝒰} where
  QSet-setoid : SetoidOn (υ₁ ⊔ lzero) (el𝒰 > 𝒰 ⇒ Set-setoid {lzero})
  QSet-setoid = >⇒-setoid 𝒰 (Set-setoid {lzero})

  open SetoidOn QSet-setoid using (isEquivRel) renaming (_≗_ to _≗ᵁ_)
  open IsEquivRel isEquivRel
    renaming (refl to qset-refl; sym to qset-sym; trans to qset-trans)

  -- Definition 3.1.4 (Equality of sets). Two sets A and B are _equal_,
  -- A = B, iff every element of A is an element of B and vice versa.
  _≅_ : QSet el𝒰 𝒰 → QSet el𝒰 𝒰 → Set υ₁
  A ≅ B = A ≗ᵁ B

  -- Example 3.1.5
  -- [todo] {1,2,3,4,5} and {3,4,2,1,5} are the same set
  -- [todo] {3,3,1,5,2,4,2} is equal to {1,2,3,4,5}

  -- Exercise 3.1.1
  -- Reflexivity, symmetry, and transitivity of equality
  ≅-refl : {A : QSet el𝒰 𝒰} → A ≅ A
  ≅-refl {A} = qset-refl {A}

  ≅-sym : {A B : QSet el𝒰 𝒰} → A ≅ B → B ≅ A
  ≅-sym {A} {B} A≅B = qset-sym {A} {B} A≅B

  ≅-trans : {A B C : QSet el𝒰 𝒰} → A ≅ B → B ≅ C → A ≅ C
  ≅-trans {A} {B} {C} A≅B B≅C = qset-trans {A} {B} {C} A≅B B≅C

  -- Substitution property of equality
  ∈*-subst : {A B : QSet el𝒰 𝒰} {x : el𝒰} → A ≅ B → x ∈* A → x ∈* B
  ∈*-subst {x = x} A≅B x∈A = ∧-elimᴸ (A≅B x) x∈A

  subst-∈* :
    {A B : QSet el𝒰 𝒰} {U : QSet (QSet el𝒰 𝒰) QSet-setoid} →
      A ≅ B → A ∈* U → B ∈* U
  subst-∈* {U = U} A≅B A∈U = ∧-elimᴸ (congg U A≅B) A∈U

  -- Axiom 3.2 (Empty set). There exists a set ∅, known as the _empty
  -- set_, which contains no elements, i.e., for every object x we
  -- have x ∉ ∅.
  ∅ : QSet el𝒰 𝒰
  ∅ = record { app = const ⊥ ; congg = λ _ → ∧-intro id id }

  is-empty : QSet el𝒰 𝒰 → Set υ₁
  is-empty S = {x : el𝒰} → x ∉* S

  x∉∅ : is-empty ∅
  x∉∅ = id

  -- Note that there can only be one empty set
  ∅-unique : {∅′ : QSet el𝒰 𝒰} → is-empty ∅′ → ∅ ≅ ∅′
  ∅-unique x∉*∅′ x = ∧-intro ⊥-elim x∉*∅′

{-

  -- Lemma 3.1.6 (Single choice)
  -- This is not provable in Agda because it's nonconstructive.
  -- Instead of using evidence that a set is not equal to the empty set,
  -- we will need to use direct evidence that an element of a set exists.

  -- Axiom 3.3 (Singleton sets and pair sets)
  singleton : 𝒰 → PSet 𝒰
  singleton x y = y ≡ x

  pair : 𝒰 → 𝒰 → PSet 𝒰
  pair x y z = z ≡ x ∨ z ≡ y

  -- Remarks 3.1.9
  singleton-unique :
    ∀ {S S′ a} → S ≗ singleton a → S′ ≗ singleton a → S ≗ S′
  singleton-unique = ≗-same

  pair-unique : ∀ {P P′ a b} → P ≗ pair a b → P′ ≗ pair a b → P ≗ P′
  pair-unique = ≗-same

  pair-comm : ∀ {a b} → pair a b ≗ pair b a
  pair-comm = mk≗ λ {_} → ∧-intro ∨-comm ∨-comm

  pair-singleton : ∀ {a} → pair a a ≗ singleton a
  pair-singleton = mk≗ λ {_} → ∧-intro ∨-merge ∨-introᴸ
-}
