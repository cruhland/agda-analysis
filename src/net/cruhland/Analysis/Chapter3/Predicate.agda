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

{-
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

SP : ∀ {α₁ α₂ β} → Setoid α₁ α₂ → Set (α₁ ⊔ α₂ ⊔ lsuc β)
SP {β = β} A = A ⇒ Set-setoid {β}

SubSetoid : ∀ {α₁ α₂ β} (A : Setoid α₁ α₂) → SP {β = β} A → Setoid (α₁ ⊔ β) α₂
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
PSet : ∀ {υ₁ υ₂ β} → Setoid υ₁ υ₂ → Set (υ₁ ⊔ υ₂ ⊔ lsuc β)
PSet {β = β} 𝒰 = SP {β = β} 𝒰

QSet : ∀ {υ₁ υ₂ β} (el𝒰 : Set υ₁) → SetoidOn υ₂ el𝒰 → Set (υ₁ ⊔ υ₂ ⊔ lsuc β)
QSet {β = β} el𝒰 𝒰 = el𝒰 > 𝒰 ⇒ Set-setoid {β}

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
  ∀ {υ₁ υ₂ α₂ β} {el𝒰 : Set υ₁} {𝒰 : SetoidOn υ₂ el𝒰}
    (el𝒜 : QSet {β = β} el𝒰 𝒰) {𝒜 : SetoidOn α₂ (QSet el𝒰 𝒰)} →
  QSet (QSet el𝒰 𝒰) 𝒜 → Set
set-in-set? A B = A ∈* B

-- [todo] The set {3, {3,4}, 4} is a set of three distinct elements,
-- one of which happens to itself be a set of two elements.

PSetoid : ∀ {α} → Set α → Set (lsuc (lsuc lzero) ⊔ lsuc α)
PSetoid {α} A = SetoidOn α (A → Set)

module _ {υ₁ υ₂} {el𝒰 : Set υ₁} {𝒰 : SetoidOn υ₂ el𝒰} where
  QSet-setoid : ∀ {β} → SetoidOn (υ₁ ⊔ β) (QSet {β = β} el𝒰 𝒰)
  QSet-setoid = >⇒-setoid 𝒰 Set-setoid

  open SetoidOn 𝒰 renaming (_≗_ to _≗ᵁ_; isEquivRel to eqvRelᵁ)
  open IsEquivRel eqvRelᵁ
    renaming (refl to reflᵁ; sym to symᵁ; trans to transᵁ)

  -- Definition 3.1.4 (Equality of sets). Two sets A and B are _equal_,
  -- A = B, iff every element of A is an element of B and vice versa.
  _≅_ : ∀ {β} → QSet {β = β} el𝒰 𝒰 → QSet {β = β} el𝒰 𝒰 → Set (υ₁ ⊔ β)
  _≅_ {β} A B = A ≗ˢ B
    where
      open SetoidOn (QSet-setoid {β}) renaming (_≗_ to _≗ˢ_)
      open IsEquivRel isEquivRel
        renaming (refl to reflˢ; sym to symˢ; trans to transˢ)

  _≇_ : ∀ {β χ} → QSet {β = β} el𝒰 𝒰 → QSet {β = β} el𝒰 𝒰 → Set (υ₁ ⊔ β ⊔ χ)
  _≇_ {β} {χ} A B = ¬_ {β = χ} (A ≅ B)

  -- Example 3.1.5
  -- [todo] {1,2,3,4,5} and {3,4,2,1,5} are the same set
  -- [todo] {3,3,1,5,2,4,2} is equal to {1,2,3,4,5}

  -- Exercise 3.1.1
  -- Reflexivity, symmetry, and transitivity of equality
  ≅-refl : ∀ {β} {A : QSet el𝒰 𝒰} → A ≅ A
  ≅-refl {β} {A} = reflˢ {A}
    where
      open SetoidOn (QSet-setoid {β}) using (isEquivRel)
      open IsEquivRel isEquivRel renaming (refl to reflˢ)

  ≅-sym : ∀ {β} {A B : QSet el𝒰 𝒰} → A ≅ B → B ≅ A
  ≅-sym {β} {A} {B} A≅B = symˢ {A} {B} A≅B
    where
      open SetoidOn (QSet-setoid {β}) using (isEquivRel)
      open IsEquivRel isEquivRel renaming (sym to symˢ)

  ≅-trans : ∀ {β} {A B C : QSet el𝒰 𝒰} → A ≅ B → B ≅ C → A ≅ C
  ≅-trans {β} {A} {B} {C} A≅B B≅C = transˢ {A} {B} {C} A≅B B≅C
    where
      open SetoidOn (QSet-setoid {β}) using (isEquivRel)
      open IsEquivRel isEquivRel renaming (trans to transˢ)

  ≅-same : ∀ {β} {A B C : QSet {β = β} el𝒰 𝒰} → A ≅ C → B ≅ C → A ≅ B
  ≅-same {β} {A} {B} {C} A≅C B≅C =
    ≅-trans {β} {A} {C} {B} A≅C (≅-sym {β} {B} {C} B≅C)

  -- Substitution property of equality
  ∈*-subst : {A B : QSet el𝒰 𝒰} {x : el𝒰} → A ≅ B → x ∈* A → x ∈* B
  ∈*-subst {x = x} A≅B x∈A = ∧-elimᴸ (A≅B x) x∈A

  subst-∈* :
    ∀ {β} {A B : QSet {β = β} el𝒰 𝒰} {U : QSet (QSet el𝒰 𝒰) QSet-setoid} →
      A ≅ B → A ∈* U → B ∈* U
  subst-∈* {U = U} A≅B A∈U = ∧-elimᴸ (congg U A≅B) A∈U

  -- Axiom 3.2 (Empty set). There exists a set ∅, known as the _empty
  -- set_, which contains no elements, i.e., for every object x we
  -- have x ∉ ∅.
  ∅ : ∀ {β} → QSet {β = β} el𝒰 𝒰
  ∅ = record { app = const ⊥ ; congg = λ _ → ∧-intro id id }

  is-empty : QSet el𝒰 𝒰 → Set υ₁
  is-empty S = {x : el𝒰} → x ∉* S

  x∉∅ : is-empty ∅
  x∉∅ = id

  -- Note that there can only be one empty set; if there were two sets
  -- ∅ and ∅′ which were both empty, then by Definition 3.1.4 they
  -- would be equal to each other.
  ∅-unique : {∅′ : QSet el𝒰 𝒰} → is-empty ∅′ → ∅ ≅ ∅′
  ∅-unique x∉*∅′ x = ∧-intro ⊥-elim x∉*∅′

  -- Lemma 3.1.6 (Single choice)
  -- This is not provable in Agda because it's nonconstructive.
  -- Instead of using evidence that a set is not equal to the empty set,
  -- we will need to use direct evidence that an element of a set exists.

  -- Axiom 3.3 (Singleton sets and pair sets)
  singleton : ∀ {β} → el𝒰 → QSet {β = β} el𝒰 𝒰
  -- TODO: Need to pull all of these definitions out of the module so they
  -- can be properly parameterized! :(
  -- Maybe we can go back to using Setoid instead of SetoidOn, and passing
  -- equality proofs around? Might be easier than parameters...
  -- The definitions in agda-stdlib make a lot more sense now.
  -- You should model your setoids after theirs.
  singleton {β} a = record { app = _≗ᵁ a ; congg = singleton-congg }
    where
      singleton-congg : {x y : el𝒰} → x ≗ᵁ y → x ≗ᵁ a ↔ y ≗ᵁ a
      singleton-congg x≗y =
        ∧-intro (λ x≗a → transᵁ (symᵁ x≗y) x≗a) (λ y≗a → transᵁ x≗y y≗a)

  pair : el𝒰 → el𝒰 → QSet el𝒰 𝒰
  pair a b = record { app = λ y → y ≗ᵁ a ∨ y ≗ᵁ b ; congg = pair-congg }
    where
      pair-eq : {x y : el𝒰} → x ≗ᵁ y → x ≗ᵁ a ∨ x ≗ᵁ b → y ≗ᵁ a ∨ y ≗ᵁ b
      pair-eq x≗y x≗a∨b = ∨-rec use-x≗a use-x≗b x≗a∨b
        where
          use-x≗a = λ x≗a → ∨-introᴸ (transᵁ (symᵁ x≗y) x≗a)
          use-x≗b = λ x≗b → ∨-introᴿ (transᵁ (symᵁ x≗y) x≗b)

      pair-congg : {x y : el𝒰} → x ≗ᵁ y → x ≗ᵁ a ∨ x ≗ᵁ b ↔ y ≗ᵁ a ∨ y ≗ᵁ b
      pair-congg x≗y = ∧-intro (pair-eq x≗y) (pair-eq (symᵁ x≗y))

  -- Remarks 3.1.9
  singleton-unique :
    ∀ {S S′ a} → S ≅ singleton a → S′ ≅ singleton a → S ≅ S′
  singleton-unique {S} {S′} {a} = ≅-same {A = S} {B = S′} {C = singleton a}

  pair-unique : ∀ {P P′ a b} → P ≅ pair a b → P′ ≅ pair a b → P ≅ P′
  pair-unique {P} {P′} {a} {b} = ≅-same {A = P} {B = P′} {C = pair a b}

  pair-comm : ∀ {a b} → pair a b ≅ pair b a
  pair-comm x = ∧-intro ∨-comm ∨-comm

  pair-singleton : ∀ {a} → pair a a ≅ singleton a
  pair-singleton x = ∧-intro ∨-merge ∨-introᴸ


a∈sa :
  ∀ {υ₁ υ₂} {el𝒰 : Set υ₁} {𝒰 : SetoidOn υ₂ el𝒰} {a : el𝒰} →
  _∈*_ {υ₁} {υ₂} {el𝒰} {𝒰} a (singleton {υ₁} {υ₂} {el𝒰} {𝒰} a)
a∈sa = {!!}

-- Examples 3.1.10
-- Exercise 3.1.2
∅₁ : ∀ {υ₁ υ₂} {el𝒰 : Set υ₁} {𝒰 : SetoidOn υ₂ el𝒰} → QSet {β = lzero} el𝒰 𝒰
∅₁ = ∅

s₁ :
  ∀ {υ₁ υ₂} {el𝒰 : Set υ₁} {𝒰 : SetoidOn υ₂ el𝒰} →
  QSet {β = υ₁} (QSet {β = lzero} el𝒰 𝒰) (QSet-setoid {β = lzero})
s₁ = singleton ∅₁

∅₂ :
  ∀ {υ₁ υ₂} {el𝒰 : Set υ₁} {𝒰 : SetoidOn υ₂ el𝒰} →
  QSet {β = υ₁} (QSet {β = lzero} el𝒰 𝒰) (QSet-setoid {β = lzero})
∅₂ = ∅

  -- ∀ {υ₁ υ₂} {el𝒰 : Set υ₁} {𝒰 : SetoidOn υ₂ el𝒰} →
  -- QSet (QSet {β = lzero} el𝒰 𝒰) (QSet-setoid {β = lzero})
∅≇s∅ :
  ∀ {υ₁ υ₂} {el𝒰 : Set υ₁} {𝒰 : SetoidOn υ₂ el𝒰} →
  _≇_ {el𝒰 = QSet {β = lzero} el𝒰 𝒰} {𝒰 = QSet-setoid {β = lzero}} {β = υ₁} {χ = lzero} ∅₂ s₁
∅≇s∅ {υ₁} {el𝒰 = el𝒰} {𝒰 = 𝒰} ∅≅s∅ = x∉∅ {el𝒰 = QSet {β = lzero} el𝒰 𝒰} {𝒰 = QSet-setoid {β = lzero}} {x = ∅₁} {!!} -- (∧-elimᴿ (x∈∅↔x∈s∅ ?) ?)
  where
    x∈∅↔x∈s∅ = ∅≅s∅
    ∅∈s∅→∅∈∅ = ∧-elimᴿ (x∈∅↔x∈s∅ ∅₁)
    ∅∈∅ = ∅∈s∅→∅∈∅ {!!}

-}
