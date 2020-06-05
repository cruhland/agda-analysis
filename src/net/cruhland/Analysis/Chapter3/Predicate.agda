open import Function using (const; id; _∘_)
open import Level
  using (Level; _⊔_; Lift; lift; lower)
  renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import net.cruhland.axiomatic.Logic using (LogicBundle)

module net.cruhland.Analysis.Chapter3.Predicate (LB : LogicBundle) where

open LogicBundle LB

{-= Chapter 3: Set theory (type theory predicate approach) =-}

{- 3.1 Fundamentals -}

-- [note] We need some preliminary definitions that aren't in the
-- book, in order to define set theory concepts inside type theory.
-- These are taken from the paper "Setoids in type theory" by Gilles
-- Barthe, Venanzio Capretta, and Olivier Pons.

-- Binary relations
Rel₂ : ∀ {α} → Set α → ∀ β → Set (α ⊔ lsuc β)
Rel₂ A β = A → A → Set β

-- Equivalence relations (generally following agda-stdlib)
record IsEquivalence {β α} {A : Set α} (_≅_ : Rel₂ A β) : Set (α ⊔ β) where
  field
    refl : ∀ {x} → x ≅ x
    sym : ∀ {x y} → x ≅ y → y ≅ x
    trans : ∀ {x y z} → x ≅ y → y ≅ z → x ≅ z

↔-IsEquivalence : ∀ β → IsEquivalence {β} _↔_
↔-IsEquivalence β = record { refl = ↔-refl ; sym = ↔-sym ; trans = ↔-trans }

-- Setoids (generally following agda-stdlib)
record Setoid α β : Set (lsuc (α ⊔ β)) where
  infix 4 _≗_
  field
    El : Set α
    _≗_ : Rel₂ El β
    isEquivalence : IsEquivalence _≗_

  open IsEquivalence isEquivalence public

open Setoid using (El)

↔-Setoid : ∀ α → Setoid (lsuc α) α
↔-Setoid α =
  record { El = Set α ; _≗_ = _↔_ ; isEquivalence = ↔-IsEquivalence α }

-- Map between setoids (some syntax taken from agda-stdlib)
record _⇒_
  {α₁ α₂ β₁ β₂} (A : Setoid α₁ α₂) (B : Setoid β₁ β₂)
    : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂) where
  open Setoid A renaming (_≗_ to _≗ᴬ_)
  open Setoid B renaming (_≗_ to _≗ᴮ_)

  field
    ap : El A → El B
    cong : ∀ {x y} → x ≗ᴬ y → ap x ≗ᴮ ap y

  infixl 5 _⟨$⟩_
  _⟨$⟩_ = ap

open _⇒_ using (_⟨$⟩_; cong)

-- Extensionality setoid (equality of equality-preserving functions)
ext-Setoid :
  ∀ {α₁ α₂ β₁ β₂} →
    Setoid α₁ α₂ → Setoid β₁ β₂ → Setoid (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂) (α₁ ⊔ β₂)
ext-Setoid A B =
  record { El = A ⇒ B ; _≗_ = ext ; isEquivalence = ext-IsEquivalence }
    where
      open module B = Setoid B renaming (_≗_ to _≗ᴮ_)

      ext = λ f g → ∀ x → f ⟨$⟩ x ≗ᴮ g ⟨$⟩ x

      ext-IsEquivalence = record
        { refl = λ {f} x → B.refl
        ; sym = λ {f g} x→fx≗gx x → B.sym (x→fx≗gx x)
        ; trans = λ {f g h} x→fx≗gx x→gx≗hx x → B.trans (x→fx≗gx x) (x→gx≗hx x)
        }

-- [note] End preliminary definitions, back to the book

private
  variable
    υ₁ υ₂ υ : Level
    U : Setoid υ₁ υ₂

-- Definition 3.1.1
-- We define a set A to be any unordered collection of objects.
-- [note] A set is defined as an (equality-preserving) predicate over
-- an underlying "universe" setoid.
PSet : Setoid υ₁ υ₂ → ∀ υ → Set (υ₁ ⊔ υ₂ ⊔ lsuc υ)
PSet U υ = U ⇒ (↔-Setoid υ)

-- [todo] e.g. {3,8,5,2} is a set

-- If x is an object, we say that x is an element of A or x ∈ A if x
-- lies in the collection
_∈_ : El U → PSet U υ → Set υ
x ∈ A = A ⟨$⟩ x

-- Otherwise we say that x ∉ A
_∉_ : El U → PSet U υ → Set υ
x ∉ A = ¬ (x ∈ A)

infix 9 _∈_ _∉_

-- [todo] For instance, 3 ∈ {1,2,3,4,5} but 7 ∉ {1,2,3,4,5}

⇒-Setoid : Setoid υ₁ υ₂ → ∀ υ → Setoid (υ₁ ⊔ υ₂ ⊔ lsuc υ) (υ₁ ⊔ υ)
⇒-Setoid U υ = ext-Setoid U (↔-Setoid υ)

PSetoid :
  ∀ {υ₁ υ₂ υ} {U : Setoid υ₁ υ₂} →
    PSet U υ → Setoid (υ₁ ⊔ υ₂ ⊔ lsuc υ) (υ₁ ⊔ υ)
PSetoid {υ = υ} {U} _ = ⇒-Setoid U υ

-- Axiom 3.1 (Sets are objects). If A is a set, then A is also an
-- object. In particular, given two sets A and B, it is meaningful to
-- ask whether A is also an element of B.
set-in-set? : ∀ {β} → PSet U υ → PSet (⇒-Setoid U υ) β → Set _
set-in-set? A B = A ∈ B

-- [todo] The set {3, {3,4}, 4} is a set of three distinct elements,
-- one of which happens to itself be a set of two elements.

-- Definition 3.1.4 (Equality of sets). Two sets A and B are _equal_,
-- A = B, iff every element of A is an element of B and vice versa.
_≅_ : PSet U υ → PSet U υ → Set _
A ≅ B = A ≗ B
  where open Setoid (PSetoid A) using (_≗_)

_≇_ : PSet U υ → PSet U υ → Set _
A ≇ B = ¬ (A ≅ B)

-- Example 3.1.5
-- [todo] {1,2,3,4,5} and {3,4,2,1,5} are the same set
-- [todo] {3,3,1,5,2,4,2} is equal to {1,2,3,4,5}

-- Exercise 3.1.1
-- Reflexivity, symmetry, and transitivity of equality
≅-refl : {A : PSet U υ} → A ≅ A
≅-refl {A = A} = A.refl {A}
  where module A = Setoid (PSetoid A)

≅-sym : {A B : PSet U υ} → A ≅ B → B ≅ A
≅-sym {A = A} {B} A≅B = A.sym {A} {B} A≅B
  where module A = Setoid (PSetoid A)

≅-trans : {A B C : PSet U υ} → A ≅ B → B ≅ C → A ≅ C
≅-trans {A = A} {B} {C} A≅B B≅C = A.trans {A} {B} {C} A≅B B≅C
  where module A = Setoid (PSetoid A)

-- Substitution property of equality
∈-subst :
  {U : Setoid υ₁ υ₂} {A B : PSet U υ} {x : El U} → A ≅ B → x ∈ A → x ∈ B
∈-subst {x = x} A≅B x∈A = ∧-elimᴸ (A≅B x) x∈A

subst-∈ :
  ∀ {χ} {A B : PSet U υ} {C : PSet (PSetoid A) χ} → A ≅ B → A ∈ C → B ∈ C
subst-∈ {C = C} A≅B A∈C = ∧-elimᴸ (cong C A≅B) A∈C

-- Axiom 3.2 (Empty set). There exists a set ∅, known as the _empty
-- set_, which contains no elements, i.e., for every object x we
-- have x ∉ ∅.
∅ : ∀ {υ} → PSet U υ
∅ {υ = υ} = record { ap = const (Lift υ ⊥) ; cong = λ _ → ∧-intro id id }

is-empty : PSet U υ → Set _
is-empty {U = U} S = (x : El U) → x ∉ S

x∉∅ : ∀ {υ} → is-empty (∅ {U = U} {υ = υ})
x∉∅ x = lower

-- Note that there can only be one empty set; if there were two sets
-- ∅ and ∅′ which were both empty, then by Definition 3.1.4 they
-- would be equal to each other.
∅-unique : {U : Setoid υ₁ υ₂} {∅′ : PSet U υ} → is-empty ∅′ → ∅ ≅ ∅′
∅-unique {υ = υ} {U = U} x∉∅′ x =
  ∧-intro (⊥-elim ∘ (x∉∅ {U = U} x)) (lift ∘ (x∉∅′ x))

-- Lemma 3.1.6 (Single choice)
-- This is not provable in Agda because it's nonconstructive.  Instead
-- of using evidence that a set is not equal to the empty set, we will
-- need to use direct evidence that an element of a set exists.

-- Axiom 3.3 (Singleton sets and pair sets)
singleton : ∀ {υ₁ υ₂} {U : Setoid υ₁ υ₂} → El U → PSet U υ₂
singleton {υ₂ = υ₂} {U} a = record { ap = in-set ; cong = singleton-cong }
  where
    open module U = Setoid U using () renaming (_≗_ to _≗ᵁ_)

    in-set = _≗ᵁ a

    singleton-cong : {x y : El U} → x ≗ᵁ y → in-set x ↔ in-set y
    singleton-cong x≗y =
      ∧-intro (λ x≗a → U.trans (U.sym x≗y) x≗a) (λ y≗a → U.trans x≗y y≗a)

is-singleton : PSet U υ → El U → Set _
is-singleton {U = U} S a = ∀ {x} → x ∈ S ↔ x ≗ᵁ a
  where open Setoid U using () renaming (_≗_ to _≗ᵁ_)

a∈sa : {U : Setoid υ₁ υ₂} → (a : El U) → a ∈ singleton {U = U} a
a∈sa {U = U} a = U.refl
  where module U = Setoid U

singleton-unique :
  {U : Setoid υ₁ υ₂} {S : PSet U υ₂} {a : El U} →
    is-singleton S a → S ≅ singleton a
singleton-unique is-S x = is-S

pair : El U → El U → PSet U _
pair {U = U} a b = record { ap = in-set ; cong = pair-cong }
  where
    open module U = Setoid U using () renaming (_≗_ to _≗ᵁ_)

    in-set = λ x → x ≗ᵁ a ∨ x ≗ᵁ b

    pair-eq : {x y : El U} → x ≗ᵁ y → in-set x → in-set y
    pair-eq x≗y x≗a∨b = ∨-rec use-x≗a use-x≗b x≗a∨b
      where
        use-x≗a = λ x≗a → ∨-introᴸ (U.trans (U.sym x≗y) x≗a)
        use-x≗b = λ x≗b → ∨-introᴿ (U.trans (U.sym x≗y) x≗b)

    pair-cong : {x y : El U} → x ≗ᵁ y → in-set x ↔ in-set y
    pair-cong x≗y = ∧-intro (pair-eq x≗y) (pair-eq (U.sym x≗y))

is-pair : PSet U υ → El U → El U → Set _
is-pair {U = U} S a b = ∀ {x} → x ∈ S ↔ x ≗ᵁ a ∨ x ≗ᵁ b
  where open Setoid U using () renaming (_≗_ to _≗ᵁ_)

a∈pab : {U : Setoid υ₁ υ₂} {a b : El U} → a ∈ pair {U = U} a b
a∈pab {U = U} = ∨-introᴸ U.refl
  where module U = Setoid U

b∈pab : {U : Setoid υ₁ υ₂} {a b : El U} → b ∈ pair {U = U} a b
b∈pab {U = U} = ∨-introᴿ U.refl
  where module U = Setoid U

pair-unique :
  {U : Setoid υ₁ υ₂} {S : PSet U υ₂} {a b : El U} →
    is-pair S a b → S ≅ pair a b
pair-unique is-pair x = is-pair

pair-comm : {U : Setoid υ₁ υ₂} {a b : El U} → pair {U = U} a b ≅ pair b a
pair-comm x = ∧-intro ∨-comm ∨-comm

pair-singleton : {U : Setoid υ₁ υ₂} {a : El U} → pair {U = U} a a ≅ singleton a
pair-singleton x = ∧-intro ∨-merge ∨-introᴸ

-- Examples 3.1.10
-- Exercise 3.1.2
∅≇sa : {U : Setoid υ₁ υ₂} → (a : El U) → ∅ {U = U} ≇ singleton a
∅≇sa {U = U} a ∅≅sa = lower (a≗a→⊥ U.refl)
  where
    module U = Setoid U
    a≗a→⊥ = ∧-elimᴿ (∅≅sa a)

∅≇s∅ : ∀ {υ} → ∅ {U = ⇒-Setoid U υ} ≇ singleton ∅
∅≇s∅ {U = U} {υ = υ} = ∅≇sa {U = ⇒-Setoid U υ} ∅

singleton-inj :
  {U : Setoid υ₁ υ₂} → let open Setoid U using (_≗_) in
    (a b : El U) → singleton {U = U} a ≅ singleton b → a ≗ b
singleton-inj {U = U} a b sa≅sb = ∧-elimᴸ (sa≅sb a) U.refl
  where open module U = Setoid U using (_≗_)

s∅≇ss∅ :
  ∀ {υ} → singleton {U = ⇒-Setoid (⇒-Setoid U υ) _} ∅ ≇ singleton (singleton ∅)
s∅≇ss∅ {U = U} {υ = υ} s∅≅ss∅ = ∅≇s∅ ∅≅s∅
  where
    V = ⇒-Setoid (⇒-Setoid U υ) _
    ∅≅s∅ = singleton-inj {U = V} ∅ (singleton ∅) s∅≅ss∅

s∅≇p∅s∅ :
  ∀ {υ} → singleton {U = ⇒-Setoid (⇒-Setoid U υ) _} ∅ ≇ pair ∅ (singleton ∅)
s∅≇p∅s∅ {U = U} {υ = υ} s∅≅p∅s∅ = ∅≇s∅ ∅≅s∅
  where
    V = ⇒-Setoid (⇒-Setoid U υ) _
    s∅∈p∅s∅→s∅∈s∅ = ∧-elimᴿ (s∅≅p∅s∅ (singleton ∅))
    s∅≅∅ = s∅∈p∅s∅→s∅∈s∅ (b∈pab {U = V} {a = ∅} {b = singleton ∅})
    ∅≅s∅ = ≅-sym {U = ⇒-Setoid U υ} {A = singleton ∅} {B = ∅} s∅≅∅

ss∅≇p∅s∅ :
  ∀ {υ} → let V = ⇒-Setoid (⇒-Setoid U υ) _ in
    singleton {U = V} (singleton ∅) ≇ pair ∅ (singleton ∅)
ss∅≇p∅s∅ {U = U} {υ = υ} ss∅≅p∅s∅ = ∅≇s∅ ∅≅s∅
  where
    V = ⇒-Setoid (⇒-Setoid U υ) _
    ∅∈p∅s∅→∅∈ss∅ = ∧-elimᴿ (ss∅≅p∅s∅ ∅)
    ∅≅s∅ = ∅∈p∅s∅→∅∈ss∅ (a∈pab {U = V} {a = ∅} {b = singleton ∅})
