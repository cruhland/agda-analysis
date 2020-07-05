open import Agda.Builtin.FromNat using (Number)
open import Function using (const; id; _∘_; flip)
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_)
open Eq.≡-Reasoning
open import net.cruhland.axiomatic.Logic using
  ( _∧_; ∧-dup; ∧-elimᴿ; ∧-intro; ∧-map; ∧-mapᴸ; ∧-mapᴿ
  ; _∨_; ∨-assocᴸᴿ; ∨-assocᴿᴸ; ∨-comm; ∨-identᴸ; ∨-identᴿ
  ; ∨-introᴸ; ∨-introᴿ; ∨-map; ∨-mapᴸ; ∨-mapᴿ; ∨-merge; ∨-rec
  ; _↔_; ↔-elimᴸ; ↔-elimᴿ; ↔-intro; ↔-refl; ↔-sym; ↔-trans
  ; ⊤
  ; ⊥-elim; ⊥ᴸᴾ; ⊥ᴸᴾ-elim; ¬_; ¬sym
  ; Σ; Σ-intro; Σ-map-snd; Σ-rec
  )
open import net.cruhland.axiomatic.Peano using (PeanoArithmetic)

module net.cruhland.Analysis.Chapter3.Predicate (PA : PeanoArithmetic) where

open PeanoArithmetic PA using
  ( ℕ; step≢zero; step-inj; number
  ; _+_; +-zeroᴸ; +-stepᴸ⃗ᴿ
  ; _≤_; _<_; n<sn; <-trans
  )

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

≡-IsEquivalence : ∀ {α} {A : Set α} → IsEquivalence {A = A} _≡_
≡-IsEquivalence = record { refl = Eq.refl ; sym = Eq.sym ; trans = Eq.trans }

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

≡-Setoid : ∀ {α} (A : Set α) → Setoid _ _
≡-Setoid A =
  record { El = A ; _≗_ = _≡_ ; isEquivalence = ≡-IsEquivalence }

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

infix 5 _∈_ _∉_

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

infix 4 _≅_ _≇_

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
∈-subst {x = x} A≅B x∈A = ↔-elimᴸ (A≅B x) x∈A

subst-∈ :
  ∀ {χ} {A B : PSet U υ} {C : PSet (PSetoid A) χ} → A ≅ B → A ∈ C → B ∈ C
subst-∈ {C = C} A≅B A∈C = ↔-elimᴸ (cong C A≅B) A∈C

-- Axiom 3.2 (Empty set). There exists a set ∅, known as the _empty
-- set_, which contains no elements, i.e., for every object x we
-- have x ∉ ∅.
∅ : ∀ {υ} → PSet U υ
∅ {υ = υ} = record { ap = const ⊥ᴸᴾ ; cong = λ _ → ↔-refl }

is-empty : PSet U υ → Set _
is-empty {U = U} S = (x : El U) → x ∉ S

x∉∅ : ∀ {υ} → is-empty (∅ {U = U} {υ = υ})
x∉∅ x = ⊥ᴸᴾ-elim

-- Note that there can only be one empty set; if there were two sets
-- ∅ and ∅′ which were both empty, then by Definition 3.1.4 they
-- would be equal to each other.
∅-unique : {U : Setoid υ₁ υ₂} {∅′ : PSet U υ} → is-empty ∅′ → ∅ ≅ ∅′
∅-unique x∉∅′ x = ↔-intro ⊥ᴸᴾ-elim (⊥-elim ∘ x∉∅′ x)

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
      ↔-intro (λ x≗a → U.trans (U.sym x≗y) x≗a) (λ y≗a → U.trans x≗y y≗a)

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
    pair-eq x≗y (∨-introᴸ x≗a) = ∨-introᴸ (U.trans (U.sym x≗y) x≗a)
    pair-eq x≗y (∨-introᴿ x≗b) = ∨-introᴿ (U.trans (U.sym x≗y) x≗b)

    pair-cong : {x y : El U} → x ≗ᵁ y → in-set x ↔ in-set y
    pair-cong x≗y = ↔-intro (pair-eq x≗y) (pair-eq (U.sym x≗y))

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
pair-comm x = ↔-intro ∨-comm ∨-comm

pair-singleton : {U : Setoid υ₁ υ₂} {a : El U} → pair {U = U} a a ≅ singleton a
pair-singleton x = ↔-intro ∨-merge ∨-introᴸ

-- Examples 3.1.10
-- Exercise 3.1.2
∅≇sa : {U : Setoid υ₁ υ₂} → (a : El U) → ∅ {U = U} ≇ singleton a
∅≇sa {U = U} a ∅≅sa = ⊥ᴸᴾ-elim (a≗a→⊥ U.refl)
  where
    module U = Setoid U
    a≗a→⊥ = ↔-elimᴿ (∅≅sa a)

∅≇s∅ : ∀ {υ} → ∅ {U = ⇒-Setoid U υ} ≇ singleton ∅
∅≇s∅ {U = U} {υ = υ} = ∅≇sa {U = ⇒-Setoid U υ} ∅

singleton-inj :
  {U : Setoid υ₁ υ₂} → let open Setoid U using (_≗_) in
    (a b : El U) → singleton {U = U} a ≅ singleton b → a ≗ b
singleton-inj {U = U} a b sa≅sb = ↔-elimᴸ (sa≅sb a) U.refl
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
    s∅∈p∅s∅→s∅∈s∅ = ↔-elimᴿ (s∅≅p∅s∅ (singleton ∅))
    s∅≅∅ = s∅∈p∅s∅→s∅∈s∅ (b∈pab {U = V} {a = ∅} {b = singleton ∅})
    ∅≅s∅ = ≅-sym {U = ⇒-Setoid U υ} {A = singleton ∅} {B = ∅} s∅≅∅

ss∅≇p∅s∅ :
  ∀ {υ} → let V = ⇒-Setoid (⇒-Setoid U υ) _ in
    singleton {U = V} (singleton ∅) ≇ pair ∅ (singleton ∅)
ss∅≇p∅s∅ {U = U} {υ = υ} ss∅≅p∅s∅ = ∅≇s∅ ∅≅s∅
  where
    V = ⇒-Setoid (⇒-Setoid U υ) _
    ∅∈p∅s∅→∅∈ss∅ = ↔-elimᴿ (ss∅≅p∅s∅ ∅)
    ∅≅s∅ = ∅∈p∅s∅→∅∈ss∅ (a∈pab {U = V} {a = ∅} {b = singleton ∅})

-- Axiom 3.4 (Pairwise union)
infixl 6 _∪_
_∪_ : ∀ {α β} → PSet U α → PSet U β → PSet U (α ⊔ β)
_∪_ {U = U} A B = record { ap = in-set ; cong = ∪-cong }
  where
    open module U = Setoid U using () renaming (_≗_ to _≗ᵁ_)

    in-set = λ x → x ∈ A ∨ x ∈ B

    ∪-in : {x y : El U} → x ≗ᵁ y → in-set x → in-set y
    ∪-in {x} {y} x≗y x∈A∨B = ∨-map (use-x∈S A) (use-x∈S B) x∈A∨B
      where
        use-x∈S : ∀ {σ} (S : PSet U σ) → x ∈ S → y ∈ S
        use-x∈S S x∈S = ↔-elimᴸ (cong S x≗y) x∈S

    ∪-cong : {x y : El U} → x ≗ᵁ y → in-set x ↔ in-set y
    ∪-cong x≗y = ↔-intro (∪-in x≗y) (∪-in (U.sym x≗y))

-- Example 3.1.11
-- [todo] {1,2} ∪ {2,3} = {1,2,3}

-- Remark 3.1.12
-- Union obeys the axiom of substitution
subst-∪ : ∀ {α β} {A A′ : PSet U α} {B : PSet U β} → A ≅ A′ → A ∪ B ≅ A′ ∪ B
subst-∪ {U = U} {A = A} {A′} {B} A≅A′ x =
  ↔-intro (x∈X∪B→x∈Y∪B A A′ A≅A′) (x∈X∪B→x∈Y∪B A′ A A′≅A)
    where
      A′≅A = ≅-sym {U = U} {A = A} {B = A′} A≅A′
      x∈X∪B→x∈Y∪B = λ X Y X≅Y → ∨-mapᴸ (∈-subst {A = X} {B = Y} X≅Y)

∪-subst : ∀ {α β} {A : PSet U α} {B B′ : PSet U β} → B ≅ B′ → A ∪ B ≅ A ∪ B′
∪-subst {U = U} {A = A} {B} {B′} B≅B′ x =
  ↔-intro (x∈A∪X→x∈A∪Y B B′ B≅B′) (x∈A∪X→x∈A∪Y B′ B B′≅B)
    where
      B′≅B = ≅-sym {U = U} {A = B} {B = B′} B≅B′
      x∈A∪X→x∈A∪Y = λ X Y X≅Y → ∨-mapᴿ (∈-subst {A = X} {B = Y} X≅Y)

-- Lemma 3.1.13
-- Exercise 3.1.3
pab≅sa∪sb :
  {U : Setoid υ₁ υ₂} {a b : El U} →
    pair {U = U} a b ≅ singleton a ∪ singleton b
pab≅sa∪sb x = ↔-refl

∪-comm : {A B : PSet U υ} → A ∪ B ≅ B ∪ A
∪-comm x = ↔-intro ∨-comm ∨-comm

∪-assoc : {A B C : PSet U υ} → (A ∪ B) ∪ C ≅ A ∪ (B ∪ C)
∪-assoc x = ↔-intro ∨-assocᴸᴿ ∨-assocᴿᴸ

∪-idemp : {A : PSet U υ} → A ∪ A ≅ A
∪-idemp x = ↔-intro ∨-merge ∨-introᴸ

-- The consistent level parameter makes the below ∪-ident definitions cleaner
infixl 6 _∪̂_
_∪̂_ : PSet U υ → PSet U υ → PSet U υ
A ∪̂ B = A ∪ B

∪-identᴸ : {A : PSet U υ} → ∅ ∪̂ A ≅ A
∪-identᴸ x = ↔-intro ∨-identᴸ ∨-introᴿ

∪-identᴿ : {U : Setoid υ₁ υ₂} {A : PSet U υ} → A ∪̂ ∅ ≅ A
∪-identᴿ x = ↔-intro ∨-identᴿ ∨-introᴸ

triple : El U → El U → El U → PSet U _
triple a b c = singleton a ∪ singleton b ∪ singleton c

quadruple : El U → El U → El U → El U → PSet U _
quadruple a b c d = pair a b ∪ pair c d

quintuple : El U → El U → El U → El U → El U → PSet U _
quintuple a b c d e = triple a b c ∪ pair d e

-- Axiom 3.7 (Infinity).
-- [note] Doing this a bit early so I can formalize more examples.
ℕ-Setoid : Setoid _ _
ℕ-Setoid = ≡-Setoid ℕ

ℕ-PSet : Set _
ℕ-PSet = PSet ℕ-Setoid lzero

ℕᴾ : ℕ-PSet
ℕᴾ = record { ap = const ⊤ ; cong = const ↔-refl }

-- Definition 3.1.15 (Subsets).
infix 4 _⊆_ _⊈_ _⊊_
_⊆_ : PSet U υ → PSet U υ → Set _
A ⊆ B = ∀ x → x ∈ A → x ∈ B

_⊈_ : PSet U υ → PSet U υ → Set _
A ⊈ B = ¬ (A ⊆ B)

-- [note] Using Σ instead of A ≇ B because the latter doesn't
-- allow constructive proofs
_⊊_ : PSet U υ → PSet U υ → Set _
_⊊_ {U = U} A B = A ⊆ B ∧ Σ (El U) λ x → x ∈ B ∧ x ∉ A

-- Remark 3.1.16
subst-⊆ : {A A′ B : PSet U υ} → A ≅ A′ → A ⊆ B → A′ ⊆ B
subst-⊆ A≅A′ A⊆B x = (A⊆B x) ∘ (↔-elimᴿ (A≅A′ x))

⊆-subst : {A B B′ : PSet U υ} → B ≅ B′ → A ⊆ B → A ⊆ B′
⊆-subst B≅B′ A⊆B x = (↔-elimᴸ (B≅B′ x)) ∘ (A⊆B x)

-- Examples 3.1.17
124⊆12345 : triple {U = ℕ-Setoid} 1 2 4 ⊆ quintuple 1 2 3 4 5
124⊆12345 n (∨-introᴸ (∨-introᴸ n≡1)) = ∨-introᴸ (∨-introᴸ (∨-introᴸ n≡1))
124⊆12345 n (∨-introᴸ (∨-introᴿ n≡2)) = ∨-introᴸ (∨-introᴸ (∨-introᴿ n≡2))
124⊆12345 n (∨-introᴿ n≡4) = ∨-introᴿ (∨-introᴸ n≡4)

124⊊12345 : triple {U = ℕ-Setoid} 1 2 4 ⊊ quintuple 1 2 3 4 5
124⊊12345 = ∧-intro 124⊆12345 (Σ-intro 3 (∧-intro 3∈12345 3∉124))
  where
    3∈12345 = ∨-introᴸ (∨-introᴿ Eq.refl)

    3∉124 : 3 ∉ triple {U = ℕ-Setoid} 1 2 4
    3∉124 (∨-introᴸ (∨-introᴸ 3≡1)) = step≢zero (step-inj 3≡1)
    3∉124 (∨-introᴸ (∨-introᴿ 3≡2)) = step≢zero (step-inj (step-inj 3≡2))
    3∉124 (∨-introᴿ 3≡4) =
      step≢zero (step-inj (step-inj (step-inj (Eq.sym 3≡4))))

A⊆A : {A : PSet U υ} → A ⊆ A
A⊆A x = id

∅⊆A : {A : PSet U υ} → ∅ ⊆ A
∅⊆A x = ⊥ᴸᴾ-elim

-- Proposition 3.1.18 (Sets are partially ordered by set inclusion)
-- Exercise 3.1.4
⊆-trans : {A B C : PSet U υ} → A ⊆ B → B ⊆ C → A ⊆ C
⊆-trans A⊆B B⊆C x = (B⊆C x) ∘ (A⊆B x)

⊆-antisym : {A B : PSet U υ} → A ⊆ B → B ⊆ A → A ≅ B
⊆-antisym A⊆B B⊆A x = ↔-intro (A⊆B x) (B⊆A x)

A≅B→A⊆B : {A B : PSet U υ} → A ≅ B → A ⊆ B
A≅B→A⊆B A≅B = ↔-elimᴸ ∘ A≅B

A≅B→B⊆A : {A B : PSet U υ} → A ≅ B → B ⊆ A
A≅B→B⊆A A≅B = ↔-elimᴿ ∘ A≅B

A⊊B→A⊆B : {A B : PSet U υ} → A ⊊ B → A ⊆ B
A⊊B→A⊆B (∧-intro A⊆B Σx∈B∧x∉A) = A⊆B

A⊊B→B⊈A : {A B : PSet U υ} → A ⊊ B → B ⊈ A
A⊊B→B⊈A (∧-intro A⊆B Σx∈B∧x∉A) B⊆A = Σ-rec use-x∈B∧x∉A Σx∈B∧x∉A
  where
    use-x∈B∧x∉A = λ { x (∧-intro x∈B x∉A) → x∉A (B⊆A x x∈B) }

⊊-trans : {A B C : PSet U υ} → A ⊊ B → B ⊊ C → A ⊊ C
⊊-trans {U = U} {A = A} {B} {C} (∧-intro A⊆B Σx∈B∧x∉A) (∧-intro B⊆C Σx∈C∧x∉B) =
  ∧-intro A⊆C Σx∈C∧x∉A
    where
      A⊆C = ⊆-trans {U = U} {A = A} {B} {C} A⊆B B⊆C

      x∉B→x∉A : ∀ {x} → x ∉ B → x ∉ A
      x∉B→x∉A {x} x∉B x∈A = x∉B (A⊆B x x∈A)

      use-x∈C∧x∉B : ∀ {x} → x ∈ C ∧ x ∉ B → x ∈ C ∧ x ∉ A
      use-x∈C∧x∉B {x} x∈C∧x∉B = ∧-mapᴿ x∉B→x∉A x∈C∧x∉B

      Σx∈C∧x∉A : Σ (El U) λ x → x ∈ C ∧ x ∉ A
      Σx∈C∧x∉A = Σ-map-snd use-x∈C∧x∉B Σx∈C∧x∉B

-- Remark 3.1.20
13⊈24 : pair {U = ℕ-Setoid} 1 3 ⊈ pair 2 4
13⊈24 x∈13→x∈24 with x∈13→x∈24 1 (∨-introᴸ Eq.refl)
... | ∨-introᴸ x≡2 = step≢zero (step-inj (Eq.sym x≡2))
... | ∨-introᴿ x≡4 = step≢zero (step-inj (Eq.sym x≡4))

24⊈13 : pair {U = ℕ-Setoid} 2 4 ⊈ pair 1 3
24⊈13 x∈24→x∈13 with x∈24→x∈13 2 (∨-introᴸ Eq.refl)
... | ∨-introᴸ x≡1 = step≢zero (step-inj x≡1)
... | ∨-introᴿ x≡3 = step≢zero (step-inj (step-inj (Eq.sym x≡3)))

-- Remark 3.1.21
-- Tao provides some examples showing that ∈ is not the same as ⊆.
-- It's harder to get them confused in Agda, because his examples
-- won't even typecheck!

-- Axiom 3.5 (Axiom of specification)
-- [note] because PSet is already a predicate, this definition is
-- really just set intersection.
infixl 8 _⟨_⟩
_⟨_⟩ : ∀ {υ′} → PSet U υ → PSet U υ′ → PSet U (υ ⊔ υ′)
_⟨_⟩ {U = U} A P = record { ap = in-set ; cong = ⟨⟩-cong }
  where
    open module U = Setoid U using () renaming (_≗_ to _≗ᵁ_)

    in-set = λ x → x ∈ A ∧ P ⟨$⟩ x

    ⟨⟩-in : {x y : El U} → x ≗ᵁ y → in-set x → in-set y
    ⟨⟩-in {x} {y} x≗y x∈A∧P = ∧-map (use-x∈S A) (use-x∈S P) x∈A∧P
      where
        use-x∈S : ∀ {σ} (S : PSet U σ) → x ∈ S → y ∈ S
        use-x∈S S x∈S = ↔-elimᴸ (cong S x≗y) x∈S

    ⟨⟩-cong : {x y : El U} → x ≗ᵁ y → in-set x ↔ in-set y
    ⟨⟩-cong x≗y = ↔-intro (⟨⟩-in x≗y) (⟨⟩-in (U.sym x≗y))

x∈A⟨P⟩ :
  ∀ {υ′} {U : Setoid υ₁ υ₂} {A P : PSet U υ} {P : PSet U υ′} {x : El U} →
  x ∈ A ⟨ P ⟩ ↔ x ∈ A ∧ P ⟨$⟩ x
x∈A⟨P⟩ = ↔-refl

A⟨P⟩⊆ : {A P : PSet U υ} → A ⟨ P ⟩ ⊆ A
A⟨P⟩⊆ x (∧-intro x∈A x∈P) = x∈A

A⟨∅⟩≅∅ : ∀ {υ′} {A : PSet U υ} → A ⟨ ∅ {υ = υ′} ⟩ ≅ ∅
A⟨∅⟩≅∅ x = ↔-intro (λ { (∧-intro x∈A x∈∅) → ⊥ᴸᴾ-elim x∈∅}) ⊥ᴸᴾ-elim

A⟨A⟩≅A : {A : PSet U υ} → A ⟨ A ⟩ ≅ A
A⟨A⟩≅A x = ↔-intro (λ { (∧-intro x∈A x∈A′) → x∈A }) ∧-dup

subst-⟨⟩ :
  ∀ {υ′} {A A′ : PSet U υ} {P : PSet U υ′} → A ≅ A′ → A ⟨ P ⟩ ≅ A′ ⟨ P ⟩
subst-⟨⟩ {U = U} {A = A} {A′} {P} A≅A′ x =
  ↔-intro (one-way A A′ A≅A′) (one-way A′ A (≅-sym {A = A} {A′} A≅A′))
    where
      one-way : (S S′ : PSet U υ) → S ≅ S′ → x ∈ S ∧ P ⟨$⟩ x → x ∈ S′ ∧ P ⟨$⟩ x
      one-way S S′ S≅S′ = ∧-mapᴸ (↔-elimᴸ (S≅S′ x))

⟨⟩-subst :
  ∀ {υ′} {A : PSet U υ} {P P′ : PSet U υ′} → P ≅ P′ → A ⟨ P ⟩ ≅ A ⟨ P′ ⟩
⟨⟩-subst {U = U} {υ′ = υ′} {A = A} {P} {P′} P≅P′ x =
  ↔-intro (one-way P P′ P≅P′) (one-way P′ P (≅-sym {A = P} {P′} P≅P′))
    where
      one-way : (Q Q′ : PSet U υ′) → Q ≅ Q′ → x ∈ A ∧ Q ⟨$⟩ x → x ∈ A ∧ Q′ ⟨$⟩ x
      one-way Q Q′ Q≅Q′ = ∧-mapᴿ (↔-elimᴸ (Q≅Q′ x))

-- Example 3.1.22
ℕ-predicate : (P : ℕ → Set) → ℕ-PSet
ℕ-predicate P = record { ap = P ; cong = P-cong }
  where
    P-cong : {x y : ℕ} → x ≡ y → P x ↔ P y
    P-cong x≡y = ↔-intro (Eq.subst P x≡y) (Eq.subst P (Eq.sym x≡y))

module _ where
  S : ℕ-PSet
  S = quintuple 1 2 3 4 5

  0+4≡4 : 0 + 4 ≡ 4
  0+4≡4 = +-zeroᴸ

  1+3≡4 : 1 + 3 ≡ 4
  1+3≡4 = Eq.trans +-stepᴸ⃗ᴿ 0+4≡4

  2+2≡4 : 2 + 2 ≡ 4
  2+2≡4 = Eq.trans +-stepᴸ⃗ᴿ 1+3≡4

  3+1≡4 : 3 + 1 ≡ 4
  3+1≡4 = Eq.trans +-stepᴸ⃗ᴿ 2+2≡4

  0+7≡7 : 0 + 7 ≡ 7
  0+7≡7 = +-zeroᴸ

  1+6≡7 : 1 + 6 ≡ 7
  1+6≡7 = Eq.trans +-stepᴸ⃗ᴿ 0+7≡7

  2+5≡7 : 2 + 5 ≡ 7
  2+5≡7 = Eq.trans +-stepᴸ⃗ᴿ 1+6≡7

  3+4≡7 : 3 + 4 ≡ 7
  3+4≡7 = Eq.trans +-stepᴸ⃗ᴿ 2+5≡7

  4+3≡7 : 4 + 3 ≡ 7
  4+3≡7 = Eq.trans +-stepᴸ⃗ᴿ 3+4≡7

  5+2≡7 : 5 + 2 ≡ 7
  5+2≡7 = Eq.trans +-stepᴸ⃗ᴿ 4+3≡7

  S⟨n<4⟩≅123 : S ⟨ ℕ-predicate (_< 4) ⟩ ≅ triple 1 2 3
  S⟨n<4⟩≅123 x = ↔-intro forward backward
    where
      forward : x ∈ S ⟨ ℕ-predicate (_< 4) ⟩ → x ∈ triple {U = ℕ-Setoid} 1 2 3
      forward (∧-intro x∈S x<4) with x∈S
      ... | ∨-introᴸ x∈123 = x∈123
      ... | ∨-introᴿ (∨-introᴸ x≡4) = ⊥-elim ((∧-elimᴿ x<4) x≡4)
      ... | ∨-introᴿ (∨-introᴿ x≡5) = ⊥-elim ((∧-elimᴿ (<-trans x<4 n<sn)) x≡5)

      x≤4 : x ∈ triple {U = ℕ-Setoid} 1 2 3 → x ≤ 4
      x≤4 (∨-introᴸ (∨-introᴸ x≡1)) =
        Σ-intro 3 (Eq.trans (Eq.cong (_+ 3) x≡1) 1+3≡4)
      x≤4 (∨-introᴸ (∨-introᴿ x≡2)) =
        Σ-intro 2 (Eq.trans (Eq.cong (_+ 2) x≡2) 2+2≡4)
      x≤4 (∨-introᴿ x≡3) =
        Σ-intro 1 (Eq.trans (Eq.cong (_+ 1) x≡3) 3+1≡4)

      4≢x : x ∈ triple {U = ℕ-Setoid} 1 2 3 → 4 ≢ x
      4≢x (∨-introᴸ (∨-introᴸ x≡1)) 4≡x =
        step≢zero (step-inj (Eq.trans 4≡x x≡1))
      4≢x (∨-introᴸ (∨-introᴿ x≡2)) 4≡x =
        step≢zero (step-inj (step-inj (Eq.trans 4≡x x≡2)))
      4≢x (∨-introᴿ x≡3) 4≡x =
        step≢zero (step-inj (step-inj (step-inj (Eq.trans 4≡x x≡3))))

      backward : x ∈ triple {U = ℕ-Setoid} 1 2 3 → x ∈ S ⟨ ℕ-predicate (_< 4) ⟩
      backward x∈123 = ∧-intro x∈S x<4
        where
          x∈S = ∨-introᴸ x∈123
          x<4 = ∧-intro (x≤4 x∈123) (¬sym (4≢x x∈123))

  S⟨n<7⟩≅S : S ⟨ ℕ-predicate (_< 7) ⟩ ≅ S
  S⟨n<7⟩≅S x = ↔-intro forward backward
    where
      forward : x ∈ S ⟨ ℕ-predicate (_< 7) ⟩ → x ∈ S
      forward (∧-intro x∈S x<7) = x∈S

      backward : x ∈ S → x ∈ S ⟨ ℕ-predicate (_< 7) ⟩
      backward x∈S = ∧-intro x∈S x<7
        where
          use-1 = λ x≡1 → Σ-intro 6 (Eq.trans (Eq.cong (_+ 6) x≡1) 1+6≡7)
          use-2 = λ x≡2 → Σ-intro 5 (Eq.trans (Eq.cong (_+ 5) x≡2) 2+5≡7)
          use-3 = λ x≡3 → Σ-intro 4 (Eq.trans (Eq.cong (_+ 4) x≡3) 3+4≡7)
          use-4 = λ x≡4 → Σ-intro 3 (Eq.trans (Eq.cong (_+ 3) x≡4) 4+3≡7)
          use-5 = λ x≡5 → Σ-intro 2 (Eq.trans (Eq.cong (_+ 2) x≡5) 5+2≡7)
          x≤7 = ∨-rec (∨-rec (∨-rec use-1 use-2) use-3) (∨-rec use-4 use-5) x∈S

          x≢7 : x ≢ 7
          x≢7 x≡7 = ∨-rec contra-triple contra-pair x∈S
            where
              7≡x = Eq.sym x≡7
              si = step-inj
              contra-1 =
                step≢zero ∘ si ∘ Eq.trans 7≡x
              contra-2 =
                step≢zero ∘ si ∘ si ∘ Eq.trans 7≡x
              contra-3 =
                step≢zero ∘ si ∘ si ∘ si ∘ Eq.trans 7≡x
              contra-4 =
                step≢zero ∘ si ∘ si ∘ si ∘ si ∘ Eq.trans 7≡x
              contra-5 =
                step≢zero ∘ si ∘ si ∘ si ∘ si ∘ si ∘ Eq.trans 7≡x
              contra-triple = ∨-rec (∨-rec contra-1 contra-2) contra-3
              contra-pair = ∨-rec contra-4 contra-5

          x<7 = ∧-intro x≤7 x≢7

  S⟨n<1⟩≅∅ : S ⟨ ℕ-predicate (_< 1) ⟩ ≅ ∅
  S⟨n<1⟩≅∅ x = ↔-intro forward backward
    where
      forward : x ∈ S ⟨ ℕ-predicate (_< 1) ⟩ → x ∈ ∅ {U = ℕ-Setoid}
      forward (∧-intro x∈S x<1) = ⊥-elim (∨-rec use-triple use-pair x∈S)
        where
          x<2 = <-trans x<1 n<sn
          x<3 = <-trans x<2 n<sn
          x<4 = <-trans x<3 n<sn
          x<5 = <-trans x<4 n<sn
          x≢1 = ∧-elimᴿ x<1
          x≢2 = ∧-elimᴿ x<2
          x≢3 = ∧-elimᴿ x<3
          x≢4 = ∧-elimᴿ x<4
          x≢5 = ∧-elimᴿ x<5
          use-triple = ∨-rec (∨-rec x≢1 x≢2) x≢3
          use-pair = ∨-rec x≢4 x≢5

      backward : x ∈ ∅ {U = ℕ-Setoid} → x ∈ S ⟨ ℕ-predicate (_< 1) ⟩
      backward = ⊥-elim ∘ x∉∅ {U = ℕ-Setoid} x

-- Definition 3.1.23 (Intersections)
_∩_ : ∀ {υ′} → PSet U υ → PSet U υ′ → PSet U (υ ⊔ υ′)
A ∩ B = A ⟨ B ⟩

subst-∩ : ∀ {υ′} {A A′ : PSet U υ} {P : PSet U υ′} → A ≅ A′ → A ∩ P ≅ A′ ∩ P
subst-∩ {U = U} {A = A} {A′} {P} = subst-⟨⟩ {U = U} {A = A} {A′} {P}

∩-subst :
  ∀ {υ′} {A : PSet U υ} {P P′ : PSet U υ′} → P ≅ P′ → A ∩ P ≅ A ∩ P′
∩-subst {U = U} {A = A} {P} {P′} = ⟨⟩-subst {U = U} {A = A} {P} {P′}

-- Examples 3.1.25
infixl 8 _∩_
124∩234≅24 : triple {U = ℕ-Setoid} 1 2 4 ∩ triple 2 3 4 ≅ pair 2 4
124∩234≅24 x = ↔-intro forward backward
  where
    forward :
      x ∈ triple {U = ℕ-Setoid} 1 2 4 ∩ triple 2 3 4 →
        x ∈ pair {U = ℕ-Setoid} 2 4
    forward (∧-intro x∈124 x∈234) = ∨-rec (∨-rec use-1 use-2) use-4 x∈124
      where
        use-1 = λ x≡1 →
          let contra-2 =
                λ x≡2 → step≢zero (step-inj (Eq.trans (Eq.sym x≡2) x≡1))
              contra-3 =
                λ x≡3 → step≢zero (step-inj (Eq.trans (Eq.sym x≡3) x≡1))
              contra-4 =
                λ x≡4 → step≢zero (step-inj (Eq.trans (Eq.sym x≡4) x≡1))
           in ⊥-elim (∨-rec (∨-rec contra-2 contra-3) contra-4 x∈234)
        use-2 = ∨-introᴸ
        use-4 = ∨-introᴿ

    backward :
      x ∈ pair {U = ℕ-Setoid} 2 4 →
        x ∈ triple {U = ℕ-Setoid} 1 2 4 ∩ triple 2 3 4
    backward x∈24 = ∨-rec use-2 use-4 x∈24
      where
        use-2 = λ x≡2 →
          ∧-intro (∨-introᴸ (∨-introᴿ x≡2)) (∨-introᴸ (∨-introᴸ x≡2))
        use-4 = λ x≡4 → ∧-intro (∨-introᴿ x≡4) (∨-introᴿ x≡4)

⟨12⟩ = pair {U = ℕ-Setoid} 1 2
⟨34⟩ = pair {U = ℕ-Setoid} 3 4

⊆-intro : {U : Setoid υ₁ υ₂} {A B : PSet U υ} → (∀ {x} → x ∈ A → x ∈ B) → A ⊆ B
⊆-intro f x = f

12∩34≅∅ : ⟨12⟩ ∩ ⟨34⟩ ≅ ∅
12∩34≅∅ = ⊆-antisym {A = ⟨12⟩ ∩ ⟨34⟩} {∅} 12∩34⊆∅ ∅⊆12∩34
  where
    ∈-pair-elim :
      ∀ {ξ} {X : Set ξ} {x a b : ℕ} →
        (x ≡ a → X) → (x ≡ b → X) → x ∈ pair {U = ℕ-Setoid} a b → X
    ∈-pair-elim = ∨-rec

    x∉12∩34 : ∀ {x} → x ∉ ⟨12⟩ ∩ ⟨34⟩
    x∉12∩34 (∧-intro x∈12 x∈34) = ∈-pair-elim use-1 use-2 x∈12
      where
        use-1 = λ x≡1 →
          let contra-3 = step≢zero ∘ step-inj ∘ flip Eq.trans x≡1 ∘ Eq.sym
              contra-4 = step≢zero ∘ step-inj ∘ flip Eq.trans x≡1 ∘ Eq.sym
           in ∈-pair-elim contra-3 contra-4 x∈34
        use-2 = λ x≡2 →
          let contra-3 =
                step≢zero ∘ step-inj ∘ step-inj ∘ flip Eq.trans x≡2 ∘ Eq.sym
              contra-4 =
                step≢zero ∘ step-inj ∘ step-inj ∘ flip Eq.trans x≡2 ∘ Eq.sym
           in ∈-pair-elim contra-3 contra-4 x∈34

    12∩34⊆∅ = ⊆-intro {A = ⟨12⟩ ∩ ⟨34⟩} {∅} (⊥-elim ∘ x∉12∩34)
    ∅⊆12∩34 = ∅⊆A {A = ⟨12⟩ ∩ ⟨34⟩}

⟨23⟩ = pair {U = ℕ-Setoid} 2 3

23∪∅≅23 : ⟨23⟩ ∪ ∅ ≅ ⟨23⟩
23∪∅≅23 = ∪-identᴿ {A = ⟨23⟩}

23∩∅≅∅ : ⟨23⟩ ∩ ∅ ≅ ∅ {υ = υ}
23∩∅≅∅ = A⟨∅⟩≅∅ {A = ⟨23⟩}
