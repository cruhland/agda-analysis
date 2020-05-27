open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import net.cruhland.axiomatic.Logic using (LogicBundle)

module net.cruhland.Analysis.Chapter3.Predicate2 (LB : LogicBundle) where

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

open _⇒_ using (_⟨$⟩_)

-- Extensionality setoid (equality of equality-preserving functions)
ext-Setoid : ∀ {α₁ α₂ β₁ β₂} → Setoid α₁ α₂ → Setoid β₁ β₂ → Setoid _ _
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
