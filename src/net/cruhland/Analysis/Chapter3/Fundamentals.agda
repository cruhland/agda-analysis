open import Agda.Builtin.FromNat using (Number)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
import Data.List.Membership.DecPropositional as DecMembership
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤)
open import Function using (id; _∘_)
open import Level using (_⊔_; Level) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (DecSetoid; Decidable)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; sym; isEquivalence)
open import Relation.Nullary using (does)
open import Relation.Nullary.Decidable using (False; True; toWitness)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sets using (SetTheory)
import net.cruhland.axioms.Sets.Finite as FiniteSets
open import net.cruhland.models.Logic using (no; yes)

module net.cruhland.Analysis.Chapter3.Fundamentals
    (PA : PeanoArithmetic) (ST : SetTheory) where
  open PeanoArithmetic PA using
    (_≡?_; ℕ; number; step; step-inj; step≢zero; zero)
  open SetTheory ST using
    (_∈_; _∉_; ES; El; PSet; PSet-Setoid; PU; SA; SS; Setoid)
  open FiniteSets SA ES PU SS using (finite; a∈finite; a∉finite)

  variable
    σ₁ σ₂ α β : Level
    S : Setoid σ₁ σ₂

  ℕ-Setoid : Setoid lzero lzero
  ℕ-Setoid = record { Carrier = ℕ ; _≈_ = _≡_ ; isEquivalence = isEquivalence }

  ℕ-DecSetoid : DecSetoid lzero lzero
  ℕ-DecSetoid = record
    { Carrier = ℕ
    ; _≈_ = _≡_
    ; isDecEquivalence = record { isEquivalence = isEquivalence ; _≟_ = _≡?_ }
    }

  open DecMembership {A = ℕ} _≡?_
    using () renaming (_∈?_ to _∈ᴸ?_; _∈_ to _∈ᴸ_; _∉_ to _∉ᴸ_)

  3≢1 : 3 ≢ 1
  3≢1 = step≢zero ∘ step-inj

  4≢1 : 4 ≢ 1
  4≢1 = step≢zero ∘ step-inj

  4≢2 = 3≢1 ∘ step-inj

  5≢1 : 5 ≢ 1
  5≢1 = step≢zero ∘ step-inj

  5≢2 = 4≢1 ∘ step-inj
  5≢3 = 4≢2 ∘ step-inj

  6≢1 : 6 ≢ 1
  6≢1 = step≢zero ∘ step-inj

  6≢2 = 5≢1 ∘ step-inj
  6≢3 = 5≢2 ∘ step-inj
  6≢4 = 5≢3 ∘ step-inj

  7≢1 : 7 ≢ 1
  7≢1 = step≢zero ∘ step-inj

  7≢2 = 6≢1 ∘ step-inj
  7≢3 = 6≢2 ∘ step-inj
  7≢4 = 6≢3 ∘ step-inj
  7≢5 = 6≢4 ∘ step-inj

  {- 3.1 Fundamentals -}

  -- Definition 3.1.1. (Informal) We define a _set_ A to be any
  -- unordered collection of objects
  _ : Setoid σ₁ σ₂ → ∀ α → Set (σ₁ ⊔ σ₂ ⊔ lsuc α)
  _ = PSet

  -- e.g., {3, 8, 5, 2} is a set.
  _ : PSet ℕ-Setoid lzero
  _ = finite (3 ∷ 8 ∷ 5 ∷ 2 ∷ [])

  -- If x is an object, we say that x _is an element of_ A or x ∈ A if
  -- x lies in the collection
  _ : El S → PSet S α → Set α
  _ = _∈_

  -- otherwise we say that x ∉ A.
  _ : El S → PSet S α → Set α
  _ = _∉_

  ⟨12345⟩ = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []

  _ : 3 ∈ᴸ ⟨12345⟩
  _ = toWitness {Q = 3 ∈ᴸ? ⟨12345⟩} _

  -- For instance, 3 ∈ {1, 2, 3, 4, 5}
  _ : 3 ∈ finite {S = ℕ-Setoid} ⟨12345⟩
  _ = a∈finite {xs = ⟨12345⟩} (there (there (here refl)))

  -- but 7 ∉ {1, 2, 3, 4, 5}.
  _ : 7 ∉ finite {S = ℕ-Setoid} ⟨12345⟩
  _ = a∉finite {xs = ⟨12345⟩} 7∉ᴸ⟨12345⟩
    where
      7∉ᴸ⟨12345⟩ : 7 ∉ᴸ ⟨12345⟩
      7∉ᴸ⟨12345⟩ (here 7≡1) = 7≢1 7≡1
      7∉ᴸ⟨12345⟩ (there (here 7≡2)) = 7≢2 7≡2
      7∉ᴸ⟨12345⟩ (there (there (here 7≡3))) = 7≢3 7≡3
      7∉ᴸ⟨12345⟩ (there (there (there (here 7≡4)))) = 7≢4 7≡4
      7∉ᴸ⟨12345⟩ (there (there (there (there (here 7≡5))))) = 7≢5 7≡5

  -- Axiom 3.1 (Sets are objects). If A is a set, then A is also an
  -- object. In particular, given two sets A and B, it is meaningful to
  -- ask whether A is also an element of B.
  set-in-set? : PSet S α → PSet (PSet-Setoid S α) β → Set β
  set-in-set? A B = A ∈ B
