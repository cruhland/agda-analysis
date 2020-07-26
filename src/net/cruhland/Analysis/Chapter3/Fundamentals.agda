open import Data.List using ([]; _∷_)
import Data.List.Membership.DecPropositional as DecMembership
open import Function using (_∘_)
open import Level using (_⊔_; Level) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (DecSetoid)
open import Relation.Binary.PropositionalEquality using (setoid; decSetoid)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sets using (SetTheory)
open import net.cruhland.models.Logic using
  (_∨_; ∨-comm; ∨-introᴸ; ∨-introᴿ; ∨-merge; _↔_; ↔-elimᴸ; ↔-elimᴿ; ↔-intro)
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)

module net.cruhland.Analysis.Chapter3.Fundamentals (ST : SetTheory) where
  open PeanoArithmetic peanoArithmetic using (ℕ; _≡?_)

  open SetTheory ST using
    ( _∈_; _∉_; _≗_; _≗̸_; El; ≗-intro; PSet; PSet-Setoid; Setoid
    ; ≗-refl; ∈-substᴸ; ∈-substᴿ; ≗-sym; ≗-trans
    ; ∅; x∉∅; ∅-unique
    ; singleton; singleton-unique; x∈sa↔x≈a; x∈sa-elim; x∈sa-intro
    ; pair; pair-unique; x∈pab↔x≈a∨x≈b; x∈pab-elim; x∈pab-intro
    ; _⊆_; ⊆-antisym; ⊆-intro
    ; finite; module Memberᴸ; module Subsetᴸ
    )

  variable
    σ₁ σ₂ α β : Level
    S : Setoid σ₁ σ₂

  ℕ-Setoid : Setoid lzero lzero
  ℕ-Setoid = setoid ℕ

  ℕ-DecSetoid : DecSetoid lzero lzero
  ℕ-DecSetoid = decSetoid _≡?_

  open Memberᴸ {DS = ℕ-DecSetoid} using (_∈?_)
  open Subsetᴸ {DS = ℕ-DecSetoid} using (_≗?_)

  {- 3.1 Fundamentals -}

  -- Definition 3.1.1. (Informal) We define a _set_ A to be any
  -- unordered collection of objects
  _ : Setoid σ₁ σ₂ → ∀ α → Set (σ₁ ⊔ σ₂ ⊔ lsuc α)
  _ = PSet

  -- e.g., {3, 8, 5, 2} is a set.
  [3852] = 3 ∷ 8 ∷ 5 ∷ 2 ∷ []
  ⟨3852⟩ : PSet ℕ-Setoid lzero
  ⟨3852⟩ = finite {S = ℕ-Setoid} [3852]

  -- If x is an object, we say that x _is an element of_ A or x ∈ A if
  -- x lies in the collection
  _ : El S → PSet S α → Set α
  _ = _∈_

  -- otherwise we say that x ∉ A.
  _ : El S → PSet S α → Set α
  _ = _∉_

  [12345] = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
  ⟨12345⟩ = finite {S = ℕ-Setoid} [12345]

  -- For instance, 3 ∈ {1, 2, 3, 4, 5}
  _ : 3 ∈ ⟨12345⟩
  _ = toWitness {Q = 3 ∈? [12345]} _

  -- but 7 ∉ {1, 2, 3, 4, 5}.
  _ : 7 ∉ ⟨12345⟩
  _ = toWitnessFalse {Q = 7 ∈? [12345]} _

  -- Axiom 3.1 (Sets are objects). If A is a set, then A is also an
  -- object. In particular, given two sets A and B, it is meaningful to
  -- ask whether A is also an element of B.
  set-in-set? : PSet S α → PSet (PSet-Setoid S α) β → Set β
  set-in-set? A B = A ∈ B

  -- Example 3.1.2. The set {3, {3, 4}, 4} is a set of three distinct
  -- elements, one of which happens to itself be a set of two
  -- elements.
  -- [note] We wrap the elements in a sum type because our sets
  -- require all elements to have the same type. Apart from that, this
  -- set will behave identically to the one given in the example.
  _ : PSet (setoid (ℕ ∨ PSet ℕ-Setoid lzero)) lzero
  _ = finite (∨-introᴸ 3 ∷ ∨-introᴿ (finite (3 ∷ 4 ∷ [])) ∷ ∨-introᴸ 4 ∷ [])

  -- To summarize so far...if x is an object and A is a set, then
  -- either x ∈ A is true or x ∈ A is false.
  -- [note] This statement is not actually correct in type theory, as
  -- it would amount to the relation _∈_ always being decidable. For
  -- specific types (such as finite sets of natural numbers) this is
  -- the case, but it doesn't hold in general. This will have
  -- interesting consequences that we'll have to deal with in later
  -- chapters.

  -- Definition 3.1.4 (Equality of sets). Two sets A and B are
  -- _equal_, A ≗ B, iff every element of A is an element of B and
  -- vice versa.
  _ : {S : Setoid σ₁ σ₂} → PSet S α → PSet S α → Set (σ₁ ⊔ α)
  _ = _≗_

  -- Example 3.1.5
  [34215] = 3 ∷ 4 ∷ 2 ∷ 1 ∷ 5 ∷ []
  _ : ⟨12345⟩ ≗ finite [34215]
  _ = toWitness {Q = [12345] ≗? [34215]} _

  [3315242] = 3 ∷ 3 ∷ 1 ∷ 5 ∷ 2 ∷ 4 ∷ 2 ∷ []
  _ : ⟨12345⟩ ≗ finite [3315242]
  _ = toWitness {Q = [12345] ≗? [3315242]} _

  -- [note] informal examples given prior to Definition 3.1.4
  [2358] = 2 ∷ 3 ∷ 5 ∷ 8 ∷ []
  _ : ⟨3852⟩ ≗ finite [2358]
  _ = toWitness {Q = [3852] ≗? [2358]} _

  [38521] = 3 ∷ 8 ∷ 5 ∷ 2 ∷ 1 ∷ []
  _ : ⟨3852⟩ ≗̸ finite [38521]
  _ = toWitnessFalse {Q = [3852] ≗? [38521]} _

  [385] = 3 ∷ 8 ∷ 5 ∷ []
  _ : ⟨3852⟩ ≗̸ finite [385]
  _ = toWitnessFalse {Q = [3852] ≗? [385]} _

  -- Exercise 3.1.1
  -- One can easily verify that this notion of equality is reflexive,
  -- symmetric, and transitive.
  _ : {A : PSet S α} → A ≗ A
  _ = ≗-refl

  _ : {A B : PSet S α} → A ≗ B → B ≗ A
  _ = ≗-sym

  _ : {A B C : PSet S α} → A ≗ B → B ≗ C → A ≗ C
  _ = ≗-trans

  -- Observe that if x ∈ A and A ≗ B, then x ∈ B, by Definition
  -- 3.1.4. This the "is an element of" relation _∈_ obeys the axiom
  -- of substitution.
  _ : {S : Setoid σ₁ σ₂} {A B : PSet S α} {x : El S} → A ≗ B → x ∈ A → x ∈ B
  _ = ∈-substᴿ

  -- [note] Tao only mentions substitution for the right-hand side of
  -- _∈_, but it's also important that it works for the left-hand
  -- side:
  _ : {A B : PSet S α} {C : PSet (PSet-Setoid S α) β} → A ≗ B → A ∈ C → B ∈ C
  _ = ∈-substᴸ

  -- Axiom 3.2 (Empty set). There exists a set ∅, known as the _empty set_
  _ : PSet S α
  _ = ∅

  -- which contains no elements, i.e., for every object x we have x ∉ ∅.
  _ : {S : Setoid σ₁ σ₂} {x : El S} → x ∉ (∅ {S = S} {α = α})
  _ = x∉∅

  -- Note that there can only be one empty set; if there were two sets
  -- ∅ and ∅′ which were both empty, then by Definition 3.1.4 they
  -- would be equal to each other.
  _ : {S : Setoid σ₁ σ₂} {∅′ : PSet S α} → (∀ {x} → x ∉ ∅′) → ∅ ≗ ∅′
  _ = ∅-unique

  -- Lemma 3.1.6 (Single choice). Let A be a non-empty set. Then there
  -- exists an object x such that x ∈ A.
  -- [note] This is not provable in Agda because it's nonconstructive.
  -- Instead of using evidence that a set is not equal to the empty
  -- set, we will need to use direct evidence that an element of a set
  -- exists.

  -- Axiom 3.3 (Singleton sets and pair sets). If a is an object, then
  -- there exists a set (singleton a) whose only element is a
  _ : El S → PSet S α
  _ = singleton

  -- i.e., for every object y, we have y ∈ singleton a if and only if y ≈ a
  _ :
    {S : Setoid σ₁ σ₂} {a y : El S} →
      let open Setoid S using (_≈_) in y ∈ singleton {S = S} {α = α} a ↔ y ≈ a
  _ = x∈sa↔x≈a

  -- Furthermore, if a and b are objects, then there exists a set
  -- (pair a b) whose only elements are a and b
  _ : El S → El S → PSet S α
  _ = pair

  -- i.e., for every object y, we have y ∈ pair a b if and only if
  -- y ≈ a or y ≈ b
  _ :
    {S : Setoid σ₁ σ₂} {a b y : El S} →
      let open Setoid S using (_≈_) in y ∈ pair {S = S} {α} a b ↔ y ≈ a ∨ y ≈ b
  _ = x∈pab↔x≈a∨x≈b

  -- Remarks 3.1.9
  -- Just as there is only one empty set, there is only one singleton
  -- set for each object a, thanks to Definition 3.1.4.
  _ :
    {S : Setoid σ₁ σ₂} {A : PSet S α} {a : El S} →
      let open Setoid S using (_≈_) in (∀ {x} → x ∈ A ↔ x ≈ a) → singleton a ≗ A
  _ = singleton-unique

  -- Similarly, given any two objects a and b, there is only one pair
  -- set formed by a and b.
  _ :
    {S : Setoid σ₁ σ₂} {A : PSet S α} {a b : El S} →
      let open Setoid S using (_≈_)
       in (∀ {x} → x ∈ A ↔ x ≈ a ∨ x ≈ b) → pair a b ≗ A
  _ = pair-unique

  -- Also, Definition 3.1.4 ensures that pair a b ≗ pair b a
  pair-comm : {S : Setoid σ₁ σ₂} {a b : El S} → pair {S = S} {α} a b ≗ pair b a
  pair-comm {S = S} = ⊆-antisym ab⊆ba ba⊆ab
    where
      ab⊆ba = ⊆-intro (x∈pab-intro ∘ ∨-comm ∘ x∈pab-elim)
      ba⊆ab = ⊆-intro (x∈pab-intro ∘ ∨-comm ∘ x∈pab-elim)

  -- and pair a a ≗ singleton a.
  pair-singleton :
    {S : Setoid σ₁ σ₂} {a : El S} → pair {S = S} {α} a a ≗ singleton a
  pair-singleton = ⊆-antisym paa⊆sa sa⊆paa
    where
      paa⊆sa = ⊆-intro (x∈sa-intro ∘ ∨-merge ∘ x∈pab-elim)
      sa⊆paa = ⊆-intro (x∈pab-intro ∘ ∨-introᴸ ∘ x∈sa-elim)
