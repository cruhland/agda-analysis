open import Data.List using ([]; _∷_; _++_; List)
open import Function using (_∘_; const; id)
open import Level using (_⊔_; Level) renaming (suc to lstep; zero to lzero)
open import Relation.Binary using (DecSetoid)
open import Relation.Binary.PropositionalEquality using
  (_≡_; decSetoid; refl; setoid; sym; trans)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sets using (SetTheory)
open import net.cruhland.models.Logic using
  ( _∧_; ∧-dup; ∧-intro; uncurry
  ; _∨_; ∨-comm; ∨-forceᴸ; ∨-introᴸ; ∨-introᴿ; ∨-merge; ∨-rec
  ; _↔_; ↔-elimᴸ; ↔-elimᴿ; ↔-intro
  ; ⊤; ⊥; ⊥-elim; ⊤-intro
  ; Dec; dec-map; no; yes
  )
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)
open import net.cruhland.models.Setoid using
  (El; equivalence-id; Π; Setoid; Setoid₀; SPred₀; SPred-const; SRel₀)

module net.cruhland.Analysis.Chapter3.Fundamentals (ST : SetTheory) where
  open PeanoArithmetic peanoArithmetic using (ℕ; _≡?_; _<_; _<?_; step)

  open SetTheory ST using
    ( _∈_; _∉_; _≃_; _≄_; ≃-intro; PSet; PSet₀; PSet-Setoid
    ; ≃→⊆ᴸ; ≃→⊆ᴿ; ≃-elimᴸ; ≃-elimᴿ; ≃-refl; ∈-substᴸ; ∈-substᴿ; ≃-sym; ≃-trans
    ; module ≃-Reasoning
    ; ∅; x∉∅; ∅-unique
    ; singleton; singleton-unique; a∈sa; x∈sa↔a≈x; x∈sa-elim; x∈sa-intro
    ; pair; x∈pab↔a≈x∨b≈x; a∈pab; b∈pab; x∈pab-elimᴸ; x∈pab-elimᴿ
    ; x∈pab-intro; x∈pab-introᴸ; x∈pab-introᴿ; pair-unique
    ; _∪_; x∈A∪B↔x∈A∨x∈B; ∪-∅ᴸ; ∪-∅ᴿ; ∪-assoc; ∪-comm; x∈A∪B-elim
    ; x∈A∪B-introᴸ; x∈A∪B-introᴿ; ∪-substᴸ; ∪-substᴿ
    ; _⊆_; _⊈_; _⊊_; ∅-⊆; A⊆∅→A≃∅; ⊆-antisym; ⊆-elim; ⊆-intro; ⊊-intro
    ; ⊆-refl; ⊆-substᴸ; ⊆-substᴿ; ⊊-substᴸ; ⊊-substᴿ; ⊆-trans; ⊊-trans
    ; ⟨_⟩; x∈⟨P⟩↔Px; x∈⟨P⟩-elim; x∈⟨P⟩-intro
    ; _∩_; x∈A∩B↔x∈A∧x∈B; ∩-assoc; ∩-comm; x∈A∩B-elim; x∈A∩B-elimᴸ; x∈A∩B-elimᴿ
    ; ∩-idempotent; x∈A∩B-intro; x∈A∩B-intro₂; ∩-substᴸ; ∩-substᴿ; ∩-∅ᴿ
    ; _∖_; x∈A∖B-elim; x∈A∖B-elimᴸ; x∈A∖B-elimᴿ; x∈A∖B-intro₂
    ; DecMembership; _∈?_; ∁-∈?; ∖-∈?; ∅-∈?; ∩-∈?
    ; pair-∈?; ⟨P⟩-∈?; singleton-∈?; ∪-∈?
    ; finite; Finite; Finite-∅; Finite-singleton; Finite-pair
    ; Finite-∪; Finite-∩ᴸ; Finite-∖; module Subsetᴸ
    ; ∪⊆-elim; ∪⊆-elimᴸ; ∪⊆-elimᴿ; ⊆∪-introᴸ; ⊆∪-introᴿ; ∪⊆-intro₂
    ; pab≃sa∪sb; ⊆∩-elim; ⊆∩-intro₂; ∩⊆-introᴸ; ∩⊆-introᴿ; ∩-preserves-⊆ᴸ
    ; ∩-over-∪ᴸ; ∪-over-∩ᴸ; A∖B⊆A
    ; replacement; ReplFun; ReplMembership; ReplProp
    ; x∈rep↔Pax; rep-∈?; rep-finite
    )
  open ≃-Reasoning

  variable
    σ₁ σ₂ α β χ : Level
    S : Setoid σ₁ σ₂

  ℕ-Setoid : Setoid lzero lzero
  ℕ-Setoid = setoid ℕ

  instance
    ℕ-DecSetoid : DecSetoid lzero lzero
    ℕ-DecSetoid = decSetoid _≡?_

  open Subsetᴸ {DS = ℕ-DecSetoid} using (_⊆?_; _≃?_)

  {- 3.1 Fundamentals -}

  -- Definition 3.1.1. (Informal) We define a _set_ A to be any
  -- unordered collection of objects
  _ : Setoid σ₁ σ₂ → ∀ α → Set (σ₁ ⊔ σ₂ ⊔ lstep α)
  _ = PSet

  ℕSet : Set₁
  ℕSet = PSet ℕ-Setoid lzero

  fromListℕ : List ℕ → ℕSet
  fromListℕ = finite

  -- e.g., {3, 8, 5, 2} is a set.
  ⟨3852⟩ : ℕSet
  ⟨3852⟩ = fromListℕ (3 ∷ 8 ∷ 5 ∷ 2 ∷ [])

  -- If x is an object, we say that x _is an element of_ A or x ∈ A if
  -- x lies in the collection
  _ : El S → PSet S α → Set α
  _ = _∈_

  -- otherwise we say that x ∉ A.
  _ : El S → PSet S α → Set α
  _ = _∉_

  ⟨12345⟩ = fromListℕ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])

  -- For instance, 3 ∈ {1, 2, 3, 4, 5}
  _ : 3 ∈ ⟨12345⟩
  _ = toWitness {Q = 3 ∈? ⟨12345⟩} _

  -- but 7 ∉ {1, 2, 3, 4, 5}.
  _ : 7 ∉ ⟨12345⟩
  _ = toWitnessFalse {Q = 7 ∈? ⟨12345⟩} _

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
  -- TODO: Restore level parameters to finite, but carefully
  -- _ : PSet (setoid (ℕ ∨ ℕSet)) (lstep lzero)
  -- _ = finite (∨-introᴸ 3 ∷ ∨-introᴿ (fromListℕ (3 ∷ 4 ∷ [])) ∷ ∨-introᴸ 4 ∷ [])

  -- To summarize so far...if x is an object and A is a set, then
  -- either x ∈ A is true or x ∈ A is false.
  -- [note] This general statement is not provable in type theory, as
  -- it would amount to the relation _∈_ always being decidable. For
  -- specific types (such as finite sets of natural numbers) this is
  -- the case, but it doesn't hold in general. This will have
  -- interesting consequences that we'll have to deal with in later
  -- chapters.

  -- Axioms 3.2 (Equality of sets). Two sets A and B are
  -- _equal_, A ≃ B, iff every element of A is an element of B and
  -- vice versa.
  _ : {S : Setoid σ₁ σ₂} → PSet S α → PSet S α → Set (σ₁ ⊔ α)
  _ = _≃_

  -- Example 3.1.4
  ⟨34215⟩ = fromListℕ (3 ∷ 4 ∷ 2 ∷ 1 ∷ 5 ∷ [])
  _ : ⟨12345⟩ ≃ ⟨34215⟩
  _ = toWitness {Q = ⟨12345⟩ ≃? ⟨34215⟩} _

  ⟨3315242⟩ = fromListℕ (3 ∷ 3 ∷ 1 ∷ 5 ∷ 2 ∷ 4 ∷ 2 ∷ [])
  _ : ⟨12345⟩ ≃ ⟨3315242⟩
  _ = toWitness {Q = ⟨12345⟩ ≃? ⟨3315242⟩} _

  -- [note] informal examples given prior to Definition 3.1.4
  ⟨2358⟩ = fromListℕ (2 ∷ 3 ∷ 5 ∷ 8 ∷ [])
  _ : ⟨3852⟩ ≃ ⟨2358⟩
  _ = toWitness {Q = ⟨3852⟩ ≃? ⟨2358⟩} _

  ⟨38521⟩ = fromListℕ (3 ∷ 8 ∷ 5 ∷ 2 ∷ 1 ∷ [])
  _ : ⟨3852⟩ ≄ ⟨38521⟩
  _ = toWitnessFalse {Q = ⟨3852⟩ ≃? ⟨38521⟩} _

  ⟨385⟩ = fromListℕ (3 ∷ 8 ∷ 5 ∷ [])
  _ : ⟨3852⟩ ≄ ⟨385⟩
  _ = toWitnessFalse {Q = ⟨3852⟩ ≃? ⟨385⟩} _

  -- Exercise 3.1.1
  -- One can easily verify that this notion of equality is reflexive,
  -- symmetric, and transitive.
  _ : {A : PSet S α} → A ≃ A
  _ = ≃-refl

  _ : {A B : PSet S α} → A ≃ B → B ≃ A
  _ = ≃-sym

  _ : {A B C : PSet S α} → A ≃ B → B ≃ C → A ≃ C
  _ = ≃-trans

  -- The "is an element of" relation _∈_ obeys the axiom of
  -- substitution.
  _ : {S : Setoid σ₁ σ₂} {A B : PSet S α} {x : El S} → A ≃ B → x ∈ A → x ∈ B
  _ = ∈-substᴿ

  _ : {A B : PSet S α} {C : PSet (PSet-Setoid S α) β} → A ≃ B → A ∈ C → B ∈ C
  _ = ∈-substᴸ

  -- Axiom 3.3 (Empty set). There exists a set ∅, known as the _empty set_
  _ : PSet S α
  _ = ∅

  -- which contains no elements, i.e., for every object x we have x ∉ ∅.
  _ : {S : Setoid σ₁ σ₂} {x : El S} → x ∉ (∅ {S = S} {α = α})
  _ = x∉∅

  -- Note that there can only be one empty set; if there were two sets
  -- ∅ and ∅′ which were both empty, then by Axiom 3.2 they would be
  -- equal to each other.
  _ : {S : Setoid σ₁ σ₂} {∅′ : PSet S α} → (∀ {x} → x ∉ ∅′) → ∅ ≃ ∅′
  _ = ∅-unique

  -- Lemma 3.1.5 (Single choice). Let A be a non-empty set. Then there
  -- exists an object x such that x ∈ A.
  -- [note] This is not provable in Agda because it's nonconstructive.
  -- Instead of using evidence that a set is not equal to the empty
  -- set, we will need to use direct evidence that an element of a set
  -- exists.

  -- Axiom 3.4 (Singleton sets and pair sets). If a is an object, then
  -- there exists a set (singleton a) whose only element is a
  _ : {S : Setoid σ₁ σ₂} → El S → PSet S σ₂
  _ = singleton

  -- i.e., for every object y, we have y ∈ singleton a if and only if a ≈ y
  _ :
    {S : Setoid σ₁ σ₂} {a y : El S} →
      let open Setoid S using (_≈_) in y ∈ singleton {S = S} a ↔ a ≈ y
  _ = x∈sa↔a≈x

  -- Furthermore, if a and b are objects, then there exists a set
  -- (pair a b) whose only elements are a and b
  _ : {S : Setoid σ₁ σ₂} → El S → El S → PSet S σ₂
  _ = pair

  -- i.e., for every object y, we have y ∈ pair a b if and only if
  -- a ≈ y or b ≈ y
  _ :
    {S : Setoid σ₁ σ₂} {a b y : El S} →
      let open Setoid S using (_≈_) in y ∈ pair {S = S} a b ↔ a ≈ y ∨ b ≈ y
  _ = x∈pab↔a≈x∨b≈x

  -- Remarks 3.1.8
  -- Just as there is only one empty set, there is only one singleton
  -- set for each object a, thanks to Axiom 3.2.
  _ :
    {S : Setoid σ₁ σ₂} {A : PSet S σ₂} {a : El S} →
      let open Setoid S using (_≈_) in (∀ {x} → x ∈ A ↔ a ≈ x) → singleton a ≃ A
  _ = singleton-unique

  -- Similarly, given any two objects a and b, there is only one pair
  -- set formed by a and b.
  _ :
    {S : Setoid σ₁ σ₂} {A : PSet S σ₂} {a b : El S} →
      let open Setoid S using (_≈_)
       in (∀ {x} → x ∈ A ↔ a ≈ x ∨ b ≈ x) → pair a b ≃ A
  _ = pair-unique

  -- Also, Axiom 3.2 ensures that pair a b ≃ pair b a
  pair-comm : {S : Setoid σ₁ σ₂} {a b : El S} → pair {S = S} a b ≃ pair b a
  pair-comm {S = S} = ⊆-antisym ab⊆ba ba⊆ab
    where
      ab⊆ba = ⊆-intro (x∈pab-intro ∘ ∨-comm ∘ x∈pab-elimᴿ)
      ba⊆ab = ⊆-intro (x∈pab-intro ∘ ∨-comm ∘ x∈pab-elimᴿ)

  -- and pair a a ≃ singleton a.
  pair-singleton :
    {S : Setoid σ₁ σ₂} {a : El S} → pair {S = S} a a ≃ singleton a
  pair-singleton = ⊆-antisym paa⊆sa sa⊆paa
    where
      paa⊆sa = ⊆-intro (x∈sa-intro ∘ ∨-merge ∘ x∈pab-elimᴿ)
      sa⊆paa = ⊆-intro (x∈pab-introᴸ ∘ x∈sa-elim)

  -- Examples 3.1.9
  -- Exercise 3.1.2
  sa≄∅ : (a : El S) → singleton {S = S} a ≄ ∅
  sa≄∅ a sa≃∅ = x∉∅ (≃-elimᴸ sa≃∅ a∈sa)

  pab≄∅ : (a b : El S) → pair {S = S} a b ≄ ∅
  pab≄∅ a b pab≃∅ = x∉∅ (≃-elimᴸ pab≃∅ a∈pab)

  s∅≄∅ : singleton {S = PSet-Setoid S α} ∅ ≄ ∅
  s∅≄∅ = sa≄∅ ∅

  ss∅≄∅ :
    {S : Setoid σ₁ σ₂} →
      singleton {S = PSet-Setoid (PSet-Setoid S α) (σ₁ ⊔ α)} (singleton ∅) ≄ ∅
  ss∅≄∅ = sa≄∅ (singleton ∅)

  p∅s∅≄∅ :
    {S : Setoid σ₁ σ₂} →
      pair {S = PSet-Setoid (PSet-Setoid S α) (σ₁ ⊔ α)} ∅ (singleton ∅) ≄ ∅
  p∅s∅≄∅ = pab≄∅ ∅ (singleton ∅)

  s∅∉s∅ :
    {S : Setoid σ₁ σ₂} →
      singleton ∅ ∉ singleton {S = PSet-Setoid (PSet-Setoid S α) (σ₁ ⊔ α)} ∅
  s∅∉s∅ s∅∈s∅ = s∅≄∅ (≃-sym (x∈sa-elim s∅∈s∅))

  ss∅≄s∅ :
    {S : Setoid σ₁ σ₂} →
      let S″ = PSet-Setoid (PSet-Setoid S α) (σ₁ ⊔ α)
       in singleton {S = S″} (singleton ∅) ≄ singleton ∅
  ss∅≄s∅ ss∅≃s∅ = s∅∉s∅ (≃-elimᴸ ss∅≃s∅ (x∈sa-intro ≃-refl))

  p∅s∅≄s∅ :
    {S : Setoid σ₁ σ₂} →
      let S″ = PSet-Setoid (PSet-Setoid S α) (σ₁ ⊔ α)
       in pair {S = S″} ∅ (singleton ∅) ≄ singleton ∅
  p∅s∅≄s∅ p∅s∅≃s∅ = s∅∉s∅ (≃-elimᴸ p∅s∅≃s∅ (x∈pab-introᴿ ≃-refl))

  p∅s∅≄ss∅ :
    {S : Setoid σ₁ σ₂} →
      let S″ = PSet-Setoid (PSet-Setoid S α) (σ₁ ⊔ α)
       in pair {S = S″} ∅ (singleton ∅) ≄ singleton (singleton ∅)
  p∅s∅≄ss∅ p∅s∅≃ss∅ =
    let ∅∈ss∅ = ≃-elimᴸ p∅s∅≃ss∅ (x∈pab-introᴸ ≃-refl)
     in s∅≄∅ (x∈sa-elim ∅∈ss∅)

  -- Axiom 3.5 (Pairwise union). Given any two sets A, B, there exists
  -- a set A ∪ B, called the _union_ A ∪ B of A and B, which consists
  -- of all the elements which belong to A or B or both.
  _ : PSet S α → PSet S β → PSet S (α ⊔ β)
  _ = _∪_

  -- In other words, for any object x, x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B.
  _ :
    {S : Setoid σ₁ σ₂} {A : PSet S α} {B : PSet S β} →
      ∀ {x} → x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B
  _ = x∈A∪B↔x∈A∨x∈B

  -- Example 3.1.10
  ⟨12⟩ = fromListℕ (1 ∷ 2 ∷ [])
  ⟨23⟩ = fromListℕ (2 ∷ 3 ∷ [])
  ⟨123⟩ = fromListℕ (1 ∷ 2 ∷ 3 ∷ [])

  _ : ⟨12⟩ ∪ ⟨23⟩ ≃ ⟨123⟩
  _ = toWitness {Q = ⟨12⟩ ∪ ⟨23⟩ ≃? ⟨123⟩} _

  -- Remark 3.1.11. If A, B, A′ are sets, and A is equal to A′, then A
  -- ∪ B is equal to A′ ∪ B.
  _ : {A A′ : PSet S α} {B : PSet S β} → A ≃ A′ → A ∪ B ≃ A′ ∪ B
  _ = ∪-substᴸ

  -- Similarly if B′ is a set which is equal to B, then A ∪ B is equal
  -- to A ∪ B′. Thus the operation of union obeys the axiom of
  -- substitution, and is thus well-defined on sets.
  _ : {A : PSet S α} {B B′ : PSet S β} → B ≃ B′ → A ∪ B ≃ A ∪ B′
  _ = ∪-substᴿ

  -- Lemma 3.1.12.
  -- Exercise 3.1.3.
  -- If a and b are objects, then pair a b ≃ singleton a ∪ singleton b.
  _ :
    {S : Setoid σ₁ σ₂} {a b : El S} →
      pair a b ≃ singleton {S = S} a ∪ singleton b
  _ = pab≃sa∪sb

  -- If A, B, C are sets, then the union operation is commutative and
  -- associative.
  _ : {A : PSet S α} {B : PSet S β} → A ∪ B ≃ B ∪ A
  _ = ∪-comm

  _ : {A : PSet S α} {B : PSet S β} {C : PSet S χ} → (A ∪ B) ∪ C ≃ A ∪ (B ∪ C)
  _ = ∪-assoc

  -- Also, we have A ∪ A ≃ A ∪ ∅ ≃ ∅ ∪ A ≃ A.
  ∪-merge : {A : PSet S α} → A ∪ A ≃ A
  ∪-merge = ⊆-antisym (⊆-intro (∨-merge ∘ x∈A∪B-elim)) (⊆-intro x∈A∪B-introᴸ)

  _ : {S : Setoid σ₁ σ₂} {A : PSet S α} → A ∪ ∅ ≃ A
  _ = ∪-∅ᴿ

  _ : {S : Setoid σ₁ σ₂} {A : PSet S α} → ∅ ∪ A ≃ A
  _ = ∪-∅ᴸ

  -- Definition 3.1.14 (Subsets). Let A, B be sets. We say that A is a
  -- _subset_ of B, denoted A ⊆ B
  _ : {S : Setoid σ₁ σ₂} → PSet S α → PSet S β → Set (σ₁ ⊔ α ⊔ β)
  _ = _⊆_

  -- iff every element of A is also an element of B, i.e. for any
  -- object x, x ∈ A → x ∈ B.
  _ :
    {S : Setoid σ₁ σ₂} {A : PSet S α} {B : PSet S β} →
      A ⊆ B ↔ ∀ {x} → x ∈ A → x ∈ B
  _ = ↔-intro ⊆-elim ⊆-intro

  -- We say that A is a _proper subset_ of B, denoted A ⊊ B, if A ⊆ B
  -- and A ≄ B.
  -- [note] Having A ≄ B in the definition of proper subset isn't
  -- useful in constructive mathematics, because it can't demonstrate
  -- the existence of an element that's in B but not in A. We instead
  -- give proper subsets their own record type.
  _ : {S : Setoid σ₁ σ₂} → PSet S α → PSet S β → Set (σ₁ ⊔ α ⊔ β)
  _ = _⊊_

  -- Remark 3.1.15. Because these definitions involve only the notions
  -- of equality and the "is an element of" relation, both of which
  -- already obey the axiom of substitution, the notion of subset also
  -- automatically obeys the axiom of substitution. Thus for instance
  -- if A ⊆ B and A ≃ A′, then A′ ⊆ B.
  _ : {A A′ : PSet S α} {B : PSet S β} → A ≃ A′ → A ⊆ B → A′ ⊆ B
  _ = ⊆-substᴸ

  _ : {A : PSet S α} {B B′ : PSet S β} → B ≃ B′ → A ⊆ B → A ⊆ B′
  _ = ⊆-substᴿ

  _ : {A A′ : PSet S α} {B : PSet S β} → A ≃ A′ → A ⊊ B → A′ ⊊ B
  _ = ⊊-substᴸ

  _ : {A : PSet S α} {B B′ : PSet S β} → B ≃ B′ → A ⊊ B → A ⊊ B′
  _ = ⊊-substᴿ

  -- Examples 3.1.16
  -- We have {1,2,4} ⊆ {1,2,3,4,5}, because every element of {1,2,4}
  -- is also an element of {1,2,3,4,5}.
  ⟨124⟩ = fromListℕ (1 ∷ 2 ∷ 4 ∷ [])
  124⊆12345 : ⟨124⟩ ⊆ ⟨12345⟩
  124⊆12345 = toWitness {Q = ⟨124⟩ ⊆? ⟨12345⟩} _

  -- In fact we also have {1,2,4} ⊊ {1,2,3,4,5}, since the two sets
  -- {1,2,4} and {1,2,3,4,5} are not equal.
  _ : ⟨124⟩ ⊊ ⟨12345⟩
  _ = ⊊-intro 124⊆12345 3 3∉124 3∈12345
    where
      3∉124 = toWitnessFalse {Q = 3 ∈? ⟨124⟩} _
      3∈12345 = toWitness {Q = 3 ∈? ⟨12345⟩} _

  -- Given any set A, we always have A ⊆ A
  _ : {A : PSet S α} → A ⊆ A
  _ = ⊆-refl

  -- and ∅ ⊆ A.
  _ : {A : PSet S α} → ∅ ⊆ A
  _ = ∅-⊆

  -- Proposition 3.1.17 (Sets are partially ordered by set
  -- inclusion). Let A, B, C be sets. If A ⊆ B and B ⊆ C then A ⊆ C.
  -- Exercise 3.1.4.
  _ : {A : PSet S α} {B : PSet S β} {C : PSet S χ} → A ⊆ B → B ⊆ C → A ⊆ C
  _ = ⊆-trans

  -- If A ⊆ B and B ⊆ A, then A ≃ B.
  _ : {A B : PSet S α} → A ⊆ B → B ⊆ A → A ≃ B
  _ = ⊆-antisym

  -- Finally, if A ⊊ B and B ⊊ C then A ⊊ C.
  _ : {A : PSet S α} {B : PSet S β} {C : PSet S χ} → A ⊊ B → B ⊊ C → A ⊊ C
  _ = ⊊-trans

  -- Remark 3.1.19. ...given two distinct sets, it is not in general
  -- true that one of them is a subset of the other.
  ⟨135⟩ = fromListℕ (1 ∷ 3 ∷ 5 ∷ [])
  ⟨246⟩ = fromListℕ (2 ∷ 4 ∷ 6 ∷ [])

  _ : ⟨135⟩ ⊈ ⟨246⟩
  _ = toWitnessFalse {Q = ⟨135⟩ ⊆? ⟨246⟩} _

  _ : ⟨246⟩ ⊈ ⟨135⟩
  _ = toWitnessFalse {Q = ⟨246⟩ ⊆? ⟨135⟩} _

  -- Axiom 3.6 (Axiom of specification). Let A be a set, and for each
  -- x ∈ A, let P(x) be a property pertaining to x (i.e., P(x) is
  -- either a true statement or a false statement). Then there exists
  -- a set, called {x ∈ A : P(x) is true} (or simply {x ∈ A : P(x)}
  -- for short), whose elements are precisely the elements x in A for
  -- which P(x) is true.

  -- [note] We modify the above axiom slightly for a better fit with
  -- type theory. Let S be a setoid with carrier type El S, and for
  -- each x : El S, let (P ⟨$⟩ x) : Set be a property pertaining to x
  -- that respects the equivalence relation on S.  Then there exists a
  -- PSet₀ S, called ⟨ P ⟩, whose elements are precisely the elements
  -- x in El S for which (P ⟨$⟩ x) is inhabited. In other words, since
  -- our PSets already have an underlying "set" in the form of a
  -- setoid, the predicate can just operate on those elements rather
  -- than the elements of another PSet.
  _ : {S : Setoid₀} → SPred₀ S → PSet₀ S
  _ = ⟨_⟩

  -- Note that {x ∈ A : P(x) is true} is always a subset of A, though
  -- it could be as large as A or as small as the empty set.
  -- [note] In our formulation, since A is a type (El S) and not a
  -- set, we can't show that comprehension makes a subset of A
  -- directly, but we can first show how to make a set of the entire
  -- type A, and then show that comprehension always gives a subset of
  -- that.
  universe : {S : Setoid₀} → PSet₀ S
  universe = ⟨ SPred-const ⊤ ⟩

  _ : {S : Setoid₀} → ⟨ SPred-const ⊥ ⟩ ≃ (∅ {S = S})
  _ = A⊆∅→A≃∅ (⊆-intro (⊥-elim ∘ x∈⟨P⟩-elim))

  _ : {S : Setoid₀} {P : SPred₀ S} → ⟨ P ⟩ ⊆ universe
  _ = ⊆-intro (const (x∈⟨P⟩-intro ⊤-intro))

  -- One can verify that the axiom of substitution works for
  -- specification, thus if A = A′ then {x ∈ A : P(x)} = {x ∈ A′ :
  -- P(x)}.
  -- [note] Again, because in our version A is not a set, we can't
  -- verify this, nor is there a need to.

  -- Example 3.1.21. Let S := {1,2,3,4,5}. Then the set
  -- {n ∈ S : n < 4} is the set of those elements n in S for which
  -- n < 4 is true, i.e., {n ∈ S : n < 4} = {1,2,3}. Similarly,
  -- the set {n ∈ S : n < 7} is the same as S itself, while
  -- {n ∈ S : n < 1} is the empty set.

  -- [note] We could define these sets with our version of
  -- specification, using logical conjunction:
  -- ⟨ record
  --   { _⟨$⟩_ = λ n → n ∈ S ∧ n < 4
  --   ; cong = λ { refl → equivalence-id }
  --   } ⟩
  -- But since set intersections are also defined using conjunction,
  -- it would be clearer to wait until they are defined below. For
  -- now, we will use specification to build the predicate portion of
  -- the sets.
  ℕ⟨_⟩ : (ℕ → Set) → ℕSet
  ℕ⟨ P ⟩ = ⟨ record { _⟨$⟩_ = P ; cong = λ { refl → equivalence-id } } ⟩

  ⟨n<4⟩ = ℕ⟨ _< 4 ⟩
  ⟨n<7⟩ = ℕ⟨ _< 7 ⟩
  ⟨n<1⟩ = ℕ⟨ _< 1 ⟩

  -- Definition 3.1.22 (Intersections). The _intersection_ S₁ ∩ S₂ of
  -- two sets is defined to be the set S₁ ∩ S₂ ≔ {x ∈ S₁ : x ∈ S₂}. In
  -- other words, S₁ ∩ S₂ consists of all the elements which belong to
  -- both S₁ and S₂.
  -- [note] While we could define intersection in terms of
  -- specification, by defining its predicate to be
  -- P x = x ∈ S₁ ∧ x ∈ S₂, we instead take the axiomatic
  -- approach to provide symmetry with union.
  _ : PSet S α → PSet S β → PSet S (α ⊔ β)
  _ = _∩_

  -- Thus, for all objects x, x ∈ S₁ ∩ S₂ ↔ x ∈ S₁ and x ∈ S₂.
  _ :
    {S : Setoid σ₁ σ₂} {S₁ : PSet S α} {S₂ : PSet S β} →
      ∀ {x} → x ∈ S₁ ∩ S₂ ↔ x ∈ S₁ ∧ x ∈ S₂
  _ = x∈A∩B↔x∈A∧x∈B

  -- Remark 3.1.23. Note that this definition is well-defined (i.e.,
  -- it obeys the axiom of substitution)...
  _ : {A A′ : PSet S α} {B : PSet S β} → A ≃ A′ → A ∩ B ≃ A′ ∩ B
  _ = ∩-substᴸ

  _ : {A : PSet S α} {B B′ : PSet S β} → B ≃ B′ → A ∩ B ≃ A ∩ B′
  _ = ∩-substᴿ

  -- Examples 3.1.24
  ⟨234⟩ = fromListℕ (2 ∷ 3 ∷ 4 ∷ [])
  ⟨24⟩ = fromListℕ (2 ∷ 4 ∷ [])
  ⟨34⟩ = fromListℕ (3 ∷ 4 ∷ [])

  _ : ⟨124⟩ ∩ ⟨234⟩ ≃ ⟨24⟩
  _ = toWitness {Q = ⟨124⟩ ∩ ⟨234⟩ ≃? ⟨24⟩} _

  _ : ⟨12⟩ ∩ ⟨34⟩ ≃ ∅
  _ = toWitness {Q = ⟨12⟩ ∩ ⟨34⟩ ≃? ∅} _

  _ : ⟨23⟩ ∪ ∅ ≃ ⟨23⟩
  _ = ∪-∅ᴿ

  _ : ⟨23⟩ ∩ ∅ ≃ ∅
  _ = ∩-∅ᴿ

  -- Example 3.1.21 [revisited].
  instance
    <-dec : ∀ {n m} → Dec (n < m)
    <-dec {n} {m} = n <? m

  _ : ⟨12345⟩ ∩ ⟨n<4⟩ ≃ ⟨123⟩
  _ = toWitness {Q = ⟨12345⟩ ∩ ⟨n<4⟩ ≃? ⟨123⟩} _

  _ : ⟨12345⟩ ∩ ⟨n<7⟩ ≃ ⟨12345⟩
  _ = toWitness {Q = ⟨12345⟩ ∩ ⟨n<7⟩ ≃? ⟨12345⟩} _

  _ : ⟨12345⟩ ∩ ⟨n<1⟩ ≃ ∅
  _ = toWitness {Q = ⟨12345⟩ ∩ ⟨n<1⟩ ≃? ∅} _

  -- Definition 3.1.26 (Difference sets). Given two sets A and B, we
  -- define the set A - B or A ∖ B to be the set A with any elements
  -- of B removed
  _ : PSet S α → PSet S β → PSet S (α ⊔ β)
  _ = _∖_

  -- For instance, {1,2,3,4} ∖ {2,4,6} = {1,3}.
  ⟨1234⟩ = fromListℕ (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ⟨13⟩ = fromListℕ (1 ∷ 3 ∷ [])
  _ : ⟨1234⟩ ∖ ⟨246⟩ ≃ ⟨13⟩
  _ = toWitness {Q = ⟨1234⟩ ∖ ⟨246⟩ ≃? ⟨13⟩} _

  -- Proposition 3.1.27 (Sets form a boolean algebra).
  -- Exercise 3.1.6
  module _ (A B C X : PSet₀ S) (A⊆X : A ⊆ X) (B⊆X : B ⊆ X) (C⊆X : C ⊆ X) where
    -- (a) (Minimal element)
    _ : A ∪ ∅ ≃ A
    _ = ∪-∅ᴿ

    _ : A ∩ ∅ ≃ ∅
    _ = ∩-∅ᴿ

    -- (b) (Maximal element)
    _ : A ∪ X ≃ X
    _ = ⊆-antisym (⊆-intro forward) (⊆-intro x∈A∪B-introᴿ)
      where
        forward : ∀ {x} → x ∈ A ∪ X → x ∈ X
        forward x∈A∪X with x∈A∪B-elim x∈A∪X
        ... | ∨-introᴸ x∈A = ⊆-elim A⊆X x∈A
        ... | ∨-introᴿ x∈X = x∈X

    _ : A ∩ X ≃ A
    _ = ⊆-antisym (⊆-intro x∈A∩B-elimᴸ) (⊆-intro backward)
      where
        backward : ∀ {x} → x ∈ A → x ∈ A ∩ X
        backward x∈A = x∈A∩B-intro₂ x∈A (⊆-elim A⊆X x∈A)

    -- (c) (Identity)
    _ : A ∩ A ≃ A
    _ = ∩-idempotent

    _ : A ∪ A ≃ A
    _ = ⊆-antisym (⊆-intro (∨-merge ∘ x∈A∪B-elim)) (⊆-intro x∈A∪B-introᴸ)

    -- (d) (Commutativity)
    _ : A ∪ B ≃ B ∪ A
    _ = ∪-comm

    _ : A ∩ B ≃ B ∩ A
    _ = ∩-comm

    -- (e) (Associativity)
    _ : (A ∪ B) ∪ C ≃ A ∪ (B ∪ C)
    _ = ∪-assoc

    _ : (A ∩ B) ∩ C ≃ A ∩ (B ∩ C)
    _ = ∩-assoc

    -- (f) (Distributivity)
    _ : A ∩ (B ∪ C) ≃ (A ∩ B) ∪ (A ∩ C)
    _ = ∩-over-∪ᴸ

    _ : A ∪ (B ∩ C) ≃ (A ∪ B) ∩ (A ∪ C)
    _ = ∪-over-∩ᴸ

    -- (g) (Partition)
    -- [note] This direction is easy, since we know both A ⊆ X and X ∖ A ⊆ X.
    A∪[X∖A]⊆X : A ∪ (X ∖ A) ⊆ X
    A∪[X∖A]⊆X = ∪⊆-intro₂ A⊆X A∖B⊆A

    -- [note] This direction is easy in classical logic because LEM
    -- holds, so we know that either x ∈ A or x ∉ A without knowing
    -- which one is the case. But we can't get away with that in type
    -- theory: to show x ∈ A ∨ x ∉ A, we must have an actual term that
    -- provides evidence of one of the two cases. So we need to add
    -- the assumption that x ∈ A is decidable (i.e., obeys LEM).  From
    -- a computational perspective this makes sense: suppose X is ℝ²
    -- and A is some fractal set such as the Mandelbrot set or the
    -- Sierpiński triangle. Then determining whether some point x : ℝ²
    -- is inside A could require computing x to an arbitrary number of
    -- decimal places. Even if those situations end up being
    -- decidable, there might be others where we don't yet know an
    -- algorithm for determining membership in all cases.
    X⊆A∪[X∖A] : {{_ : DecMembership A}} → X ⊆ A ∪ (X ∖ A)
    X⊆A∪[X∖A] = ⊆-intro backward
      where
        backward : ∀ {x} → x ∈ X → x ∈ A ∪ (X ∖ A)
        backward {x} x∈X with x ∈? A
        ... | yes x∈A = x∈A∪B-introᴸ x∈A
        ... | no x∉A = x∈A∪B-introᴿ (x∈A∖B-intro₂ x∈X x∉A)

    -- [note] Because we needed the DecMembership assumption for the
    -- second case, we need it for the full proof as well.
    A∪[X∖A]≃X : {{_ : DecMembership A}} → A ∪ (X ∖ A) ≃ X
    A∪[X∖A]≃X = ⊆-antisym A∪[X∖A]⊆X X⊆A∪[X∖A]

    _ : A ∩ (X ∖ A) ≃ ∅
    _ = ⊆-antisym (⊆-intro forward) (⊆-intro (⊥-elim ∘ x∉∅))
      where
        forward : ∀ {x} → x ∈ A ∩ (X ∖ A) → x ∈ ∅
        forward x∈A∩[X∖A] =
          let ∧-intro x∈A x∈X∖A = x∈A∩B-elim x∈A∩[X∖A]
           in ⊥-elim (x∈A∖B-elimᴿ x∈X∖A x∈A)

    -- (h) (De Morgan laws)
    X∖[A∪B]⊆[X∖A]∩[X∖B] : X ∖ (A ∪ B) ⊆ X ∖ A ∩ X ∖ B
    X∖[A∪B]⊆[X∖A]∩[X∖B] = ⊆-intro forward
      where
        forward : ∀ {x} → x ∈ X ∖ (A ∪ B) → x ∈ X ∖ A ∩ X ∖ B
        forward x∈X∖[A∪B] =
          let ∧-intro x∈X x∉A∪B = x∈A∖B-elim x∈X∖[A∪B]
              x∈X∖A = x∈A∖B-intro₂ x∈X (x∉A∪B ∘ x∈A∪B-introᴸ)
              x∈X∖B = x∈A∖B-intro₂ x∈X (x∉A∪B ∘ x∈A∪B-introᴿ)
           in x∈A∩B-intro₂ x∈X∖A x∈X∖B

    [X∖A]∩[X∖B]⊆X∖[A∪B] : X ∖ A ∩ X ∖ B ⊆ X ∖ (A ∪ B)
    [X∖A]∩[X∖B]⊆X∖[A∪B] = ⊆-intro backward
      where
        backward : ∀ {x} → x ∈ X ∖ A ∩ X ∖ B → x ∈ X ∖ (A ∪ B)
        backward x∈[X∖A]∩[X∖B] =
          let ∧-intro x∈X∖A x∈X∖B = x∈A∩B-elim x∈[X∖A]∩[X∖B]
              ∧-intro x∈X x∉A = x∈A∖B-elim x∈X∖A
              x∉B = x∈A∖B-elimᴿ x∈X∖B
           in x∈A∖B-intro₂ x∈X (∨-rec x∉A x∉B ∘ x∈A∪B-elim)

    X∖[A∪B]≃[X∖A]∩[X∖B] : X ∖ (A ∪ B) ≃ X ∖ A ∩ X ∖ B
    X∖[A∪B]≃[X∖A]∩[X∖B] = ⊆-antisym X∖[A∪B]⊆[X∖A]∩[X∖B] [X∖A]∩[X∖B]⊆X∖[A∪B]

    X∖[A∩B]⊆[X∖A]∪[X∖B] :
      {{_ : DecMembership A}} {{_ : DecMembership B}} →
        X ∖ (A ∩ B) ⊆ X ∖ A ∪ X ∖ B
    X∖[A∩B]⊆[X∖A]∪[X∖B] = ⊆-intro forward
      where
        forward : ∀ {x} → x ∈ X ∖ (A ∩ B) → x ∈ X ∖ A ∪ X ∖ B
        forward {x} x∈X∖[A∩B] with x ∈? A | x ∈? B
        ... | yes x∈A | yes x∈B =
          let ∧-intro x∈X x∉A∩B = x∈A∖B-elim x∈X∖[A∩B]
           in ⊥-elim (x∉A∩B (x∈A∩B-intro₂ x∈A x∈B))
        ... | yes x∈A | no x∉B =
          x∈A∪B-introᴿ (x∈A∖B-intro₂ (x∈A∖B-elimᴸ x∈X∖[A∩B]) x∉B)
        ... | no x∉A | _ =
          x∈A∪B-introᴸ (x∈A∖B-intro₂ (x∈A∖B-elimᴸ x∈X∖[A∩B]) x∉A)

    [X∖A]∪[X∖B]⊆X∖[A∩B] : X ∖ A ∪ X ∖ B ⊆ X ∖ (A ∩ B)
    [X∖A]∪[X∖B]⊆X∖[A∩B] = ⊆-intro backward
      where
        backward : ∀ {x} → x ∈ X ∖ A ∪ X ∖ B → x ∈ X ∖ (A ∩ B)
        backward {x} x∈[X∖A]∪[X∖B] with x∈A∪B-elim x∈[X∖A]∪[X∖B]
        ... | ∨-introᴸ x∈X∖A =
          let ∧-intro x∈X x∉A = x∈A∖B-elim x∈X∖A
           in x∈A∖B-intro₂ x∈X (x∉A ∘ x∈A∩B-elimᴸ)
        ... | ∨-introᴿ x∈X∖B =
          let ∧-intro x∈X x∉B = x∈A∖B-elim x∈X∖B
           in x∈A∖B-intro₂ x∈X (x∉B ∘ x∈A∩B-elimᴿ)

    X∖[A∩B]≃[X∖A]∪[X∖B] :
      {{_ : DecMembership A}} {{_ : DecMembership B}} →
        X ∖ (A ∩ B) ≃ X ∖ A ∪ X ∖ B
    X∖[A∩B]≃[X∖A]∪[X∖B] = ⊆-antisym X∖[A∩B]⊆[X∖A]∪[X∖B] [X∖A]∪[X∖B]⊆X∖[A∩B]

  -- Axiom 3.7 (Replacement). Let A be a set. For any object x ∈ A,
  -- and any object y, suppose we have a statement P(x, y) pertaining
  -- to x and y, such that for each x ∈ A there is at most one y for
  -- which P(x, y) is true. Then there exists a set {y : P(x, y) is
  -- true for some x ∈ A}
  _ :
    {S T : Setoid₀} (P : SRel₀ S T) (A : PSet₀ S) → ReplProp {T = T} {A} P →
      PSet₀ T
  _ = replacement

  -- such that for any object z, z ∈ {y : P(x, y) is true for some x ∈ A} ↔
  -- P(x, z) is true for some x ∈ A
  _ :
    {S T : Setoid₀} {z : El T}
      {A : PSet₀ S} {P : SRel₀ S T} {rp : ReplProp {T = T} P} →
        z ∈ replacement {T = T} P A rp ↔ ReplMembership {T = T} {A} z P
  _ = x∈rep↔Pax

  -- Example 3.1.30. Let A := {3,5,9}, and let P(x,y) be the statement
  -- y = step x, i.e., y is the successor of x. Observe that for every
  -- x ∈ A, there is exactly one y for which P(x,y) is true --
  -- specifically, the successor of x. Thus, the above axiom asserts
  -- that the set {y : y = step x for some x ∈ {3,5,9}} exists; in
  -- this case, it is clearly the same set as {4,6,10}.
  ⟨359⟩ = fromListℕ (3 ∷ 5 ∷ 9 ∷ [])
  ⟨46A⟩ = fromListℕ (4 ∷ 6 ∷ 10 ∷ [])

  step-P : SRel₀ ℕ-Setoid ℕ-Setoid
  step-P = record
    { _⟨$⟩_ = λ x → record
      { _⟨$⟩_ = λ y → y ≡ step x
      ; cong = λ { refl → equivalence-id }
      }
    ; cong = λ { refl refl → equivalence-id }
    }

  step-P-prop : ReplProp {T = ℕ-Setoid} {A = ⟨359⟩} step-P
  step-P-prop = record { P-most = λ _ y≡x z≡x → trans y≡x (sym z≡x) }

  instance
    y≡?sx : ∀ {x y} → Dec (y ≡ step x)
    y≡?sx {x} {y} = dec-map sym sym (step x ≡? y)

    step-P-fun : ReplFun {T = ℕ-Setoid} {A = ⟨359⟩} step-P
    step-P-fun = record { f = step ; Pf = const refl }

  _ : replacement step-P ⟨359⟩ step-P-prop ≃ ⟨46A⟩
  _ = toWitness {Q = replacement step-P ⟨359⟩ step-P-prop ≃? ⟨46A⟩} _

  -- TODO: remaining examples of replacement

  -- Exercise 3.1.1.
  module _ {S : Setoid₀} where
    open Setoid S using (_≈_) renaming (sym to ≈-sym; trans to ≈-trans)

    ex3-1-1 :
      {a b c d : El S} → pair {S = S} a b ≃ pair c d →
        a ≈ c ∧ b ≈ d ∨ a ≈ d ∧ b ≈ c
    ex3-1-1 {a} ab≃cd
      with x∈pab-elimᴸ (≃-elimᴸ ab≃cd a∈pab) | x∈pab-elimᴸ (≃-elimᴸ ab≃cd b∈pab)
    ex3-1-1 ab≃cd | ∨-introᴸ a≈c | ∨-introᴸ b≈c
      with x∈pab-elimᴿ (≃-elimᴿ ab≃cd b∈pab)
    ex3-1-1 ab≃cd | ∨-introᴸ a≈c | ∨-introᴸ b≈c | ∨-introᴸ a≈d =
      ∨-introᴿ (∧-intro a≈d b≈c)
    ex3-1-1 ab≃cd | ∨-introᴸ a≈c | ∨-introᴸ b≈c | ∨-introᴿ b≈d =
      ∨-introᴸ (∧-intro a≈c b≈d)
    ex3-1-1 ab≃cd | ∨-introᴸ a≈c | ∨-introᴿ b≈d =
      ∨-introᴸ (∧-intro a≈c b≈d)
    ex3-1-1 ab≃cd | ∨-introᴿ a≈d | ∨-introᴸ b≈c =
      ∨-introᴿ (∧-intro a≈d b≈c)
    ex3-1-1 ab≃cd | ∨-introᴿ a≈d | ∨-introᴿ b≈d
      with x∈pab-elimᴿ (≃-elimᴿ ab≃cd a∈pab)
    ex3-1-1 ab≃cd | ∨-introᴿ a≈d | ∨-introᴿ b≈d | ∨-introᴸ a≈c =
      ∨-introᴸ (∧-intro a≈c b≈d)
    ex3-1-1 ab≃cd | ∨-introᴿ a≈d | ∨-introᴿ b≈d | ∨-introᴿ b≈c =
      ∨-introᴿ (∧-intro a≈d b≈c)

  -- Exercise 3.1.2 (see Examples 3.1.9).
  -- Exercise 3.1.3 (see Lemma 3.1.12).
  -- Exercise 3.1.4 (see Proposition 3.1.17).

  -- Exercise 3.1.5. Let A, B be sets. Show that the three statements
  -- A ⊆ B, A ∪ B ≃ B, A ∩ B ≃ A are logically equivalent (any one of
  -- them implies the other two).
  module _ {S : Setoid₀} {A B : PSet₀ S} where
    1→2 : A ⊆ B → A ∪ B ≃ B
    1→2 A⊆B = ⊆-antisym (∪⊆-intro₂ A⊆B ⊆-refl) (∪⊆-elimᴿ ⊆-refl)

    1→3 : A ⊆ B → A ∩ B ≃ A
    1→3 A⊆B = ⊆-antisym ∩⊆-introᴸ (⊆-substᴸ ∩-idempotent (∩-preserves-⊆ᴸ A⊆B))

    2→1 : A ∪ B ≃ B → A ⊆ B
    2→1 A∪B≃B = ∪⊆-elimᴸ (≃→⊆ᴸ A∪B≃B)

    2→3 : A ∪ B ≃ B → A ∩ B ≃ A
    2→3 = 1→3 ∘ 2→1

    3→1 : A ∩ B ≃ A → A ⊆ B
    3→1 A∩B≃A = ⊆-trans (≃→⊆ᴿ A∩B≃A) ∩⊆-introᴿ

    3→2 : A ∩ B ≃ A → A ∪ B ≃ B
    3→2 = 1→2 ∘ 3→1

  -- Exercise 3.1.6 (see Proposition 3.1.27).

  -- Exercise 3.1.7.
  module _ {A B C : PSet₀ S} where
    _ : A ∩ B ⊆ A
    _ = ∩⊆-introᴸ

    _ : A ∩ B ⊆ B
    _ = ∩⊆-introᴿ

    _ : C ⊆ A ∧ C ⊆ B ↔ C ⊆ A ∩ B
    _ = ↔-intro (uncurry ⊆∩-intro₂) ⊆∩-elim

    _ : A ⊆ A ∪ B
    _ = ⊆∪-introᴸ

    _ : B ⊆ A ∪ B
    _ = ⊆∪-introᴿ

    _ : A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C
    _ = ↔-intro (uncurry ∪⊆-intro₂) ∪⊆-elim

  -- Exercise 3.1.8.
  module _ {A B : PSet₀ S} where
    _ : A ∩ (A ∪ B) ≃ A
    _ = ⊆-antisym ∩⊆-introᴸ (⊆∩-intro₂ ⊆-refl ⊆∪-introᴸ)

    _ : A ∪ (A ∩ B) ≃ A
    _ = ⊆-antisym (∪⊆-intro₂ ⊆-refl ∩⊆-introᴸ) ⊆∪-introᴸ

  -- Exercise 3.1.9.
  A≃X∖B : {A B X : PSet₀ S} → A ∪ B ≃ X → A ∩ B ≃ ∅ → A ≃ X ∖ B
  A≃X∖B {A = A} {B} {X} A∪B≃X A∩B≃∅ = ⊆-antisym (⊆-intro fwd) (⊆-intro rev)
    where
      fwd : ∀ {x} → x ∈ A → x ∈ X ∖ B
      fwd x∈A =
        let x∈X = ⊆-elim (⊆-trans ⊆∪-introᴸ (≃→⊆ᴸ A∪B≃X)) x∈A
            x∉B = x∉∅ ∘ ∈-substᴿ A∩B≃∅ ∘ x∈A∩B-intro₂ x∈A
         in x∈A∖B-intro₂ x∈X x∉B

      rev : ∀ {x} → x ∈ X ∖ B → x ∈ A
      rev x∈X∖B =
        let ∧-intro x∈X x∉B = x∈A∖B-elim x∈X∖B
         in ∨-forceᴸ x∉B (x∈A∪B-elim (∈-substᴿ (≃-sym A∪B≃X) x∈X))

  B≃X∖A : {A B X : PSet₀ S} → A ∪ B ≃ X → A ∩ B ≃ ∅ → B ≃ X ∖ A
  B≃X∖A A∪B≃X A∩B≃∅ = A≃X∖B (≃-trans ∪-comm A∪B≃X) (≃-trans ∩-comm A∩B≃∅)

  -- Exercise 3.1.10.
  module _ {A B : PSet₀ S} where
    _ : (A ∖ B) ∩ (A ∩ B) ≃ ∅
    _ = A⊆∅→A≃∅ (⊆-intro fwd)
      where
        fwd : ∀ {x} → x ∈ (A ∖ B) ∩ (A ∩ B) → x ∈ ∅
        fwd x∈[A∖B]∩[A∩B] =
          let ∧-intro x∈A∖B x∈A∩B = x∈A∩B-elim x∈[A∖B]∩[A∩B]
              x∈B = x∈A∩B-elimᴿ x∈A∩B
              x∉B = x∈A∖B-elimᴿ x∈A∖B
           in ⊥-elim (x∉B x∈B)

    _ : (B ∖ A) ∩ (A ∩ B) ≃ ∅
    _ = A⊆∅→A≃∅ (⊆-intro fwd)
      where
        fwd : ∀ {x} → x ∈ (B ∖ A) ∩ (A ∩ B) → x ∈ ∅
        fwd x∈[B∖A]∩[A∩B] =
          let ∧-intro x∈B∖A x∈A∩B = x∈A∩B-elim x∈[B∖A]∩[A∩B]
              x∈A = x∈A∩B-elimᴸ x∈A∩B
              x∉A = x∈A∖B-elimᴿ x∈B∖A
           in ⊥-elim (x∉A x∈A)

    _ : (A ∖ B) ∩ (B ∖ A) ≃ ∅
    _ = A⊆∅→A≃∅ (⊆-intro fwd)
      where
        fwd : ∀ {x} → x ∈ (A ∖ B) ∩ (B ∖ A) → x ∈ ∅
        fwd x∈[A∖B]∩[B∖A] =
          let ∧-intro x∈A∖B x∈B∖A = x∈A∩B-elim x∈[A∖B]∩[B∖A]
              x∈A = x∈A∖B-elimᴸ x∈A∖B
              x∉A = x∈A∖B-elimᴿ x∈B∖A
           in ⊥-elim (x∉A x∈A)

    _ :
      {{_ : DecMembership A}} {{_ : DecMembership B}} →
        (A ∖ B) ∪ (A ∩ B) ∪ (B ∖ A) ≃ A ∪ B
    _ = ⊆-antisym (⊆-intro fwd) (⊆-intro rev)
      where
        fwd : ∀ {x} → x ∈ (A ∖ B) ∪ (A ∩ B) ∪ (B ∖ A) → x ∈ A ∪ B
        fwd x∈123 with x∈A∪B-elim x∈123
        fwd x∈123 | ∨-introᴸ x∈[A∖B]∪[A∩B] with x∈A∪B-elim x∈[A∖B]∪[A∩B]
        fwd x∈123 | ∨-introᴸ x∈[A∖B]∪[A∩B] | ∨-introᴸ x∈A∖B =
          x∈A∪B-introᴸ (x∈A∖B-elimᴸ x∈A∖B)
        fwd x∈123 | ∨-introᴸ x∈[A∖B]∪[A∩B] | ∨-introᴿ x∈A∩B =
          x∈A∪B-introᴸ (x∈A∩B-elimᴸ x∈A∩B)
        fwd x∈123 | ∨-introᴿ x∈B∖A =
          x∈A∪B-introᴿ (x∈A∖B-elimᴸ x∈B∖A)

        rev : ∀ {x} → x ∈ A ∪ B → x ∈ (A ∖ B) ∪ (A ∩ B) ∪ (B ∖ A)
        rev {x} x∈A∪B with x∈A∪B-elim x∈A∪B
        rev {x} x∈A∪B | ∨-introᴸ x∈A with x ∈? B
        rev {x} x∈A∪B | ∨-introᴸ x∈A | yes x∈B =
          x∈A∪B-introᴸ (x∈A∪B-introᴿ (x∈A∩B-intro₂ x∈A x∈B))
        rev {x} x∈A∪B | ∨-introᴸ x∈A | no x∉B =
          x∈A∪B-introᴸ (x∈A∪B-introᴸ (x∈A∖B-intro₂ x∈A x∉B))
        rev {x} x∈A∪B | ∨-introᴿ x∈B with x ∈? A
        rev {x} x∈A∪B | ∨-introᴿ x∈B | yes x∈A =
          x∈A∪B-introᴸ (x∈A∪B-introᴿ (x∈A∩B-intro₂ x∈A x∈B))
        rev {x} x∈A∪B | ∨-introᴿ x∈B | no x∉A =
          x∈A∪B-introᴿ (x∈A∖B-intro₂ x∈B x∉A)
