open import Data.List using ([]; _∷_; _++_)
import Data.List.Membership.DecPropositional as DecMembership
open import Function using (_∘_; const; id)
open import Level using (_⊔_; Level) renaming (suc to lstep; zero to lzero)
open import Relation.Binary using (DecSetoid)
open import Relation.Binary.PropositionalEquality using (setoid; decSetoid)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sets using (SetTheory)
open import net.cruhland.models.Logic using
  ( _∨_; ∨-comm; ∨-introᴸ; ∨-introᴿ; ∨-merge
  ; _↔_; ↔-elimᴸ; ↔-elimᴿ; ↔-intro
  ; ⊤; ⊥; ⊥-elim; ⊤-intro
  )
open import net.cruhland.models.Peano.Unary using (peanoArithmetic)

module net.cruhland.Analysis.Chapter3.Fundamentals (ST : SetTheory) where
  open PeanoArithmetic peanoArithmetic using (ℕ; _≡?_)

  open SetTheory ST using
    ( _∈_; _∉_; _≃_; _≄_; El; ≃-intro; PSet; PSet-Setoid; Setoid
    ; ≃-elimᴸ; ≃-refl; ∈-substᴸ; ∈-substᴿ; ≃-sym; ≃-trans
    ; ∅; x∉∅; ∅-unique
    ; singleton; singleton-unique; a∈sa; x∈sa↔a≈x; x∈sa-elim; x∈sa-intro
    ; pair; x∈pab↔a≈x∨b≈x; a∈pab; x∈pab-elim
    ; x∈pab-intro; x∈pab-introᴸ; x∈pab-introᴿ; pair-unique
    ; _∪_; x∈A∪B↔x∈A∨x∈B; ∪-∅ᴸ; ∪-∅ᴿ; ∪-assoc; ∪-comm; x∈A∪B-elim
    ; x∈A∪B-introᴸ; x∈A∪B-introᴿ; ∪-substᴸ; ∪-substᴿ
    ; _⊆_; _⊈_; _⊊_; ∅-⊆; ⊆-antisym; ⊆-elim; ⊆-intro; ⊊-intro
    ; ⊆-refl; ⊆-substᴸ; ⊆-substᴿ; ⊊-substᴸ; ⊊-substᴿ; ⊆-trans; ⊊-trans
    ; ⟨_~_⟩; x∈⟨P⟩↔Px; congProp; x∈⟨P⟩-elim; x∈⟨P⟩-intro
    ; finite; module Memberᴸ; module Subsetᴸ; ∪-finite
    )

  variable
    σ₁ σ₂ α β χ : Level
    S : Setoid σ₁ σ₂

  ℕ-Setoid : Setoid lzero lzero
  ℕ-Setoid = setoid ℕ

  ℕ-DecSetoid : DecSetoid lzero lzero
  ℕ-DecSetoid = decSetoid _≡?_

  open Memberᴸ {DS = ℕ-DecSetoid} using (_∈?_)
  open Subsetᴸ {DS = ℕ-DecSetoid} using (_⊆?_; _≃?_)

  {- 3.1 Fundamentals -}

  -- Definition 3.1.1. (Informal) We define a _set_ A to be any
  -- unordered collection of objects
  _ : Setoid σ₁ σ₂ → ∀ α → Set (σ₁ ⊔ σ₂ ⊔ lstep α)
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
  _ : PSet (setoid (ℕ ∨ PSet ℕ-Setoid lzero)) (lstep lzero)
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
  -- _equal_, A ≃ B, iff every element of A is an element of B and
  -- vice versa.
  _ : {S : Setoid σ₁ σ₂} → PSet S α → PSet S α → Set (σ₁ ⊔ α)
  _ = _≃_

  -- Example 3.1.5
  [34215] = 3 ∷ 4 ∷ 2 ∷ 1 ∷ 5 ∷ []
  _ : ⟨12345⟩ ≃ finite [34215]
  _ = toWitness {Q = [12345] ≃? [34215]} _

  [3315242] = 3 ∷ 3 ∷ 1 ∷ 5 ∷ 2 ∷ 4 ∷ 2 ∷ []
  _ : ⟨12345⟩ ≃ finite [3315242]
  _ = toWitness {Q = [12345] ≃? [3315242]} _

  -- [note] informal examples given prior to Definition 3.1.4
  [2358] = 2 ∷ 3 ∷ 5 ∷ 8 ∷ []
  _ : ⟨3852⟩ ≃ finite [2358]
  _ = toWitness {Q = [3852] ≃? [2358]} _

  [38521] = 3 ∷ 8 ∷ 5 ∷ 2 ∷ 1 ∷ []
  _ : ⟨3852⟩ ≄ finite [38521]
  _ = toWitnessFalse {Q = [3852] ≃? [38521]} _

  [385] = 3 ∷ 8 ∷ 5 ∷ []
  _ : ⟨3852⟩ ≄ finite [385]
  _ = toWitnessFalse {Q = [3852] ≃? [385]} _

  -- Exercise 3.1.1
  -- One can easily verify that this notion of equality is reflexive,
  -- symmetric, and transitive.
  _ : {A : PSet S α} → A ≃ A
  _ = ≃-refl

  _ : {A B : PSet S α} → A ≃ B → B ≃ A
  _ = ≃-sym

  _ : {A B C : PSet S α} → A ≃ B → B ≃ C → A ≃ C
  _ = ≃-trans

  -- Observe that if x ∈ A and A ≃ B, then x ∈ B, by Definition
  -- 3.1.4. This the "is an element of" relation _∈_ obeys the axiom
  -- of substitution.
  _ : {S : Setoid σ₁ σ₂} {A B : PSet S α} {x : El S} → A ≃ B → x ∈ A → x ∈ B
  _ = ∈-substᴿ

  -- [note] Tao only mentions substitution for the right-hand side of
  -- _∈_, but it's also important that it works for the left-hand
  -- side:
  _ : {A B : PSet S α} {C : PSet (PSet-Setoid S α) β} → A ≃ B → A ∈ C → B ∈ C
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
  _ : {S : Setoid σ₁ σ₂} {∅′ : PSet S α} → (∀ {x} → x ∉ ∅′) → ∅ ≃ ∅′
  _ = ∅-unique

  -- Lemma 3.1.6 (Single choice). Let A be a non-empty set. Then there
  -- exists an object x such that x ∈ A.
  -- [note] This is not provable in Agda because it's nonconstructive.
  -- Instead of using evidence that a set is not equal to the empty
  -- set, we will need to use direct evidence that an element of a set
  -- exists.

  -- Axiom 3.3 (Singleton sets and pair sets). If a is an object, then
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

  -- Remarks 3.1.9
  -- Just as there is only one empty set, there is only one singleton
  -- set for each object a, thanks to Definition 3.1.4.
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

  -- Also, Definition 3.1.4 ensures that pair a b ≃ pair b a
  pair-comm : {S : Setoid σ₁ σ₂} {a b : El S} → pair {S = S} a b ≃ pair b a
  pair-comm {S = S} = ⊆-antisym ab⊆ba ba⊆ab
    where
      ab⊆ba = ⊆-intro (x∈pab-intro ∘ ∨-comm ∘ x∈pab-elim)
      ba⊆ab = ⊆-intro (x∈pab-intro ∘ ∨-comm ∘ x∈pab-elim)

  -- and pair a a ≃ singleton a.
  pair-singleton :
    {S : Setoid σ₁ σ₂} {a : El S} → pair {S = S} a a ≃ singleton a
  pair-singleton = ⊆-antisym paa⊆sa sa⊆paa
    where
      paa⊆sa = ⊆-intro (x∈sa-intro ∘ ∨-merge ∘ x∈pab-elim)
      sa⊆paa = ⊆-intro (x∈pab-introᴸ ∘ x∈sa-elim)

  -- Examples 3.1.10
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

  -- Axiom 3.4 (Pairwise union). Given any two sets A, B, there exists
  -- a set A ∪ B, called the _union_ A ∪ B of A and B, whose elements
  -- consist of all the elements which belong to A or B or both.
  _ : PSet S α → PSet S β → PSet S (α ⊔ β)
  _ = _∪_

  -- In other words, for any object x, x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B.
  _ :
    {S : Setoid σ₁ σ₂} {A : PSet S α} {B : PSet S β} →
      ∀ {x} → x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B
  _ = x∈A∪B↔x∈A∨x∈B

  -- Example 3.1.11
  [12] = 1 ∷ 2 ∷ []
  [23] = 2 ∷ 3 ∷ []
  [123] = 1 ∷ 2 ∷ 3 ∷ []
  _ : finite {S = ℕ-Setoid} [12] ∪ finite [23] ≃ finite [123]
  _ = ≃-trans (∪-finite [12] [23]) (toWitness {Q = [12] ++ [23] ≃? [123]} _)

  -- Remark 3.1.12. If A, B, A′ are sets, and A is equal to A′, then A
  -- ∪ B is equal to A′ ∪ B.
  _ : {A A′ : PSet S α} {B : PSet S β} → A ≃ A′ → A ∪ B ≃ A′ ∪ B
  _ = ∪-substᴸ

  -- Similarly if B′ is a set which is equal to B, then A ∪ B is equal
  -- to A ∪ B′. Thus the operation of union obeys the axiom of
  -- substitution, and is thus well-defined on sets.
  _ : {A : PSet S α} {B B′ : PSet S β} → B ≃ B′ → A ∪ B ≃ A ∪ B′
  _ = ∪-substᴿ

  -- Lemma 3.1.13.
  -- If a and b are objects, then pair a b ≃ singleton a ∪ singleton b.
  pab≃sa∪sb :
    {S : Setoid σ₁ σ₂} {a b : El S} →
      pair a b ≃ singleton {S = S} a ∪ singleton b
  pab≃sa∪sb {S = S} {a} {b} = ⊆-antisym (⊆-intro forward) (⊆-intro backward)
    where
      open Setoid S using (_≈_)

      forward : ∀ {x} → x ∈ pair a b → x ∈ singleton a ∪ singleton b
      forward x∈pab with x∈pab-elim x∈pab
      ... | ∨-introᴸ x≈a = x∈A∪B-introᴸ (x∈sa-intro x≈a)
      ... | ∨-introᴿ x≈b = x∈A∪B-introᴿ (x∈sa-intro x≈b)

      backward : ∀ {x} → x ∈ singleton a ∪ singleton b → x ∈ pair a b
      backward x∈sa∪sb with x∈A∪B-elim x∈sa∪sb
      ... | ∨-introᴸ x∈sa = x∈pab-introᴸ (x∈sa-elim x∈sa)
      ... | ∨-introᴿ x∈sb = x∈pab-introᴿ (x∈sa-elim x∈sb)

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

  -- Definition 3.1.15 (Subsets). Let A, B be sets. We say that A is a
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

  -- Remark 3.1.16. Because these definitions involve only the notions
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

  -- Examples 3.1.17
  -- We have {1,2,4} ⊆ {1,2,3,4,5}, because every element of {1,2,4}
  -- is also an element of {1,2,3,4,5}.
  [124] = 1 ∷ 2 ∷ 4 ∷ []
  ⟨124⟩ = finite {S = ℕ-Setoid} [124]
  124⊆12345 : ⟨124⟩ ⊆ ⟨12345⟩
  124⊆12345 = toWitness {Q = [124] ⊆? [12345]} _

  -- In fact we also have {1,2,4} ⊊ {1,2,3,4,5}, since the two sets
  -- {1,2,4} and {1,2,3,4,5} are not equal.
  _ : ⟨124⟩ ⊊ ⟨12345⟩
  _ = ⊊-intro 124⊆12345 3 3∉124 3∈12345
    where
      3∉124 = toWitnessFalse {Q = 3 ∈? [124]} _
      3∈12345 = toWitness {Q = 3 ∈? [12345]} _

  -- Given any set A, we always have A ⊆ A
  _ : {A : PSet S α} → A ⊆ A
  _ = ⊆-refl

  -- and ∅ ⊆ A.
  _ : {A : PSet S α} → ∅ ⊆ A
  _ = ∅-⊆

  A⊆∅→A≃∅ : {A : PSet S α} → A ⊆ (∅ {α = α}) → A ≃ ∅
  A⊆∅→A≃∅ A⊆∅ = ⊆-antisym A⊆∅ ∅-⊆

  -- Proposition 3.1.18 (Sets are partially ordered by set
  -- inclusion). Let A, B, C be sets. If A ⊆ B and B ⊆ C then A ⊆ C.
  _ : {A : PSet S α} {B : PSet S β} {C : PSet S χ} → A ⊆ B → B ⊆ C → A ⊆ C
  _ = ⊆-trans

  -- If A ⊆ B and B ⊆ A, then A ≃ B.
  _ : {A B : PSet S α} → A ⊆ B → B ⊆ A → A ≃ B
  _ = ⊆-antisym

  -- Finally, if A ⊊ B and B ⊊ C then A ⊊ C.
  _ : {A : PSet S α} {B : PSet S β} {C : PSet S χ} → A ⊊ B → B ⊊ C → A ⊊ C
  _ = ⊊-trans

  -- Remark 3.1.20. ...given two distinct sets, it is not in general
  -- true that one of them is a subset of the other.
  [135] = 1 ∷ 3 ∷ 5 ∷ []
  [246] = 2 ∷ 4 ∷ 6 ∷ []
  ⟨135⟩ = finite {S = ℕ-Setoid} [135]
  ⟨246⟩ = finite {S = ℕ-Setoid} [246]

  _ : ⟨135⟩ ⊈ ⟨246⟩
  _ = toWitnessFalse {Q = [135] ⊆? [246]} _

  _ : ⟨246⟩ ⊈ ⟨135⟩
  _ = toWitnessFalse {Q = [246] ⊆? [135]} _

  -- Axiom 3.5 (Axiom of specification). Let A be a set, and for each
  -- x ∈ A, let P(x) be a property pertaining to x (i.e., P(x) is
  -- either a true statement or a false statement). Then there exists
  -- a set, called {x ∈ A : P(x) is true} (or simply {x ∈ A : P(x)}
  -- for short), whose elements are precisely the elements x in A for
  -- which P(x) is true.

  -- [note] We modify the above axiom slightly for a better fit with
  -- type theory. Let S be a setoid with carrier type El S, and for
  -- each x : El S, let P x : Set α be a property pertaining to x, and
  -- let P-cong : ∀ {x y} → x ≈ y → P x → P y be a proof that P
  -- respects the equivalence relation of S. Then there exists a
  -- PSet S α, called ⟨ P ~ P-cong ⟩, whose elements are precisely the
  -- elements x in El S for which P x is inhabited. In other words,
  -- since our PSets already have an underlying "set" in the form of a
  -- setoid, the predicate can just operate on those elements rather
  -- than the elements of another PSet.
  _ :
    let open Setoid S using (_≈_)
     in (P : El S → Set α) → (∀ {x y} → x ≈ y → P x → P y) → PSet S α
  _ = ⟨_~_⟩

  -- Note that {x ∈ A : P(x) is true} is always a subset of A, though
  -- it could be as large as A or as small as the empty set.
  -- [note] In our formulation, since A is a type (El S) and not a
  -- set, we can't show that comprehension makes a subset of A
  -- directly, but we can first show how to make a set of the entire
  -- type A, and then show that comprehension always gives a subset of
  -- that.
  universe : PSet S lzero
  universe = ⟨ const ⊤ ~ const id ⟩

  _ : ⟨ const ⊥ ~ const id ⟩ ≃ (∅ {S = S})
  _ = A⊆∅→A≃∅ (⊆-intro (⊥-elim ∘ x∈⟨P⟩-elim))

  _ :
    {S : Setoid σ₁ σ₂} {P : El S → Set α} {P-cong : congProp {S = S} P} →
      ⟨ P ~ P-cong ⟩ ⊆ universe {S = S}
  _ = ⊆-intro (const (x∈⟨P⟩-intro ⊤-intro))

  -- One can verify that the axiom of substitution works for
  -- specification, thus if A = A′ then {x ∈ A : P(x)} = {x ∈ A′ :
  -- P(x)}.
  -- [note] Again, because in our version A is not a set, we can't
  -- verify this, nor is there a need to.
