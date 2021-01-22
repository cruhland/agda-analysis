module net.cruhland.Analysis.Chapter2 where

open import Relation.Nullary.Decidable using (False; fromWitnessFalse)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_; cast)
open import net.cruhland.axioms.DecEq using (_≃?_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (const; id)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using
  ( _∧_; ∧-intro
  ; _∨_; ∨-forceᴿ; ∨-introᴸ; ∨-introᴿ
  ; _↔_; ↔-intro
  ; ⊥-elim; ¬_
  )

module _ (PA : PeanoArithmetic) where
  open module ℕ = PeanoArithmetic PA using
    ( ℕ; ind; step; step-case; step≄zero; zero
    ; case-step; case-zero; case; _IsPred_; number; Pred; pred-intro; pred
    ; *-stepᴸ; *-stepᴿ; _^_; ^-stepᴿ; ^-zeroᴿ; Positive; +-positive
    ; +-both-zero; _≤_; _<_; _>_; _<⁺_; ≤-intro; <-intro
    )

  {- 2.1 The Peano Axioms -}

  -- Axiom 2.1. 0 is a natural number.
  _ : ℕ
  _ = 0

  -- Axiom 2.2. If n is a natural number, then (step n) is also a
  -- natural number
  _ : ℕ → ℕ
  _ = step

  _ : ℕ
  _ = step (step zero)

  -- Definition 2.1.3
  -- The digit-based representation is provided by the Peano.Literals module
  _ : 1 ≃ step zero
  _ = Eq.refl

  _ : 2 ≃ step (step zero)
  _ = Eq.refl

  _ : 3 ≃ step (step (step zero))
  _ = Eq.refl

  _ : 1 ≃ step 0
  _ = Eq.refl

  _ : 2 ≃ step 1
  _ = Eq.refl

  _ : 3 ≃ step 2
  _ = Eq.refl

  -- Proposition 2.1.4. 3 is a natural number.
  _ : ℕ
  _ = step (step (step zero))

  _ : ℕ
  _ = step 2

  _ : ℕ
  _ = 3

  -- Axiom 2.3. 0 is not the successor of any natural number.
  _ : ∀ {n} → step n ≄ 0
  _ = step≄zero

  -- Proposition 2.1.6. 4 is not equal to 0.
  4≄0 : 4 ≄ 0
  4≄0 = step≄zero

  -- Axiom 2.4. Different natural numbers must have different successors.
  _ : ∀ {n m} → step n ≃ step m → n ≃ m
  _ = AA.inject {{r = ℕ.step-injective}}

  -- Proposition 2.1.8. 6 is not equal to 2.
  6≄2 : 6 ≄ 2
  6≄2 = λ 6≃2 → 4≄0 (AA.inject (AA.inject 6≃2))

  -- Axiom 2.5 (Principle of mathematical induction).
  _ : (P : ℕ → Set) → P 0 → (∀ {k} → P k → P (step k)) → ∀ n → P n
  _ = ind

  -- Proposition 2.1.16 (Recursive definitions).
  -- Suppose for each natural number n, we have some function
  -- f_n : ℕ → ℕ from the natural numbers to the natural numbers. Let
  -- c be a natural number.
  module RecDef
      (f : (n : ℕ) → ℕ → ℕ)
      (f-subst : ∀ {n₁ n₂ m₁ m₂} → n₁ ≃ n₂ → m₁ ≃ m₂ → f n₁ m₁ ≃ f n₂ m₂)
      (c : ℕ) where

    -- Then we can assign a unique [see UniqueAssignment below]
    -- natural number a_n to each natural number n, such that...
    data _AssignedTo_ : ℕ → ℕ → Set where
      -- a_0 = c
      assign-zero :
        ∀ {n} → n ≃ zero → c AssignedTo n
      -- and a_(step n) = f_n(a_n) for each natural number n.
      assign-step :
        ∀ {a n n′} → n ≃ step n′ → a AssignedTo n′ → (f n′ a) AssignedTo n

    AssignedTo-substᴿ :
      ∀ {m n₁ n₂} → n₁ ≃ n₂ → m AssignedTo n₁ → m AssignedTo n₂
    AssignedTo-substᴿ n₁≃n₂ (assign-zero n₁≃z) =
      assign-zero (Eq.trans (Eq.sym n₁≃n₂) n₁≃z)
    AssignedTo-substᴿ n₁≃n₂ (assign-step n₁≃sn₁′ m′≔n₁′) =
      assign-step (Eq.trans (Eq.sym n₁≃n₂) n₁≃sn₁′) m′≔n₁′

    record UniqueAssignment (n : ℕ) : Set where
      constructor assign-intro
      field
        a : ℕ
        assign-exists : a AssignedTo n
        assign-unique : ∀ {b} → b AssignedTo n → a ≃ b

    rec-def : ∀ n → UniqueAssignment n
    rec-def = ind P Pz Ps
      where
        P = UniqueAssignment

        Pz : P zero
        Pz = assign-intro c (assign-zero Eq.refl) (c-unique Eq.refl)
          where
            c-unique : ∀ {m} → m ≃ zero → ∀ {b} → b AssignedTo m → c ≃ b
            c-unique m≃z (assign-zero _) =
              Eq.refl
            c-unique m≃z (assign-step m≃sm′ b′≔m′) =
              ⊥-elim (step≄zero (Eq.trans (Eq.sym m≃sm′) m≃z))

        Ps : step-case P
        Ps {k} (assign-intro a a≔k unique) =
          assign-intro (f k a) (assign-step Eq.refl a≔k) (f-unique Eq.refl)
            where
              f-unique : ∀ {m} → m ≃ step k → ∀ {b} → b AssignedTo m → f k a ≃ b
              f-unique m≃sk (assign-zero m≃z) =
                ⊥-elim (step≄zero (Eq.trans (Eq.sym m≃sk) m≃z))
              f-unique m≃sk (assign-step m≃sm′ b′≔m′) =
                let m′≃k = AA.inject (Eq.trans (Eq.sym m≃sm′) m≃sk)
                    a≃b′ = unique (AssignedTo-substᴿ m′≃k b′≔m′)
                 in f-subst (Eq.sym m′≃k) a≃b′

  {- 2.2 Addition -}

  -- Definition 2.2.1 (Addition of natural numbers).
  _ : ℕ → ℕ → ℕ
  _ = _+_ {{ℕ.plus}}

  0+m : {m : ℕ} → 0 + m ≃ m
  0+m = AA.ident {{r = ℕ.+-identityᴸ}}

  1+m : ∀ {m} → 1 + m ≃ step m
  1+m {m} =
    begin
      1 + m
    ≃⟨ AA.comm-swap ⟩
      0 + step m
    ≃⟨ AA.ident ⟩
      step m
    ∎

  2+3≃5 : 2 + 3 ≃ 5
  2+3≃5 =
    begin
      2 + 3
    ≃⟨ AA.comm-swap ⟩
      1 + 4
    ≃⟨ AA.comm-swap ⟩
      0 + 5
    ≃⟨ AA.ident ⟩
      5
    ∎

  -- Lemma 2.2.2. For any natural number n, n + 0 = n.
  _ : {n : ℕ} → n + 0 ≃ n
  _ = AA.ident {{r = ℕ.+-identityᴿ}}

  -- Lemma 2.2.3. For any natural numbers n and m, n + step m = step (n + m).
  _ : ∀ {n m} → n + step m ≃ step (n + m)
  _ = AA.commᴿ {{r = ℕ.+-commutative-stepᴿ}}

  _ : ∀ {n} → step n ≃ n + 1
  _ = ℕ.sn≃n+1

  -- Proposition 2.2.4 (Addition is commutative).
  _ : {n m : ℕ} → n + m ≃ m + n
  _ = AA.comm {{r = ℕ.+-commutative}}

  -- Proposition 2.2.5 (Addition is associative).
  -- Exercise 2.2.1
  _ : {a b c : ℕ} → (a + b) + c ≃ a + (b + c)
  _ = AA.assoc {{r = ℕ.+-associative}}

  -- Proposition 2.2.6 (Cancellation law).
  _ : {a b c : ℕ} → a + b ≃ a + c → b ≃ c
  _ = AA.cancel {{r = ℕ.+-cancellativeᴸ}}

  -- Definition 2.2.7 (Positive natural numbers).
  _ : ℕ → Set
  _ = Positive

  positive-step : ∀ {n} → Positive (step n)
  positive-step = step≄zero

  -- Proposition 2.2.8. If a is positive and b is a natural number,
  -- then a + b is positive.
  _ : ∀ {a b} → Positive a → Positive (a + b)
  _ = +-positive

  -- Corollary 2.2.9. If a and b are natural numbers such that a + b = 0,
  -- then a = 0 and b = 0.
  _ : {a b : ℕ} → a + b ≃ 0 → a ≃ 0 ∧ b ≃ 0
  _ = +-both-zero

  -- Lemma 2.2.10. Let a be a positive natural number. Then there exists
  -- exactly one natural number b such that step b = a.
  -- Exercise 2.2.2
  record UniquePred (n : ℕ) : Set where
    constructor upred-intro
    field
      pred-exists : Pred n

    open Pred pred-exists public

    field
      pred-unique : ∀ m → m IsPred n → pred-value ≃ m

  unique-predecessor : ∀ a → Positive a → UniquePred a
  unique-predecessor a a≄0 =
    let p@(pred-intro b a≃sb) = pred a≄0
     in upred-intro p (λ b′ a≃sb′ → AA.inject (Eq.trans (Eq.sym a≃sb) a≃sb′))

  -- Definition 2.2.11 (Ordering of the natural numbers).
  _ : ℕ → ℕ → Set
  _ = _≤_

  -- Using Definition 2.2.11 on some examples
  8>5 : 8 > 5
  8>5 = <-intro 5≤8 5≄8
    where
      5+3≃8 =
        begin
          5 + 3
        ≃⟨⟩
          5 + step (step (step zero))
        ≃˘⟨ AA.comm-swap ⟩
          step 5 + step (step zero)
        ≃˘⟨ AA.comm-swap ⟩
          step (step 5) + step zero
        ≃˘⟨ AA.comm-swap ⟩
          step (step (step 5)) + zero
        ≃⟨ AA.ident ⟩
          step (step (step 5))
        ≃⟨⟩
          8
        ∎
      5≤8 = ≤-intro 3 5+3≃8
      si = AA.inject
      5≄8 = λ 5≃8 → step≄zero (si (si (si (si (si (Eq.sym 5≃8))))))

  -- Proposition 2.2.12 (Basic properties of order for natural numbers).
  -- Exercise 2.2.3

  -- (a) (Order is reflexive)
  _ : ∀ {a} → a ≤ a
  _ = Eq.refl {{r = ℕ.≤-reflexive}}

  -- (b) (Order is transitive)
  _ : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
  _ = Eq.trans {{r = ℕ.≤-transitive}}

  -- (c) (Order is anti-symmetric)
  _ : ∀ {a b} → a ≤ b → b ≤ a → a ≃ b
  _ = AA.antisym {{r = ℕ.≤-antisymmetric}}

  -- (d) (Addition preserves order)
  _ : ∀ {a b c} → a ≤ b ↔ a + c ≤ b + c
  _ = ↔-intro AA.subst AA.cancel

  -- (e)
  a<b↔sa≤b : ∀ {a b} → a < b ↔ step a ≤ b
  a<b↔sa≤b {a} {b} = ↔-intro (cast {{r = ℕ.<-as-s≤}}) (cast {{r = ℕ.s≤-as-<}})

  -- (f)
  <↔<⁺ : ∀ {a b} → a < b ↔ a <⁺ b
  <↔<⁺ = ↔-intro (cast {{r = ℕ.<-as-<⁺}}) (cast {{r = ℕ.<⁺-as-<}})

  -- Proposition 2.2.13 (Trichotomy of order for natural numbers).
  _ : ∀ {a b} → AA.ExactlyOneOfThree (a < b) (a ≃ b) (a > b)
  _ = ℕ.order-trichotomy

  -- Proposition 2.2.14
  -- Exercise 2.2.5
  _ :
    (P : ℕ → Set) (b : ℕ) →
    (∀ m → b ≤ m → (∀ k → b ≤ k → k < m → P k) → P m) →
    ∀ n → b ≤ n → P n
  _ = ℕ.strong-ind

  -- Exercise 2.2.6
  backwards-ind :
    (P : ℕ → Set) → (∀ {n₁ n₂} → n₁ ≃ n₂ → P n₁ → P n₂) → ∀ {n} → P n →
    (∀ {k} → P (step k) → P k) →
    ∀ {m} → m ≤ n → P m
  backwards-ind P P-subst {n} Pn Pk m≤n = ind Q Qz Qs n Pn m≤n
    where
      Q = λ x → P x → ∀ {y} → y ≤ x → P y

      Qz : Q 0
      Qz Pz y≤z = P-subst (Eq.sym (∨-forceᴿ ℕ.n≮0 (ℕ.≤-split y≤z))) Pz

      Qs : step-case Q
      Qs Qk Psk y≤sk with ℕ.≤s-split y≤sk
      ... | ∨-introᴸ y≤k = Qk (Pk Psk) y≤k
      ... | ∨-introᴿ y≃sk = P-subst (Eq.sym y≃sk) Psk

  {- 2.3 Multiplication -}

  -- Definition 2.3.1 (Multiplication of natural numbers).
  _ : ℕ → ℕ → ℕ
  _ = _*_ {{ℕ.star}}

  0*m : {m : ℕ} → 0 * m ≃ 0
  0*m = AA.absorb {{r = ℕ.*-absorptiveᴸ}}

  1*m : {m : ℕ} → 1 * m ≃ 0 + m
  1*m {m} = Eq.trans *-stepᴸ (AA.subst 0*m)

  2*m : {m : ℕ} → 2 * m ≃ 0 + m + m
  2*m {m} = Eq.trans *-stepᴸ (AA.subst 1*m)

  -- Lemma 2.3.2 (Multiplication is commutative).
  -- Exercise 2.3.1
  _ : {n m : ℕ} → n * m ≃ m * n
  _ = AA.comm {{r = ℕ.*-commutative}}

  -- Lemma 2.3.3 (Positive natural numbers have no zero divisors).
  -- Exercise 2.3.2
  no-zero-divs : {n m : ℕ} → n * m ≃ 0 ↔ n ≃ 0 ∨ m ≃ 0
  no-zero-divs {n} {m} = ↔-intro AA.zero-prod backward
    where
      backward : n ≃ 0 ∨ m ≃ 0 → n * m ≃ 0
      backward (∨-introᴸ n≃0) = Eq.trans (AA.subst n≃0) AA.absorb
      backward (∨-introᴿ m≃0) = Eq.trans (AA.subst m≃0) AA.absorb

  -- Proposition 2.3.4 (Distributive law).
  _ : {a b c : ℕ} → a * (b + c) ≃ a * b + a * c
  _ = AA.distrib {{r = ℕ.*-distributive-+ᴸ}}

  -- Proposition 2.3.5 (Multiplication is associative).
  -- Exercise 2.3.3
  _ : {a b c : ℕ} → (a * b) * c ≃ a * (b * c)
  _ = AA.assoc {{r = ℕ.*-associative}}

  -- Proposition 2.3.6 (Multiplication preserves order).
  _ : ∀ {a b c} → a < b → c ≄ 0 → a * c < b * c
  _ = ℕ.*-preserves-<ᴿ

  -- Corollary 2.3.7 (Cancellation law).
  _ : {a b c : ℕ} → c ≄ 0 → a * c ≃ b * c → a ≃ b
  _ = λ c≄0 →
        let instance c≄ⁱ0 = fromWitnessFalse c≄0
         in AA.cancel {{r = ℕ.*-cancellativeᴿ}}

  -- Proposition 2.3.9 (Euclidean algorithm).
  -- Exercise 2.3.5
  record _DividedBy_ (n m : ℕ) : Set where
    constructor div-intro
    field
      q r : ℕ
      r<m : r < m
      n≃mq+r : n ≃ m * q + r

  euclid : ∀ n m → m ≄ 0 → n DividedBy m
  euclid n m m≄0 = ind P Pz Ps n
    where
      P = _DividedBy m

      Pz : P 0
      Pz = div-intro q r r<m n≃mq+r
        where
          q = 0
          r = 0
          r<m = <-intro ℕ.0≤n (Eq.¬sym m≄0)
          n≃mq+r = Eq.sym (Eq.trans AA.ident AA.absorb)

      Ps : step-case P
      Ps {k} (div-intro q r r<m k≃mq+r) with ℕ.≤-split (r<m as step r ≤ m)
      ... | ∨-introᴸ sr<m = div-intro q (step r) sr<m sk≃mq+sr
        where
          sk≃mq+sr = Eq.trans (AA.subst k≃mq+r) (Eq.sym AA.commᴿ)
      ... | ∨-introᴿ sr≃m = div-intro (step q) 0 0<m sk≃m[sq]+0
        where
          0<m = <-intro ℕ.0≤n (Eq.¬sym m≄0)

          sk≃m[sq]+0 =
            begin
              step k
            ≃⟨ AA.subst k≃mq+r ⟩
              step (m * q + r)
            ≃˘⟨ AA.commᴿ ⟩
              m * q + step r
            ≃⟨ AA.subst sr≃m ⟩
              m * q + m
            ≃˘⟨ *-stepᴿ ⟩
              m * step q
            ≃˘⟨ AA.ident ⟩
              m * step q + 0
            ∎

  -- Definition 2.3.11 (Exponentiation for natural numbers).
  _ : ℕ → ℕ → ℕ
  _ = _^_

  -- Examples 2.3.12
  x^0≃1 : ∀ {x} → x ^ 0 ≃ 1
  x^0≃1 = ^-zeroᴿ

  x^1≃x : ∀ {x} → x ^ 1 ≃ x
  x^1≃x {x} =
    begin
      x ^ 1
    ≃⟨ ^-stepᴿ ⟩
      x ^ 0 * x
    ≃⟨ AA.subst x^0≃1 ⟩
      1 * x
    ≃⟨ AA.ident ⟩
      x
    ∎

  x^2≃xx : ∀ {x} → x ^ 2 ≃ x * x
  x^2≃xx {x} =
    begin
      x ^ 2
    ≃⟨ ^-stepᴿ ⟩
      x ^ 1 * x
    ≃⟨ AA.subst x^1≃x ⟩
      x * x
    ∎

  x^3≃xxx : ∀ {x} → x ^ 3 ≃ x * x * x
  x^3≃xxx {x} =
    begin
      x ^ 3
    ≃⟨ ^-stepᴿ ⟩
      x ^ 2 * x
    ≃⟨ AA.subst x^2≃xx ⟩
      x * x * x
    ∎

  2x≃x+x : ∀ {x} → 2 * x ≃ x + x
  2x≃x+x {x} =
    begin
      2 * x
    ≃⟨⟩
      step 1 * x
    ≃⟨ *-stepᴸ ⟩
      1 * x + x
    ≃⟨ AA.subst AA.ident ⟩
      x + x
    ∎

  -- Exercise 2.3.4
  ex234 : ∀ {a b} → (a + b) ^ 2 ≃ a ^ 2 + 2 * a * b + b ^ 2
  ex234 {a} {b} =
    begin
      (a + b) ^ 2
    ≃⟨ x^2≃xx ⟩
      (a + b) * (a + b)
    ≃⟨ AA.distrib ⟩
      a * (a + b) + b * (a + b)
    ≃⟨ AA.distrib-twoᴸ ⟩
      a * a + a * b + (b * a + b * b)
    ≃⟨ AA.subst (AA.subst AA.comm) ⟩
      a * a + a * b + (a * b + b * b)
    ≃˘⟨ AA.assoc ⟩
      a * a + a * b + a * b + b * b
    ≃⟨ AA.subst AA.assoc ⟩
      a * a + (a * b + a * b) + b * b
    ≃˘⟨ AA.subst (AA.subst 2x≃x+x) ⟩
      a * a + 2 * (a * b) + b * b
    ≃˘⟨ AA.subst (AA.subst AA.assoc) ⟩
      a * a + 2 * a * b + b * b
    ≃˘⟨ AA.subst (AA.subst x^2≃xx) ⟩
      a ^ 2 + 2 * a * b + b * b
    ≃˘⟨ AA.subst x^2≃xx ⟩
      a ^ 2 + 2 * a * b + b ^ 2
    ∎
