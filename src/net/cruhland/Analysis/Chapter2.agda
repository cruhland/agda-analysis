module net.cruhland.Analysis.Chapter2 where

open import Agda.Builtin.FromNat using (Number)
open import Function using (id; const)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; Eq; refl; sym; ¬sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Logic using
  ( _∧_; ∧-intro
  ; _∨_; ∨-forceᴿ; ∨-introᴸ; ∨-introᴿ
  ; _↔_; ↔-intro
  ; ⊥-elim; ¬_
  )

module _ (PA : PeanoArithmetic) where
  open PeanoArithmetic PA using
    ( ℕ; ind; step; step-case; step-inj; step≄zero; zero
    ; case-step; case-zero; case; _IsPred_; number; Pred; pred-intro; pred
    ; _+_; +-stepᴸ; +-stepᴿ; +-stepᴸ⃗ᴿ; +-stepᴿ⃗ᴸ; step≃+; +-substᴸ; +-substᴿ
    ; +-assoc; +-cancelᴸ; +-comm; +-zeroᴸ; +-zeroᴿ
    ; Positive; +-positive; +-both-zero
    ; _≤_; _<_; _>_; <→s≤; s≤→<; ≤→<∨≃; ≤s→≤∨≃s; ≤-intro; <-intro
    ; ≤-antisym; ≤-compat-+ᴰᴿ; ≤-compat-+ᵁᴿ; ≤-refl; ≤-trans; ≤-zero; <-zero
    ; _<⁺_; <→<⁺; <⁺→<; strong-ind; Trichotomy; trichotomy
    ; _*_; *-assoc; *-comm; *-oneᴸ; *-stepᴸ; *-stepᴿ; *-substᴸ; *-substᴿ
    ; *-zeroᴸ; *-zeroᴿ
    ; *-cancelᴿ; *-distrib-+ᴸ; *-distrib-+ᴿ; *-either-zero; *-preserves-<
    ; _^_; ^-stepᴿ; ^-zeroᴿ
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
  _ = refl

  _ : 2 ≃ step (step zero)
  _ = refl

  _ : 3 ≃ step (step (step zero))
  _ = refl

  _ : 1 ≃ step 0
  _ = refl

  _ : 2 ≃ step 1
  _ = refl

  _ : 3 ≃ step 2
  _ = refl

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
  _ = step-inj

  -- Proposition 2.1.8. 6 is not equal to 2.
  6≄2 : 6 ≄ 2
  6≄2 = λ 6≃2 → 4≄0 (step-inj (step-inj 6≃2))

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
      assign-zero (trans (sym n₁≃n₂) n₁≃z)
    AssignedTo-substᴿ n₁≃n₂ (assign-step n₁≃sn₁′ m′≔n₁′) =
      assign-step (trans (sym n₁≃n₂) n₁≃sn₁′) m′≔n₁′

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
        Pz = assign-intro c (assign-zero refl) (c-unique refl)
          where
            c-unique : ∀ {m} → m ≃ zero → ∀ {b} → b AssignedTo m → c ≃ b
            c-unique m≃z (assign-zero _) =
              refl
            c-unique m≃z (assign-step m≃sm′ b′≔m′) =
              ⊥-elim (step≄zero (trans (sym m≃sm′) m≃z))

        Ps : step-case P
        Ps {k} (assign-intro a a≔k unique) =
          assign-intro (f k a) (assign-step refl a≔k) (f-unique refl)
            where
              f-unique : ∀ {m} → m ≃ step k → ∀ {b} → b AssignedTo m → f k a ≃ b
              f-unique m≃sk (assign-zero m≃z) =
                ⊥-elim (step≄zero (trans (sym m≃sk) m≃z))
              f-unique m≃sk (assign-step m≃sm′ b′≔m′) =
                let m′≃k = step-inj (trans (sym m≃sm′) m≃sk)
                    a≃b′ = unique (AssignedTo-substᴿ m′≃k b′≔m′)
                 in f-subst (sym m′≃k) a≃b′

  {- 2.2 Addition -}

  -- Definition 2.2.1 (Addition of natural numbers).
  _ : ℕ → ℕ → ℕ
  _ = _+_

  0+m : ∀ {m} → 0 + m ≃ m
  0+m = +-zeroᴸ

  1+m : ∀ {m} → 1 + m ≃ step m
  1+m {m} =
    begin
      1 + m
    ≃⟨ +-stepᴸ⃗ᴿ ⟩
      0 + step m
    ≃⟨ +-zeroᴸ ⟩
      step m
    ∎

  2+3≃5 : 2 + 3 ≃ 5
  2+3≃5 =
    begin
      2 + 3
    ≃⟨ +-stepᴸ⃗ᴿ ⟩
      1 + 4
    ≃⟨ +-stepᴸ⃗ᴿ ⟩
      0 + 5
    ≃⟨ +-zeroᴸ ⟩
      5
    ∎

  -- Lemma 2.2.2. For any natural number n, n + 0 = n.
  _ : ∀ {n} → n + 0 ≃ n
  _ = +-zeroᴿ

  -- Lemma 2.2.3. For any natural numbers n and m, n + step m = step (n + m).
  _ : ∀ {n m} → n + step m ≃ step (n + m)
  _ = +-stepᴿ

  _ : ∀ {n} → step n ≃ n + 1
  _ = step≃+

  -- Proposition 2.2.4 (Addition is commutative).
  _ : ∀ {n m} → n + m ≃ m + n
  _ = +-comm

  -- Proposition 2.2.5 (Addition is associative).
  -- Exercise 2.2.1
  _ : ∀ {a b c} → (a + b) + c ≃ a + (b + c)
  _ = +-assoc

  -- Proposition 2.2.6 (Cancellation law).
  _ : ∀ {a b c} → a + b ≃ a + c → b ≃ c
  _ = +-cancelᴸ

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
  -- My first proof uses a direct argument instead of the book's approach of
  -- proof by contradicition, because the latter is nonconstructive.
  a+b≃0→a≃0∧b≃0 : ∀ {a b} → a + b ≃ 0 → a ≃ 0 ∧ b ≃ 0
  a+b≃0→a≃0∧b≃0 {a} {b} a+b≃0 with case a
  ... | case-zero a≃0 = ∧-intro a≃0 b≃0
    where
      b≃0 =
        begin
          b
        ≃˘⟨ +-zeroᴸ ⟩
          0 + b
        ≃˘⟨ +-substᴸ a≃0 ⟩
          a + b
        ≃⟨ a+b≃0 ⟩
          0
        ∎
  ... | case-step (pred-intro p a≃sp) = ⊥-elim (step≄zero s[p+b]≃0)
    where
      s[p+b]≃0 =
        begin
          step (p + b)
        ≃˘⟨ +-stepᴸ ⟩
          step p + b
        ≃˘⟨ +-substᴸ a≃sp ⟩
          a + b
        ≃⟨ a+b≃0 ⟩
          0
        ∎

  -- I realized that we could use the book's argument if we showed that
  -- n ≃ 0 is decidable for any n.
  _ : ∀ {a b} → a + b ≃ 0 → a ≃ 0 ∧ b ≃ 0
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
     in upred-intro p (λ b′ a≃sb′ → step-inj (trans (sym a≃sb) a≃sb′))

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
        ≃⟨ +-stepᴿ⃗ᴸ ⟩
          step 5 + step (step zero)
        ≃⟨ +-stepᴿ⃗ᴸ ⟩
          step (step 5) + step zero
        ≃⟨ +-stepᴿ⃗ᴸ ⟩
          step (step (step 5)) + zero
        ≃⟨ +-zeroᴿ ⟩
          step (step (step 5))
        ≃⟨⟩
          8
        ∎
      5≤8 = ≤-intro 3 5+3≃8
      si = step-inj
      5≄8 = λ 5≃8 → step≄zero (si (si (si (si (si (sym 5≃8))))))

  -- Proposition 2.2.12 (Basic properties of order for natural numbers).
  -- Exercise 2.2.3

  -- (a) (Order is reflexive)
  _ : ∀ {a} → a ≤ a
  _ = ≤-refl

  -- (b) (Order is transitive)
  _ : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
  _ = ≤-trans

  -- (c) (Order is anti-symmetric)
  _ : ∀ {a b} → a ≤ b → b ≤ a → a ≃ b
  _ = ≤-antisym

  -- (d) (Addition preserves order)
  _ : ∀ {a b c} → a ≤ b ↔ a + c ≤ b + c
  _ = ↔-intro ≤-compat-+ᵁᴿ ≤-compat-+ᴰᴿ

  -- (e)
  _ : ∀ {a b} → a < b ↔ step a ≤ b
  _ = ↔-intro <→s≤ s≤→<

  -- (f)
  <↔<⁺ : ∀ {a b} → a < b ↔ a <⁺ b
  <↔<⁺ = ↔-intro <→<⁺ <⁺→<

  -- Proposition 2.2.13 (Trichotomy of order for natural numbers).
  trichotomy-of-order :
    ∀ {a b} →
      Trichotomy a b ∧ ¬ ((a < b ∧ a ≃ b) ∨ (a > b ∧ a ≃ b) ∨ (a < b ∧ a > b))
  trichotomy-of-order {a} {b} = ∧-intro trichotomy any-pair-absurd
    where
      any-pair-absurd : ¬ ((a < b ∧ a ≃ b) ∨ (a > b ∧ a ≃ b) ∨ (a < b ∧ a > b))
      any-pair-absurd
        (∨-introᴸ (∧-intro (<-intro a≤b a≄b) a≃b)) =
          a≄b a≃b
      any-pair-absurd
        (∨-introᴿ (∨-introᴸ (∧-intro (<-intro b≤a b≄a) a≃b))) =
          b≄a (sym a≃b)
      any-pair-absurd
        (∨-introᴿ (∨-introᴿ (∧-intro (<-intro a≤b a≄b) (<-intro b≤a b≄a)))) =
          a≄b (≤-antisym a≤b b≤a)

  -- Proposition 2.2.14
  -- Exercise 2.2.5
  _ :
    (P : ℕ → Set) (b : ℕ) →
    (∀ m → b ≤ m → (∀ k → b ≤ k → k < m → P k) → P m) →
    ∀ n → b ≤ n → P n
  _ = strong-ind

  -- Exercise 2.2.6
  backwards-ind :
    (P : ℕ → Set) → (∀ {n₁ n₂} → n₁ ≃ n₂ → P n₁ → P n₂) → ∀ {n} → P n →
    (∀ {k} → P (step k) → P k) →
    ∀ {m} → m ≤ n → P m
  backwards-ind P P-subst {n} Pn Pk m≤n = ind Q Qz Qs n Pn m≤n
    where
      Q = λ x → P x → ∀ {y} → y ≤ x → P y

      Qz : Q 0
      Qz Pz y≤z = P-subst (sym (∨-forceᴿ <-zero (≤→<∨≃ y≤z))) Pz

      Qs : step-case Q
      Qs Qk Psk y≤sk with ≤s→≤∨≃s y≤sk
      ... | ∨-introᴸ y≤k = Qk (Pk Psk) y≤k
      ... | ∨-introᴿ y≃sk = P-subst (sym y≃sk) Psk

  {- 2.3 Multiplication -}

  -- Definition 2.3.1 (Multiplication of natural numbers).
  _ : ℕ → ℕ → ℕ
  _ = _*_

  0*m : ∀ {m} → 0 * m ≃ 0
  0*m = *-zeroᴸ

  1*m : ∀ {m} → 1 * m ≃ 0 + m
  1*m {m} = trans *-stepᴸ (+-substᴸ 0*m)

  2*m : ∀ {m} → 2 * m ≃ 0 + m + m
  2*m {m} = trans *-stepᴸ (+-substᴸ 1*m)

  -- Lemma 2.3.2 (Multiplication is commutative).
  -- Exercise 2.3.1
  _ : ∀ {n m} → n * m ≃ m * n
  _ = *-comm

  -- Lemma 2.3.3 (Positive natural numbers have no zero divisors).
  -- Exercise 2.3.2
  no-zero-divs : ∀ {n m} → n * m ≃ 0 ↔ n ≃ 0 ∨ m ≃ 0
  no-zero-divs {n} {m} = ↔-intro *-either-zero backward
    where
      backward : n ≃ 0 ∨ m ≃ 0 → n * m ≃ 0
      backward (∨-introᴸ n≃0) = trans (*-substᴸ n≃0) *-zeroᴸ
      backward (∨-introᴿ m≃0) = trans (*-substᴿ m≃0) *-zeroᴿ

  -- Proposition 2.3.4 (Distributive law).
  _ : ∀ {a b c} → a * (b + c) ≃ a * b + a * c
  _ = *-distrib-+ᴸ

  -- Proposition 2.3.5 (Multiplication is associative).
  -- Exercise 2.3.3
  _ : ∀ {a b c} → (a * b) * c ≃ a * (b * c)
  _ = *-assoc

  -- Proposition 2.3.6 (Multiplication preserves order).
  _ : ∀ {a b c} → a < b → c ≄ 0 → a * c < b * c
  _ = *-preserves-<

  -- Corollary 2.3.7 (Cancellation law).
  _ : ∀ {a b c} → c ≄ 0 → a * c ≃ b * c → a ≃ b
  _ = *-cancelᴿ

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
          r<m = <-intro ≤-zero (¬sym m≄0)
          n≃mq+r = sym (trans +-zeroᴿ *-zeroᴿ)

      Ps : step-case P
      Ps {k} (div-intro q r r<m k≃mq+r) with ≤→<∨≃ (<→s≤ r<m)
      ... | ∨-introᴸ sr<m = div-intro q (step r) sr<m sk≃mq+sr
        where
          sk≃mq+sr = trans (AA.subst k≃mq+r) (sym +-stepᴿ)
      ... | ∨-introᴿ sr≃m = div-intro (step q) 0 0<m sk≃m[sq]+0
        where
          0<m = <-intro ≤-zero (¬sym m≄0)

          sk≃m[sq]+0 =
            begin
              step k
            ≃⟨ AA.subst k≃mq+r ⟩
              step (m * q + r)
            ≃˘⟨ +-stepᴿ ⟩
              m * q + step r
            ≃⟨ +-substᴿ sr≃m ⟩
              m * q + m
            ≃˘⟨ *-stepᴿ ⟩
              m * step q
            ≃˘⟨ +-zeroᴿ ⟩
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
    ≃⟨ *-substᴸ x^0≃1 ⟩
      1 * x
    ≃⟨ *-oneᴸ ⟩
      x
    ∎

  x^2≃xx : ∀ {x} → x ^ 2 ≃ x * x
  x^2≃xx {x} =
    begin
      x ^ 2
    ≃⟨ ^-stepᴿ ⟩
      x ^ 1 * x
    ≃⟨ *-substᴸ x^1≃x ⟩
      x * x
    ∎

  x^3≃xxx : ∀ {x} → x ^ 3 ≃ x * x * x
  x^3≃xxx {x} =
    begin
      x ^ 3
    ≃⟨ ^-stepᴿ ⟩
      x ^ 2 * x
    ≃⟨ *-substᴸ x^2≃xx ⟩
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
    ≃⟨ +-substᴸ *-oneᴸ ⟩
      x + x
    ∎

  -- Exercise 2.3.4
  ex234 : ∀ {a b} → (a + b) ^ 2 ≃ a ^ 2 + 2 * a * b + b ^ 2
  ex234 {a} {b} =
    begin
      (a + b) ^ 2
    ≃⟨ x^2≃xx ⟩
      (a + b) * (a + b)
    ≃⟨ *-distrib-+ᴿ ⟩
      a * (a + b) + b * (a + b)
    ≃⟨ +-substᴸ *-distrib-+ᴸ ⟩
      a * a + a * b + b * (a + b)
    ≃⟨ +-substᴿ *-distrib-+ᴸ ⟩
      a * a + a * b + (b * a + b * b)
    ≃⟨ +-substᴿ (+-substᴸ *-comm) ⟩
      a * a + a * b + (a * b + b * b)
    ≃˘⟨ +-assoc ⟩
      a * a + a * b + a * b + b * b
    ≃⟨ +-substᴸ +-assoc ⟩
      a * a + (a * b + a * b) + b * b
    ≃˘⟨ +-substᴸ (+-substᴿ 2x≃x+x) ⟩
      a * a + 2 * (a * b) + b * b
    ≃˘⟨ +-substᴸ (+-substᴿ *-assoc) ⟩
      a * a + 2 * a * b + b * b
    ≃˘⟨ +-substᴸ (+-substᴸ x^2≃xx) ⟩
      a ^ 2 + 2 * a * b + b * b
    ≃˘⟨ +-substᴿ x^2≃xx ⟩
      a ^ 2 + 2 * a * b + b ^ 2
    ∎
