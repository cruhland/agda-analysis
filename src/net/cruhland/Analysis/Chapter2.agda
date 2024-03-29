import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_; _*_; _^_; _≤_; _<_; _>_)
import net.cruhland.axioms.Ordering as Ord
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as Sign
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic
  using (_∧_; _∨_; ∨-forceᴿ; ∨-introᴸ; ∨-introᴿ; _↔_; ↔-intro; _↯_)

module net.cruhland.Analysis.Chapter2 (PA : PeanoArithmetic) where
  private
    open module ℕ = PeanoArithmetic PA using (ℕ; step; zero)

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
  _ = ℕ.step≄zero

  -- Proposition 2.1.6. 4 is not equal to 0.
  4≄0 : 4 ≄ 0
  4≄0 = ℕ.step≄zero

  -- Axiom 2.4. Different natural numbers must have different successors.
  _ : ∀ {n m} → step n ≃ step m → n ≃ m
  _ = AA.inject {{r = ℕ.step-injective}}

  -- Proposition 2.1.8. 6 is not equal to 2.
  6≄2 : 6 ≄ 2
  6≄2 = AA.subst₁ (AA.subst₁ 4≄0)

  -- Axiom 2.5 (Principle of mathematical induction).
  _ : (P : ℕ → Set) → P 0 → (∀ {k} → P k → P (step k)) → ∀ n → P n
  _ = ℕ.ind

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
    rec-def = ℕ.ind P Pz Ps
      where
        P = UniqueAssignment

        Pz : P zero
        Pz = assign-intro c (assign-zero Eq.refl) (c-unique Eq.refl)
          where
            c-unique : ∀ {m} → m ≃ zero → ∀ {b} → b AssignedTo m → c ≃ b
            c-unique m≃z (assign-zero _) =
              Eq.refl
            c-unique m≃z (assign-step m≃sm′ b′≔m′) =
              let sm′≃z = Eq.trans (Eq.sym m≃sm′) m≃z
                  sm′≄z = ℕ.step≄zero
               in sm′≃z ↯ sm′≄z

        Ps : ℕ.step-case P
        Ps {k} (assign-intro a a≔k unique) =
          assign-intro (f k a) (assign-step Eq.refl a≔k) (f-unique Eq.refl)
            where
              f-unique : ∀ {m} → m ≃ step k → ∀ {b} → b AssignedTo m → f k a ≃ b
              f-unique m≃sk (assign-zero m≃z) =
                let sk≃z = Eq.trans (Eq.sym m≃sk) m≃z
                    sk≄z = ℕ.step≄zero
                 in sk≃z ↯ sk≄z
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
    ≃⟨ AA.fnOpCommSwap ⟩
      0 + step m
    ≃⟨ AA.ident ⟩
      step m
    ∎

  2+3≃5 : 2 + 3 ≃ 5
  2+3≃5 =
    begin
      2 + 3
    ≃⟨ AA.fnOpCommSwap ⟩
      1 + 4
    ≃⟨ AA.fnOpCommSwap ⟩
      0 + 5
    ≃⟨ AA.ident ⟩
      5
    ∎

  -- Lemma 2.2.2. For any natural number n, n + 0 = n.
  _ : {n : ℕ} → n + 0 ≃ n
  _ = AA.ident {{r = ℕ.+-identityᴿ}}

  -- Lemma 2.2.3. For any natural numbers n and m, n + step m = step (n + m).
  _ : ∀ {n m} → n + step m ≃ step (n + m)
  _ = Eq.sym (AA.fnOpComm {{r = ℕ.+-fnOpCommutative-stepᴿ}})

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
  _ = Sign.Positive

  positive-step : ∀ {n} → Sign.Positive (step n)
  positive-step = ℕ.Pos-intro-≄0 ℕ.step≄zero

  -- Proposition 2.2.8. If a is positive and b is a natural number,
  -- then a + b is positive.
  _ : {a b : ℕ} → Sign.Positive a → Sign.Positive (a + b)
  _ = ℕ.+-positive

  -- Corollary 2.2.9. If a and b are natural numbers such that a + b = 0,
  -- then a = 0 and b = 0.
  _ : {a b : ℕ} → a + b ≃ 0 → a ≃ 0 ∧ b ≃ 0
  _ = ℕ.+-both-zero

  -- Lemma 2.2.10. Let a be a positive natural number. Then there exists
  -- exactly one natural number b such that step b = a.
  -- Exercise 2.2.2
  record UniquePred (n : ℕ) : Set where
    constructor upred-intro
    field
      pred-exists : ℕ.Pred n

    open ℕ.Pred pred-exists public

    field
      pred-unique : ∀ m → m ℕ.IsPred n → pred-value ≃ m

  unique-predecessor : ∀ a → Sign.Positive a → UniquePred a
  unique-predecessor a pos-a =
    let p@(ℕ.pred-intro b a≃sb) = ℕ.pred (Sign.pos≄0 pos-a)
     in upred-intro p (λ b′ a≃sb′ → AA.inject (Eq.trans (Eq.sym a≃sb) a≃sb′))

  -- Definition 2.2.11 (Ordering of the natural numbers).
  _ : ℕ → ℕ → Set
  _ = _≤_

  -- Using Definition 2.2.11 on some examples
  8>5 : 8 > 5
  8>5 = Ord.lt-flip (ℕ.<-intro-≤≄ 5≤8 5≄8)
    where
      5+3≃8 =
        begin
          5 + 3
        ≃⟨⟩
          5 + step (step (step zero))
        ≃˘⟨ AA.fnOpCommSwap ⟩
          step 5 + step (step zero)
        ≃˘⟨ AA.fnOpCommSwap ⟩
          step (step 5) + step zero
        ≃˘⟨ AA.fnOpCommSwap ⟩
          step (step (step 5)) + zero
        ≃⟨ AA.ident ⟩
          step (step (step 5))
        ≃⟨⟩
          8
        ∎
      5≤8 = ℕ.≤-intro-diff 5+3≃8
      si = AA.inject
      5≄8 = Eq.≄-intro λ 5≃8 →
        let 3≃0 = si (si (si (si (si (Eq.sym 5≃8)))))
            3≄0 = ℕ.step≄zero
         in 3≃0 ↯ 3≄0

  -- Proposition 2.2.12 (Basic properties of order for natural numbers).
  -- Exercise 2.2.3
  lte = Ord.NonStrict².lte ℕ.nonStrictOrder

  -- (a) (Order is reflexive)
  _ : {a : ℕ} → a ≤ a
  _ = Eq.refl {{r = Ord.NonStrict.reflexive lte}}


  -- (b) (Order is transitive)
  _ : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
  _ = Eq.trans {{r = Ord.NonStrict.transitive lte}}

  -- (c) (Order is anti-symmetric)
  _ : {a b : ℕ} → a ≤ b → b ≤ a → a ≃ b
  _ = AA.antisym {{r = Ord.NonStrict.antisymmetric lte}}

  -- (d) (Addition preserves order)
  _ : {a b c : ℕ} → a ≤ b ↔ a + c ≤ b + c
  _ = ↔-intro AA.subst₂ AA.cancel

  -- (e)
  a<b↔sa≤b : ∀ {a b} → a < b ↔ step a ≤ b
  a<b↔sa≤b {a} {b} = ↔-intro ℕ.s≤-from-< ℕ.<-from-s≤

  -- (f)
  record _+d⁺≃_ (n m : ℕ) : Set where
    constructor +d⁺≃-intro
    field
      {d} : ℕ
      pos[d] : Sign.Positive d
      n+d≃m : n + d ≃ m

  <↔+d⁺≃ : ∀ {a b} → a < b ↔ a +d⁺≃ b
  <↔+d⁺≃ = ↔-intro <→+d⁺≃ +d⁺≃→<
    where
      <→+d⁺≃ = λ a<b → +d⁺≃-intro (ℕ.<-diff-pos a<b) (ℕ.<-elim-diff a<b)
      +d⁺≃→< = λ { (+d⁺≃-intro pos[d] n+d≃m) → ℕ.<-intro-diff pos[d] n+d≃m }

  -- Proposition 2.2.13 (Trichotomy of order for natural numbers).
  order-trichotomy : ∀ a b → AA.ExactlyOneOfThree (a < b) (a ≃ b) (a > b)
  order-trichotomy = ℕ.order-trichotomy

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
  backwards-ind P P-subst {n} Pn Pk m≤n = ℕ.ind Q Qz Qs n Pn m≤n
    where
      Q = λ x → P x → ∀ {y} → y ≤ x → P y

      Qz : Q 0
      Qz Pz y≤z = P-subst (Eq.sym (∨-forceᴿ ℕ.n≮0 (ℕ.≤-split y≤z))) Pz

      Qs : ℕ.step-case Q
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
  1*m {m} = Eq.trans ℕ.*-stepᴸ (AA.subst₂ 0*m)

  2*m : {m : ℕ} → 2 * m ≃ 0 + m + m
  2*m {m} = Eq.trans ℕ.*-stepᴸ (AA.subst₂ 1*m)

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
      backward (∨-introᴸ n≃0) = Eq.trans (AA.subst₂ n≃0) AA.absorb
      backward (∨-introᴿ m≃0) = Eq.trans (AA.subst₂ m≃0) AA.absorb

  -- Proposition 2.3.4 (Distributive law).
  _ : {a b c : ℕ} → a * (b + c) ≃ a * b + a * c
  _ = AA.distrib {{r = ℕ.*-distributive-+ᴸ}}

  -- Proposition 2.3.5 (Multiplication is associative).
  -- Exercise 2.3.3
  _ : {a b c : ℕ} → (a * b) * c ≃ a * (b * c)
  _ = AA.assoc {{r = ℕ.*-associative}}

  -- Proposition 2.3.6 (Multiplication preserves order).
  _ : {a b c : ℕ} → a < b → Sign.Positive c → a * c < b * c
  _ = ℕ.*-preserves-<ᴿ

  -- Corollary 2.3.7 (Cancellation law).
  _ : {a b c : ℕ} → c ≄ 0 → a * c ≃ b * c → a ≃ b
  _ = λ c≄0 →
        let instance pos[c] = ℕ.Pos-intro-≄0 c≄0
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
  euclid n m m≄0 = ℕ.ind P Pz Ps n
    where
      P = _DividedBy m

      Pz : P 0
      Pz = div-intro q r r<m n≃mq+r
        where
          q = 0
          r = 0
          r<m = ℕ.<-intro-≤≄ ℕ.≤-zeroᴸ (Eq.sym m≄0)
          n≃mq+r = Eq.sym (Eq.trans AA.ident AA.absorb)

      Ps : ℕ.step-case P
      Ps {k} (div-intro q r r<m k≃mq+r) with ℕ.≤-split (ℕ.s≤-from-< r<m)
      ... | ∨-introᴸ sr<m = div-intro q (step r) sr<m sk≃mq+sr
        where
          sk≃mq+sr = Eq.trans (AA.subst₁ k≃mq+r) AA.fnOpCommᴿ
      ... | ∨-introᴿ sr≃m = div-intro (step q) 0 0<m sk≃m[sq]+0
        where
          0<m = ℕ.<-intro-≤≄ ℕ.≤-zeroᴸ (Eq.sym m≄0)

          sk≃m[sq]+0 =
            begin
              step k
            ≃⟨ AA.subst₁ k≃mq+r ⟩
              step (m * q + r)
            ≃⟨ AA.fnOpCommᴿ ⟩
              m * q + step r
            ≃⟨ AA.subst₂ sr≃m ⟩
              m * q + m
            ≃˘⟨ ℕ.*-stepᴿ ⟩
              m * step q
            ≃˘⟨ AA.ident ⟩
              m * step q + 0
            ∎

  -- Definition 2.3.11 (Exponentiation for natural numbers).
  _ : ℕ → ℕ → ℕ
  _ = _^_

  -- Examples 2.3.12
  x^0≃1 : {x : ℕ} → x ^ 0 ≃ 1
  x^0≃1 = ℕ.^-zeroᴿ

  x^1≃x : {x : ℕ} → x ^ 1 ≃ x
  x^1≃x {x} =
    begin
      x ^ 1
    ≃⟨ ℕ.^-stepᴿ ⟩
      x ^ 0 * x
    ≃⟨ AA.subst₂ x^0≃1 ⟩
      1 * x
    ≃⟨ AA.ident ⟩
      x
    ∎

  x^2≃xx : {x : ℕ} → x ^ 2 ≃ x * x
  x^2≃xx {x} =
    begin
      x ^ 2
    ≃⟨ ℕ.^-stepᴿ ⟩
      x ^ 1 * x
    ≃⟨ AA.subst₂ x^1≃x ⟩
      x * x
    ∎

  x^3≃xxx : {x : ℕ} → x ^ 3 ≃ x * x * x
  x^3≃xxx {x} =
    begin
      x ^ 3
    ≃⟨ ℕ.^-stepᴿ ⟩
      x ^ 2 * x
    ≃⟨ AA.subst₂ x^2≃xx ⟩
      x * x * x
    ∎

  2x≃x+x : ∀ {x} → 2 * x ≃ x + x
  2x≃x+x {x} =
    begin
      2 * x
    ≃⟨⟩
      step 1 * x
    ≃⟨ ℕ.*-stepᴸ ⟩
      1 * x + x
    ≃⟨ AA.subst₂ AA.ident ⟩
      x + x
    ∎

  -- Exercise 2.3.4
  ex234 : {a b : ℕ} → (a + b) ^ 2 ≃ a ^ 2 + 2 * a * b + b ^ 2
  ex234 {a} {b} =
    begin
      (a + b) ^ 2
    ≃⟨ x^2≃xx ⟩
      (a + b) * (a + b)
    ≃⟨ AA.distrib ⟩
      a * (a + b) + b * (a + b)
    ≃⟨ AA.distrib-twoᴸ ⟩
      a * a + a * b + (b * a + b * b)
    ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
      a * a + a * b + (a * b + b * b)
    ≃˘⟨ AA.assoc ⟩
      a * a + a * b + a * b + b * b
    ≃⟨ AA.subst₂ AA.assoc ⟩
      a * a + (a * b + a * b) + b * b
    ≃˘⟨ AA.subst₂ (AA.subst₂ 2x≃x+x) ⟩
      a * a + 2 * (a * b) + b * b
    ≃˘⟨ AA.subst₂ (AA.subst₂ AA.assoc) ⟩
      a * a + 2 * a * b + b * b
    ≃˘⟨ AA.subst₂ (AA.subst₂ x^2≃xx) ⟩
      a ^ 2 + 2 * a * b + b * b
    ≃˘⟨ AA.subst₂ x^2≃xx ⟩
      a ^ 2 + 2 * a * b + b ^ 2
    ∎
