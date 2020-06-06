module net.cruhland.Analysis.Chapter2 where

open import Agda.Builtin.FromNat using (Number)
open import Data.Unit using (⊤)
open import Function using (id; const)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; subst; cong)
open Eq.≡-Reasoning
open import net.cruhland.axiomatic.Logic using (LogicBundle)
open import net.cruhland.axiomatic.Peano using (PeanoBundle)

module _ (LB : LogicBundle) (PB : PeanoBundle LB) where
  open LogicBundle LB
  open PeanoBundle PB
  open import net.cruhland.axiomatic.Logic.Decidable LB
  open import net.cruhland.axiomatic.Peano.Addition LB PB
  open import net.cruhland.axiomatic.Peano.Literals LB PB
  open import net.cruhland.axiomatic.Peano.Multiplication LB PB
  open import net.cruhland.axiomatic.Peano.Ordering LB PB

  {- 2.1 The Peano Axioms -}

  -- Axiom 2.1. 0 is a natural number.
  _ : ℕ
  _ = 0

  -- Axiom 2.2. If n is a natural number, then (succ n) is also a
  -- natural number
  _ : ℕ → ℕ
  _ = succ

  _ : ℕ
  _ = succ (succ zero)

  -- Definition 2.1.3
  -- The digit-based representation is provided by the Peano.Literals module
  _ : 1 ≡ succ zero
  _ = refl

  _ : 2 ≡ succ (succ zero)
  _ = refl

  _ : 3 ≡ succ (succ (succ zero))
  _ = refl

  _ : 1 ≡ succ 0
  _ = refl

  _ : 2 ≡ succ 1
  _ = refl

  _ : 3 ≡ succ 2
  _ = refl

  -- Proposition 2.1.4. 3 is a natural number.
  _ : ℕ
  _ = succ (succ (succ zero))

  _ : ℕ
  _ = succ 2

  _ : ℕ
  _ = 3

  -- Axiom 2.3. 0 is not the successor of any natural number.
  _ : ∀ {n} → succ n ≢ 0
  _ = succ≢zero

  -- Proposition 2.1.6. 4 is not equal to 0.
  4≢0 : 4 ≢ 0
  4≢0 = succ≢zero

  -- Axiom 2.4. Different natural numbers must have different successors.
  _ : ∀ {n m} → succ n ≡ succ m → n ≡ m
  _ = succ-inj

  -- Proposition 2.1.8. 6 is not equal to 2.
  6≢2 : 6 ≢ 2
  6≢2 = λ 6≡2 → 4≢0 (succ-inj (succ-inj 6≡2))

  -- Axiom 2.5 (Principle of mathematical induction).
  _ : (P : ℕ → Set) → P 0 → (∀ {k} → P k → P (succ k)) → ∀ n → P n
  _ = ind

  -- Proposition 2.1.16 (Recursive definitions).
  -- There's something not quite right here, but it's hard for me to
  -- pin it down. I think because the book doesn't have the ind-zero
  -- and ind-succ axioms that I defined. Essentially, those β-reduction
  -- rules are equivalent to the book's argument that recursive definitions
  -- exist. It makes me wonder whether ind-zero and ind-succ are necessary.
  rec-def :
    (f : {ℕ} → (ℕ → ℕ)) →
    (c : ℕ) →
    Σ (ℕ → ℕ) (λ a → a 0 ≡ c ∧ ∀ n → a (succ n) ≡ f {n} (a n))
  rec-def f c = Σ-intro (ind (const ℕ) c f) (∧-intro ind-zero (λ n → ind-succ))

  {- 2.2 Addition -}

  -- Definition 2.2.1 (Addition of natural numbers).
  _ : ℕ → ℕ → ℕ
  _ = _+_

  0+m : ∀ {m} → 0 + m ≡ m
  0+m = rec-zero

  1+m : ∀ {m} → 1 + m ≡ succ m
  1+m {m} =
    begin
      1 + m
    ≡⟨⟩
      rec m succ 1
    ≡⟨⟩
      rec m succ (succ zero)
    ≡⟨ rec-succ-tail ⟩
      rec (succ m) succ zero
    ≡⟨ rec-zero ⟩
      succ m
    ∎

  2+3≡5 : 2 + 3 ≡ 5
  2+3≡5 =
    begin
      2 + 3
    ≡⟨⟩
      rec 3 succ 2
    ≡⟨⟩
      rec 3 succ (succ (succ zero))
    ≡⟨ rec-succ-tail ⟩
      rec (succ 3) succ (succ zero)
    ≡⟨ rec-succ-tail ⟩
      rec (succ (succ 3)) succ zero
    ≡⟨ rec-zero ⟩
      5
    ∎

  -- Lemma 2.2.2. For any natural number n, n + 0 = n.
  _ : ∀ {n} → n + 0 ≡ n
  _ = +-zeroᴿ

  -- Lemma 2.2.3. For any natural numbers n and m, n + succ m = succ (n + m).
  _ : ∀ {n m} → n + succ m ≡ succ (n + m)
  _ = +-succᴿ

  _ : ∀ {n} → succ n ≡ n + 1
  _ = succ≡+

  -- Proposition 2.2.4 (Addition is commutative).
  _ : ∀ {n m} → n + m ≡ m + n
  _ = +-comm

  -- Proposition 2.2.5 (Addition is associative).
  -- Exercise 2.2.1
  _ : ∀ {a b c} → (a + b) + c ≡ a + (b + c)
  _ = +-assoc

  -- Proposition 2.2.6 (Cancellation law).
  _ : ∀ {a b c} → a + b ≡ a + c → b ≡ c
  _ = +-cancelᴸ

  -- Definition 2.2.7 (Positive natural numbers).
  _ : ℕ → Set
  _ = Positive

  positive-succ : ∀ {n} → Positive (succ n)
  positive-succ = succ≢zero

  -- Proposition 2.2.8. If a is positive and b is a natural number,
  -- then a + b is positive.
  _ : ∀ {a b} → Positive a → Positive (a + b)
  _ = +-positive

  -- Corollary 2.2.9. If a and b are natural numbers such that a + b = 0,
  -- then a = 0 and b = 0.
  -- My first proof uses a direct argument instead of the book's approach of
  -- proof by contradicition, because the latter is nonconstructive.
  a+b≡0→a≡0∧b≡0 : ∀ {a b} → a + b ≡ 0 → a ≡ 0 ∧ b ≡ 0
  a+b≡0→a≡0∧b≡0 {a} {b} a+b≡0 = ∨-rec case-a≡0 case-a≡succ-p (case a)
    where
      case-a≡0 : a ≡ 0 → a ≡ 0 ∧ b ≡ 0
      case-a≡0 a≡0 = ∧-intro a≡0 (trans (sym +-zeroᴸ) 0+b≡0)
        where
          0+b≡0 = subst (λ x → x + b ≡ 0) a≡0 a+b≡0

      case-a≡succ-p : Σ ℕ (λ p → a ≡ succ p) → a ≡ 0 ∧ b ≡ 0
      case-a≡succ-p p∧a≡succ-p = ⊥-elim (succ≢zero s[p+b]≡0)
        where
          a≡succ-p = snd p∧a≡succ-p
          succ-p+b≡0 = subst (λ x → x + b ≡ 0) a≡succ-p a+b≡0
          s[p+b]≡0 = trans (sym +-succᴸ) succ-p+b≡0

  -- I realized that we could use the book's argument if we showed that
  -- n ≡ 0 is decidable for any n.
  _ : ∀ {a b} → a + b ≡ 0 → a ≡ 0 ∧ b ≡ 0
  _ = +-both-zero

  -- Lemma 2.2.10. Let a be a positive natural number. Then there exists
  -- exactly one natural number b such that succ b = a.
  -- Exercise 2.2.2
  _HasUniquePredecessor_ : ℕ → ℕ → Set
  a HasUniquePredecessor b = a ≡ succ b ∧ ∀ b′ → a ≡ succ b′ → b ≡ b′

  unique-predecessor : ∀ a → Positive a → Σ ℕ (a HasUniquePredecessor_)
  unique-predecessor a a≢0 = Σ-map-snd use-pred (pred a≢0)
    where
      use-pred : ∀ {b} → a ≡ succ b → a HasUniquePredecessor b
      use-pred a≡sb =
        ∧-intro a≡sb λ b′ a≡sb′ → succ-inj (trans (sym a≡sb) a≡sb′)

  -- Definition 2.2.11 (Ordering of the natural numbers).
  _ : ℕ → ℕ → Set
  _ = _≤_

  -- Using Definition 2.2.11 on some examples
  8>5 : 8 > 5
  8>5 = ∧-intro 5≤8 5≢8
    where
      5+3≡8 =
        begin
          5 + 3
        ≡⟨⟩
          5 + succ (succ (succ zero))
        ≡⟨ +-succᴿ⃗ᴸ ⟩
          succ 5 + succ (succ zero)
        ≡⟨ +-succᴿ⃗ᴸ ⟩
          succ (succ 5) + succ zero
        ≡⟨ +-succᴿ⃗ᴸ ⟩
          succ (succ (succ 5)) + zero
        ≡⟨ +-zeroᴿ ⟩
          succ (succ (succ 5))
        ≡⟨⟩
          8
        ∎
      5≤8 = Σ-intro 3 5+3≡8
      si = succ-inj
      5≢8 = λ 5≡8 → succ≢zero (si (si (si (si (si (sym 5≡8))))))

  -- Proposition 2.2.12 (Basic properties of order for natural numbers).
  -- Exercise 2.2.3

  -- (a) (Order is reflexive)
  _ : ∀ {a} → a ≤ a
  _ = ≤-refl

  -- (b) (Order is transitive)
  _ : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
  _ = ≤-trans

  -- (c) (Order is anti-symmetric)
  _ : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
  _ = ≤-antisym

  -- (d) (Addition preserves order)
  _ : ∀ {a b c} → a ≤ b ↔ a + c ≤ b + c
  _ = ∧-intro ≤-compat-+ᵁᴿ ≤-compat-+ᴰᴿ

  -- (e)
  _ : ∀ {a b} → a < b ↔ succ a ≤ b
  _ = ∧-intro <→≤ ≤→<

  -- (f)
  <↔positive-diff : ∀ {a b} → a < b ↔ Σ ℕ λ d → Positive d ∧ b ≡ a + d
  <↔positive-diff = ∧-intro <→positive-diff positive-diff→<

  -- Proposition 2.2.13 (Trichotomy of order for natural numbers).
  _ :
    ∀ {a b} →
    (a < b ∨ (a ≡ b ∨ a > b)) ∧
      ¬ (a < b ∧ a ≡ b ∨ (a > b ∧ a ≡ b ∨ a < b ∧ a > b))
  _ = ∧-intro trichotomy any-pair-absurd
    where
      use-<≡ = λ <≡ → ∧-elimᴿ (∧-elimᴸ <≡) (∧-elimᴿ <≡)
      use->≡ = λ >≡ → ∧-elimᴿ (∧-elimᴸ >≡) (sym (∧-elimᴿ >≡))
      use-<> = λ <> →
        ∧-elimᴿ
          (∧-elimᴸ <>)
          (≤-antisym (∧-elimᴸ (∧-elimᴸ <>)) (∧-elimᴸ (∧-elimᴿ <>)))
      any-pair-absurd = λ pairs → ∨-rec use-<≡ (∨-rec use->≡ use-<>) pairs

  -- Proposition 2.2.14
  -- Exercise 2.2.5
  _ :
    (P : ℕ → Set) (b : ℕ) →
    (∀ m → b ≤ m → (∀ k → b ≤ k → k < m → P k) → P m) →
    ∀ n → b ≤ n → P n
  _ = strong-ind

  -- Exercise 2.2.6
  backwards-ind :
    (P : ℕ → Set) → ∀ {n} → P n →
    (∀ {k} → P (succ k) → P k) →
    ∀ {m} → m ≤ n → P m
  backwards-ind P {n} Pn Pk m≤n = ind Q Qz Qs n Pn m≤n
    where
      Q = λ x → P x → ∀ {y} → y ≤ x → P y

      Qz : Q 0
      Qz Pz y≤z = subst P (sym (∨-forceᴿ <-zero (≤→<∨≡ y≤z))) Pz

      Qs : succProp Q
      Qs Qk Psk y≤sk = ∨-rec use-y≤k use-y≡sk (≤s→≤∨≡s y≤sk)
        where
          use-y≤k = λ y≤k → Qk (Pk Psk) y≤k
          use-y≡sk = λ y≡sk → subst P (sym y≡sk) Psk

  {- 2.3 Multiplication -}

  -- Definition 2.3.1 (Multiplication of natural numbers).
  _ : ℕ → ℕ → ℕ
  _ = _*_

  0*m : ∀ {m} → 0 * m ≡ 0
  0*m = *-zeroᴸ

  1*m : ∀ {m} → 1 * m ≡ 0 + m
  1*m {m} = trans *-succᴸ (cong (_+ m) 0*m)

  2*m : ∀ {m} → 2 * m ≡ 0 + m + m
  2*m {m} = trans *-succᴸ (cong (_+ m) 1*m)

  -- Lemma 2.3.2 (Multiplication is commutative).
  -- Exercise 2.3.1
  _ : ∀ {n m} → n * m ≡ m * n
  _ = *-comm

  -- Lemma 2.3.3 (Positive natural numbers have no zero divisors).
  -- Exercise 2.3.2
  no-zero-divs : ∀ {n m} → n * m ≡ 0 ↔ n ≡ 0 ∨ m ≡ 0
  no-zero-divs {n} {m} = ∧-intro *-either-zero backward
    where
      use-n≡0 = λ n≡0 → trans (cong (_* m) n≡0) *-zeroᴸ
      use-m≡0 = λ m≡0 → trans (cong (n *_) m≡0) *-zeroᴿ
      backward = ∨-rec use-n≡0 use-m≡0

  -- Proposition 2.3.4 (Distributive law).
  _ : ∀ {a b c} → a * (b + c) ≡ a * b + a * c
  _ = *-distrib-+ᴸ

  -- Proposition 2.3.5 (Multiplication is associative).
  -- Exercise 2.3.3
  _ : ∀ {a b c} → (a * b) * c ≡ a * (b * c)
  _ = *-assoc

  -- Proposition 2.3.6 (Multiplication preserves order).
  _ : ∀ {a b c} → a < b → c ≢ 0 → a * c < b * c
  _ = *-preserves-<

  -- Corollary 2.3.7 (Cancellation law).
  _ : ∀ {a b c} → c ≢ 0 → a * c ≡ b * c → a ≡ b
  _ = *-cancelᴿ

  -- Proposition 2.3.9 (Euclidean algorithm).
  -- Exercise 2.3.5
  euclid : ∀ n m → m ≢ 0 → Σ ℕ λ q → Σ ℕ λ r → r < m ∧ n ≡ m * q + r
  euclid n m m≢0 = ind P Pz Ps n
    where
      P = λ x → Σ ℕ λ q → Σ ℕ λ r → r < m ∧ x ≡ m * q + r

      Pz : P 0
      Pz = Σ-intro q (Σ-intro r (∧-intro r<m n≡mq+r))
        where
          q = 0
          r = 0
          r<m = ∧-intro ≤-zero (¬sym m≢0)
          n≡mq+r = sym (trans +-zeroᴿ *-zeroᴿ)

      Ps : succProp P
      Ps {k} Pk = Σ-rec (λ q Σr → Σ-rec (use-qr q) Σr) Pk
        where
          use-qr : ∀ q r → r < m ∧ k ≡ m * q + r → P (succ k)
          use-qr q r props = ∨-rec use-sr<m use-sr≡m (≤→<∨≡ (<→≤ r<m))
            where
              r<m = ∧-elimᴸ props
              k≡mq+r = ∧-elimᴿ props

              sk≡mq+sr = trans (cong succ k≡mq+r) (sym +-succᴿ)
              use-sr<m = λ sr<m →
                Σ-intro q (Σ-intro (succ r) (∧-intro sr<m sk≡mq+sr))

              0<m = ∧-intro ≤-zero (¬sym m≢0)
              use-sr≡m = λ sr≡m →
                let sk≡m[sq]+0 =
                      begin
                        succ k
                      ≡⟨ cong succ k≡mq+r ⟩
                        succ (m * q + r)
                      ≡⟨ sym +-succᴿ ⟩
                        m * q + succ r
                      ≡⟨ cong (m * q +_) sr≡m ⟩
                        m * q + m
                      ≡⟨ sym *-succᴿ ⟩
                        m * succ q
                      ≡⟨ sym +-zeroᴿ ⟩
                        m * succ q + 0
                      ∎
                 in Σ-intro (succ q) (Σ-intro 0 (∧-intro 0<m sk≡m[sq]+0))

  -- Definition 2.3.11 (Exponentiation for natural numbers).
  _^_ : ℕ → ℕ → ℕ
  n ^ m = rec 1 (_* n) m

  infixr 8 _^_

  -- Examples 2.3.12
  x^0≡1 : ∀ {x} → x ^ 0 ≡ 1
  x^0≡1 = rec-zero

  x^1≡x : ∀ {x} → x ^ 1 ≡ x
  x^1≡x {x} =
    begin
      x ^ 1
    ≡⟨ rec-succ ⟩
      x ^ 0 * x
    ≡⟨ cong (_* x) x^0≡1 ⟩
      1 * x
    ≡⟨ *-oneᴸ ⟩
      x
    ∎

  x^2≡xx : ∀ {x} → x ^ 2 ≡ x * x
  x^2≡xx {x} =
    begin
      x ^ 2
    ≡⟨ rec-succ ⟩
      x ^ 1 * x
    ≡⟨ cong (_* x) x^1≡x ⟩
      x * x
    ∎

  x^3≡xxx : ∀ {x} → x ^ 3 ≡ x * x * x
  x^3≡xxx {x} =
    begin
      x ^ 3
    ≡⟨ rec-succ ⟩
      x ^ 2 * x
    ≡⟨ cong (_* x) x^2≡xx ⟩
      x * x * x
    ∎

  2x≡x+x : ∀ {x} → 2 * x ≡ x + x
  2x≡x+x {x} =
    begin
      2 * x
    ≡⟨⟩
      succ 1 * x
    ≡⟨ *-succᴸ ⟩
      1 * x + x
    ≡⟨ cong (_+ x) *-oneᴸ ⟩
      x + x
    ∎

  -- Exercise 2.3.4
  ex234 : ∀ {a b} → (a + b) ^ 2 ≡ a ^ 2 + 2 * a * b + b ^ 2
  ex234 {a} {b} =
    begin
      (a + b) ^ 2
    ≡⟨ x^2≡xx ⟩
      (a + b) * (a + b)
    ≡⟨ *-distrib-+ᴿ ⟩
      a * (a + b) + b * (a + b)
    ≡⟨ cong (_+ b * (a + b)) *-distrib-+ᴸ ⟩
      a * a + a * b + b * (a + b)
    ≡⟨ cong (a * a + a * b +_) *-distrib-+ᴸ ⟩
      a * a + a * b + (b * a + b * b)
    ≡⟨ cong (λ x → a * a + a * b + (x + b * b)) *-comm ⟩
      a * a + a * b + (a * b + b * b)
    ≡⟨ sym +-assoc ⟩
      a * a + a * b + a * b + b * b
    ≡⟨ cong (_+ b * b) +-assoc ⟩
      a * a + (a * b + a * b) + b * b
    ≡⟨ cong (λ x → a * a + x + b * b) (sym 2x≡x+x) ⟩
      a * a + 2 * (a * b) + b * b
    ≡⟨ cong (λ x → a * a + x + b * b) (sym *-assoc) ⟩
      a * a + 2 * a * b + b * b
    ≡⟨ cong (λ x → x + 2 * a * b + b * b) (sym x^2≡xx) ⟩
      a ^ 2 + 2 * a * b + b * b
    ≡⟨ cong (a ^ 2 + 2 * a * b +_) (sym x^2≡xx) ⟩
      a ^ 2 + 2 * a * b + b ^ 2
    ∎
