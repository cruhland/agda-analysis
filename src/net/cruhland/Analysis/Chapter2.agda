module net.cruhland.Analysis.Chapter2 where

open import Agda.Builtin.FromNat using (Number)
open import Data.Unit using (⊤)
open import Function using (id)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; trans; subst; cong)
open Eq.≡-Reasoning
open import net.cruhland.axiomatic.Logic using (LogicBundle)
open import net.cruhland.axiomatic.Peano using (PeanoBundle)

module _ (LB : LogicBundle) (PB : PeanoBundle LB) where
  open LogicBundle LB
  open PeanoBundle PB
  open import net.cruhland.axiomatic.Logic.Decidable LB
  open import net.cruhland.axiomatic.Peano.Addition LB PB
  open import net.cruhland.axiomatic.Peano.Literals LB PB

  -- Proposition 2.1.4
  threeProof : ℕ
  threeProof = succ (succ (succ zero))

  threeDigit : ℕ
  threeDigit = 3

  -- Proposition 2.1.6
  4≢0 : 4 ≢ 0
  4≢0 = succ≢zero

  -- Proposition 2.1.8
  6≢2 : 6 ≢ 2
  6≢2 = λ 6≡2 → 4≢0 (succ-inj (succ-inj 6≡2))

  -- Definition 2.2.1
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

  -- Lemma 2.2.2
  n+0≡n : ∀ {n} → n + 0 ≡ n
  n+0≡n = +-zeroᴿ

  -- Lemma 2.2.3
  n+sm≡s[n+m] : ∀ {n m} → n + succ m ≡ succ (n + m)
  n+sm≡s[n+m] = +-succᴿ

  sn≡n+1 : ∀ {n} → succ n ≡ n + 1
  sn≡n+1 {n} =
    begin
      succ n
    ≡⟨ cong succ (sym n+0≡n) ⟩
      succ (n + 0)
    ≡⟨ sym n+sm≡s[n+m] ⟩
      n + succ 0
    ≡⟨⟩
      n + 1
    ∎

  -- Proposition 2.2.4
  addition-is-commutative : ∀ {n m} → n + m ≡ m + n
  addition-is-commutative = +-comm

  -- Proposition 2.2.5 / Exercise 2.2.1
  addition-is-associative : ∀ {a b c} → (a + b) + c ≡ a + (b + c)
  addition-is-associative = +-assoc

  -- Proposition 2.2.6
  cancellation-law : ∀ {a b c} → a + b ≡ a + c → b ≡ c
  cancellation-law = +-cancelᴸ

  -- Definition 2.2.7
  Positive : ℕ → Set
  Positive n = n ≢ 0

  -- Proposition 2.2.8
  pos+n≡pos : ∀ {a b} → Positive a → Positive (a + b)
  pos+n≡pos {a} {b} pos-a = ind P Pz Ps b
    where
      P = λ x → Positive (a + x)

      Pz : P 0
      Pz = subst Positive (sym +-zeroᴿ) pos-a

      Ps : succProp P
      Ps {k} _ = λ a+sk≡0 → succ≢zero (trans (sym +-succᴿ) a+sk≡0)

  -- Corollary 2.2.9
  -- My first proof uses a direct argument instead of the book's approach of
  -- proof by contradicition, because the latter is nonconstructive.
  a+b≡0→a≡0∧b≡0 : ∀ {a b} → a + b ≡ 0 → a ≡ 0 ∧ b ≡ 0
  a+b≡0→a≡0∧b≡0 {a} {b} a+b≡0 = ∨-elim case-a≡0 case-a≡succ-p (case a)
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
  zero-dec : (n : ℕ) → Decidable (n ≡ 0)
  zero-dec n = ∨-elim ∨-introᴸ n≡succ→n≢0 (case n)
    where
      n≡succ→n≢0 : Σ ℕ (λ p → n ≡ succ p) → Decidable (n ≡ 0)
      n≡succ→n≢0 p,n≡sp = ∨-introᴿ n≢0
        where
          n≢0 = λ n≡0 → succ≢zero (trans (sym (snd p,n≡sp)) n≡0)

  coro229 : ∀ {a b} → a + b ≡ 0 → a ≡ 0 ∧ b ≡ 0
  coro229 {a} {b} a+b≡0 = ¬[¬a∨¬b]→a∧b (zero-dec a) (zero-dec b) ¬[a≢0∨b≢0]
    where
      a≢0→⊥ = λ a≢0 → pos+n≡pos a≢0 a+b≡0
      b≢0→⊥ = λ b≢0 → pos+n≡pos b≢0 (trans +-comm a+b≡0)
      ¬[a≢0∨b≢0] = ∨-elim a≢0→⊥ b≢0→⊥

  -- Lemma 2.2.10
  -- Exercise 2.2.2
  _HasUniquePredecessor_ : ℕ → ℕ → Set
  a HasUniquePredecessor b = a ≡ succ b ∧ ∀ b′ → a ≡ succ b′ → b ≡ b′

  unique-predecessor : ∀ a → Positive a → Σ ℕ (a HasUniquePredecessor_)
  unique-predecessor a a≢0 = ∨-elim a≡0→goal a≡s→goal (case a)
    where
      a≡sb∧b-unique : ∀ {b} → a ≡ succ b → a HasUniquePredecessor b
      a≡sb∧b-unique a≡sb =
        ∧-intro a≡sb λ b′ a≡sb′ → succ-inj (trans (sym a≡sb) a≡sb′)

      a≡0→goal = λ a≡0 → ⊥-elim (a≢0 a≡0)
      a≡s→goal = Σ-map-snd a≡sb∧b-unique
