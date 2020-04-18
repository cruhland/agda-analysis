module net.cruhland.Analysis.Chapter2 where

open import Agda.Builtin.FromNat using (Number)
open import Data.Unit using (⊤)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; trans; subst; cong)
open Eq.≡-Reasoning
open import net.cruhland.axiomatic.Logic using (LogicBundle)
open import net.cruhland.axiomatic.Peano using (PeanoBundle)

module _ (LB : LogicBundle) (PB : PeanoBundle LB) where
  open LogicBundle LB
  open PeanoBundle PB
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
  -- This can't be proven by the method the book uses, because Agda
  -- uses constructive logic.
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
