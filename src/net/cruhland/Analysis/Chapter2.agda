module net.cruhland.Analysis.Chapter2 where

open import Agda.Builtin.FromNat using (Number)
open import Data.Unit using (⊤)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; cong)
open Eq.≡-Reasoning
open import net.cruhland.axiomatic.Peano using (PeanoBundle)

module _ (PB : PeanoBundle) where
  open PeanoBundle PB
  open import net.cruhland.axiomatic.Peano.Addition PB
  open import net.cruhland.axiomatic.Peano.Literals PB

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
  n+0≡n = +-identityᴿ

  -- Lemma 2.2.3
  n+sm≡s[n+m] : ∀ {n m} → n + succ m ≡ succ (n + m)
  n+sm≡s[n+m] = +-succᴿ
