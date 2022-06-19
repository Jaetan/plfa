module part1.Naturals where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

one = suc zero
two = suc one
three = suc two
four = suc three
five = suc four
six = suc five
seven = suc six
-- seven = suc (suc (suc (suc (suc (suc (suc zero))))))

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin 2 + 3 ≡⟨⟩ suc (1 + 3)
              ≡⟨⟩ suc (suc (0 + 3))
              ≡⟨⟩ suc (suc 3)
              ≡⟨⟩ suc 4
              ≡⟨⟩ 5 ∎

_ : 2 + 3 ≡ 5
_ = refl

_ : 3 + 4 ≡ 7
_ = begin 3 + 4
    ≡⟨⟩ suc (2 + 4)
    ≡⟨⟩ suc (suc (1 + 4))
    ≡⟨⟩ suc (suc (suc (0 + 4)))
    ≡⟨⟩ suc (suc (suc 4))
    ≡⟨⟩ suc (suc 5)
    ≡⟨⟩ suc 6
    ≡⟨⟩ 7 ∎

_⋆_ : ℕ → ℕ → ℕ
zero ⋆ n = zero
(suc m) ⋆ n = (m ⋆ n) + n

_ : 2 ⋆ 3 ≡ 6
_ = begin 2 ⋆ 3 ≡⟨⟩  (1 ⋆ 3) + 3
                ≡⟨⟩ ((0 ⋆ 3) + 3) + 3
                ≡⟨⟩  (0 + 3) + 3
                ≡⟨⟩   3 + 3
                ≡⟨⟩   6 ∎

_ : 3 ⋆ 4 ≡ 12
_ = begin 3 ⋆ 4 ≡⟨⟩   ( 2 ⋆ 4) + 4
                ≡⟨⟩  (( 1 ⋆ 4) + 4) + 4
                ≡⟨⟩ ((( 0 ⋆ 4) + 4) + 4) + 4
                ≡⟨⟩  (( 0 + 4) + 4) + 4
                ≡⟨⟩   ( 4 + 4) + 4
                ≡⟨⟩     8 + 4
                ≡⟨⟩    12 ∎

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = (m ^ n) ⋆ m

_ : 3 ^ 4 ≡ 81
_ = begin  3 ^ 4 ≡⟨⟩    ( 3 ^ 3) ⋆ 3
                 ≡⟨⟩   (( 3 ^ 2) ⋆ 3) ⋆ 3
                 ≡⟨⟩  ((( 3 ^ 1) ⋆ 3) ⋆ 3) ⋆ 3
                 ≡⟨⟩ (((( 3 ^ 0) ⋆ 3) ⋆ 3) ⋆ 3) ⋆ 3
                 ≡⟨⟩  ((( 1 ⋆ 3) ⋆ 3) ⋆ 3) ⋆ 3
                 ≡⟨⟩   (( 3 ⋆ 3) ⋆ 3) ⋆ 3
                 ≡⟨⟩    ( 9 ⋆ 3) ⋆ 3
                 ≡⟨⟩     27 ⋆ 3
                 ≡⟨⟩     81 ∎

_∸_ : ℕ → ℕ → ℕ
zero ∸ n = zero
suc m ∸ zero = suc m
suc m ∸ suc n = m ∸ n

_ : 5 ∸ 3 ≡ 2
_ = begin 5 ∸ 3    ≡⟨⟩ (suc 4) ∸ (suc 2)
    ≡⟨⟩   4 ∸ 2    ≡⟨⟩ (suc 3) ∸ (suc 1)
    ≡⟨⟩   3 ∸ 1    ≡⟨⟩ (suc 2) ∸ (suc zero)
    ≡⟨⟩   2 ∸ zero ≡⟨⟩ (suc 1) ∸ zero
    ≡⟨⟩   suc 1    ≡⟨⟩ 2 ∎

_ : 3 ∸ 5 ≡ 0
_ = begin 3 ∸ 5    ≡⟨⟩ (suc 2) ∸ (suc 4)
    ≡⟨⟩   2 ∸ 4    ≡⟨⟩ (suc 1) ∸ (suc 3)
    ≡⟨⟩   1 ∸ 3    ≡⟨⟩ (suc zero) ∸ (suc 2)
    ≡⟨⟩   zero ∸ 2 ≡⟨⟩ zero ∎

infixl 6 _+_ _∸_
infixl 7 _⋆_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _⋆_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

data Carry : Set where
  NC : Carry
  CY : Carry

-- This version avoids inc ⟨⟩ ≡ ⟨⟩ I, which looks desirable since ⟨⟩
-- is an empty binary number, not zero as a binary. However, this
-- makes it impossible to prove from (inc n) ≡ suc (from n) later; so
-- it is not the definition used in later files.
-- inc : Bin → Bin
-- inc ⟨⟩ = ⟨⟩
-- inc n = incc n CY
--   where incc : Bin → Carry → Bin
--         incc n NC = n
--         incc ⟨⟩ CY = ⟨⟩ I
--         incc (n O) CY = n I
--         incc (n I) CY = (incc n CY) O

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = inc b O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = zero
from (n O) = 2 ⋆ (from n)
from (n I) = 2 ⋆ (from n) + 1

-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
