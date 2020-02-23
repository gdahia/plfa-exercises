module plfa.part1.Naturals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

-- Operations on naturals are recursive functions

_+_ : ℕ → ℕ → ℕ
n + zero = n
n + (suc m) = suc (n + m)

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    suc (suc 5)
  ≡⟨⟩
    suc 6
  ≡⟨⟩
    7
  ∎

-- Multiplication

_*_ : ℕ → ℕ → ℕ
n * zero = zero
n * (suc m) = n + (n * m)

-- Exercise *-example

_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    3 * (suc (suc (suc (suc 0))))
  ≡⟨⟩
    3 + (3 + (3 + 3))
  ≡⟨⟩
    12
  ∎

-- Exercise _^_

_^_ : ℕ → ℕ → ℕ
n ^ 0 = 1
n ^ (suc m) = n * (n ^ m)

_ : 3 ^ 4 ≡ 81
_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 ^ (suc (suc (suc (suc 0))))
  ≡⟨⟩
    3 * (3 * (3 * 3))
  ≡⟨⟩
    81
  ∎

-- Monus

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

-- Exercise ∸-example₁ and ∸-example₂

∸-example₁ : 5 ∸ 3 ≡ 2
∸-example₁ =
  begin
    5 ∸ 3
  ≡⟨⟩ -- expand nats
    suc (suc (suc 2)) ∸ (suc (suc (suc 0)))
  ≡⟨⟩ -- third case
    2 ∸ 0
  ≡⟨⟩ -- first case
    2
  ∎

∸-example₂ : 3 ∸ 5 ≡ 0
∸-example₂ =
  begin
    3 ∸ 5
  ≡⟨⟩ -- expand nats
    suc (suc (suc 0)) ∸ (suc (suc (suc 2)))
  ≡⟨⟩ -- third case
    0 ∸ 2
  ≡⟨⟩ -- second case
    0
  ∎

infixl 6  _+_  _∸_
infixl 7  _*_

-- More pragmas

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- Exercise Bin

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

-- example works

works_for_example : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
works_for_example = refl

-- one through four works

works_for_O : inc (⟨⟩ O) ≡ ⟨⟩ I
works_for_O = refl

works_for_I : inc (⟨⟩ I) ≡ ⟨⟩ I O
works_for_I = refl

works_for_OI : inc (⟨⟩ O I) ≡ ⟨⟩ I O
works_for_OI = refl

works_for_IO : inc (⟨⟩ I O) ≡ ⟨⟩ I I
works_for_IO = refl

works_for_II : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
works_for_II = refl

-- representation conversion

to : ℕ → Bin
to 0 = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (bin O) = 2 * (from bin)
from (bin I) = 1 + 2 * (from bin)

zero_conv_to : to 0 ≡ ⟨⟩ O
zero_conv_to = refl

zero_conv_from : 0 ≡ from (⟨⟩ O)
zero_conv_from = refl

one_conv_to : to 1 ≡ ⟨⟩ I
one_conv_to = refl

one_conv_from : 1 ≡ from (⟨⟩ I)
one_conv_from = refl

zero_one_conv_from : 1 ≡ from (⟨⟩ O I)
zero_one_conv_from = refl

two_conv_to : to 2 ≡ ⟨⟩ I O
two_conv_to = refl

two_conv_from : 2 ≡ from (⟨⟩ I O)
two_conv_from = refl

three_conv_to : to 3 ≡ ⟨⟩ I I
three_conv_to = refl

three_conv_from : 3 ≡ from (⟨⟩ I I)
three_conv_from = refl

four_conv_to : to 4 ≡ ⟨⟩ I O O
four_conv_to = refl

four_conv_from : 4 ≡ from (⟨⟩ I O O)
four_conv_from = refl
