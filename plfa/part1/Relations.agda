module plfa.part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

infix 4 _≤_

-- Exercise orderings (practice)

-- The cartesian product is trivially reflexive, and transitive but it is not
-- anti-symmetric.

-- The "divides" order defined by m | n iff there is k such that k * m = n is
--  - reflexive (k = 1, n = n)
--  - transitive (if k₁ * m = n, k₂ * n = p, then k₁ * k₂ * m = p and m | p)
--  - anti-symmetric (if k₁ * m = n and k₂ * n = m, then k₁ * k₂ * m = m, k₁ *
-- k₂ = 1, and n = m)
-- However, | is not total: neither 2 | 3 nor 3 | 2, for example.

-- Reflexivity

≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

-- Transitivity

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

-- Anti-symmetry

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

-- Exercise ≤-antisym-cases (practice)

-- Because the successor of a number cannot be equal to zero, and in each
-- inductive step we reduce the value of the number by one in both
-- inequalities.

-- Monotonicity

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

-- Exercise *-mono-≤ (stretch)

*-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
  ------------
  → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
  ------------
  → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q  =  ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

-- Strict inequality

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

-- Exercise <-trans (recommended)

<-trans : ∀ (m n p : ℕ)
  → m < n
  → n < p
  --------
  → m < p
<-trans zero (suc n) (suc p) z<s _ = z<s
<-trans (suc m) (suc n) (suc p) (s<s m<n) (s<s n<p) = s<s (<-trans m n p m<n n<p)

-- Exercise trichotomy (practice)

data Trichotomy (m n : ℕ) : Set where

  forward :
      m < n
      ---------
    → Trichotomy m n

  stale :
      m ≡ n
      ---------
    → Trichotomy m n

  flipped :
      n < m
      ---------
    → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = stale refl
<-trichotomy zero (suc n) = forward z<s
<-trichotomy (suc m) zero = flipped z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...                             | forward m<n = forward (s<s m<n)
...                             | stale m≡n = stale (cong suc m≡n)
...                             | flipped n<m = flipped (s<s n<m)

-- Exercise +-mono-< (practice)

+-mono-<ʳ : ∀ (n p q : ℕ)
  → n < p
  ----------
  → q + n < q + p
+-mono-<ʳ _ _ zero n<p = n<p
+-mono-<ʳ n p (suc q) n<p = s<s (+-mono-<ʳ n p q n<p)

+-mono-<ˡ : ∀ (m n p : ℕ)
  → m < n
  ----------
  → m + p < n + p
+-mono-<ˡ m n p m<n rewrite +-comm m p | +-comm n p = +-mono-<ʳ m n p m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
  -----------
  → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (m + p) (n + p) (n + q) (+-mono-<ˡ m n p m<n) (+-mono-<ʳ p q n p<q)

-- Exercise ≤-iff-< (recommended)

≤-if-< : ∀ (m n : ℕ)
  → m < n
  ----------
  → (suc m) ≤ n
≤-if-< zero (suc n) z<s = s≤s z≤n
≤-if-< (suc m) (suc n) (s<s m<n) = s≤s (≤-if-< m n m<n)

<-if-≤ : ∀ (m n : ℕ)
  → (suc m) ≤ n
  ----------
  → m < n
<-if-≤ zero (suc n) _ = z<s
<-if-≤ (suc m) (suc n) (s≤s sm≤n) = s<s (<-if-≤ m n sm≤n)

-- Exercise <-trans-revisited (practice)

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

<-trans-revisited : ∀ (m n p : ℕ)
  → m < n
  → n < p
  ----------
  → m < p
<-trans-revisited m n p m<n n<p = <-if-≤ m p (inv-s≤s (+-mono-≤ 0 1 (suc (suc m)) p z≤n (≤-trans (s≤s (≤-if-< m n m<n)) (≤-if-< n p n<p))))

-- Even and odd

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc   : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)

-- Exercise o+o≡e (stretch)

e+o≡o : ∀ {m n : ℕ}
  → even m
  → odd n
    -----------
  → odd (m + n)

e+o≡o {m} {n} em (suc en) rewrite +-comm m n = suc (e+e≡e en em)

o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
  -----------
  → even (m + n)

o+o≡e (suc zero) (suc zero) = suc (suc zero)
o+o≡e (suc em) on = suc (e+o≡o em on)

-- Exercise Bin-predicates (stretch)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin
to 0 = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (bin O) = from bin + from bin
from (bin I) = 1 + from bin + from bin

data One : Bin → Set where
  one :
    ----------
    One (⟨⟩ I)

  add-zero : ∀ {bin : Bin}
    → One bin
    -------------
    → One (bin O)

  add-one : ∀ {bin : Bin}
    → One bin
    -------------
    → One (bin I)

inc-preserves-leading-one : ∀ {bin : Bin}
  → One bin
  ---------------
  → One (inc bin)

inc-preserves-leading-one one = add-zero one
inc-preserves-leading-one (add-zero lone) = add-one lone
inc-preserves-leading-one (add-one lone) = add-zero (inc-preserves-leading-one lone)

data Can : Bin → Set where
  zero :
    --------
    Can (⟨⟩ O)

  leading-one : ∀ {bin : Bin}
    → One bin
      -------
    → Can bin

inc-preserves-can : ∀ {bin : Bin}
  → Can bin
    -------------
  → Can (inc bin)

inc-preserves-can zero = leading-one one
inc-preserves-can (leading-one one) = leading-one (add-zero one)
inc-preserves-can (leading-one (add-zero lone)) = leading-one (add-one lone)
inc-preserves-can (leading-one (add-one lone)) = leading-one (add-zero (inc-preserves-leading-one lone))

to-yields-can : ∀ (n : ℕ)
     ----------
  → Can (to n)

to-yields-can zero = zero
to-yields-can (suc n) = inc-preserves-can (to-yields-can n)

zero-<-from-one : ∀ (bin : Bin)
  → One bin
     -------------
  → 0 < (from bin)

zero-<-from-one (⟨⟩ I) one = z<s
zero-<-from-one (bin O) (add-zero bin-one) = (+-mono-< 0 (from bin) 0 (from bin) (zero-<-from-one bin bin-one) (zero-<-from-one bin bin-one))
zero-<-from-one (bin I) (add-one bin-one) = z<s

to-suc-n-2-O : ∀ (n : ℕ)
  → 0 < n
     ---------------------
  → to (n + n) ≡ (to n) O

to-suc-n-2-O zero ()
to-suc-n-2-O (suc zero) z<s = refl
to-suc-n-2-O (suc (suc n)) z<s =
  begin
    to (suc (suc n) + suc (suc n))
  ≡⟨⟩
    inc (to (suc n + suc (suc n)))
  ≡⟨ cong inc (cong to (+-comm (suc n) (suc (suc n)))) ⟩
    inc (to (suc (suc n) + suc n))
  ≡⟨⟩
    inc (inc (to (suc n + suc n)))
  ≡⟨ cong inc (cong inc (to-suc-n-2-O (suc n) z<s)) ⟩
    inc (inc (to (suc n) O))
  ≡⟨⟩
    (to (suc (suc n))) O
  ∎


to-from-can≡id : ∀ {bin : Bin}
  → Can bin
     ---------------
  → to (from bin) ≡ bin

to-from-can≡id zero = refl
to-from-can≡id (leading-one one) = refl
to-from-can≡id {bin O} (leading-one (add-zero lone)) =
  begin
    to (from (bin O))
  ≡⟨⟩
    to (from bin + from bin)
  ≡⟨ to-suc-n-2-O (from bin) (zero-<-from-one bin lone) ⟩
    (to (from bin)) O
  ≡⟨ cong (_O) (to-from-can≡id (leading-one lone)) ⟩
    bin O
  ∎
to-from-can≡id {bin I} (leading-one (add-one lone)) =
  begin
    to (from (bin I))
  ≡⟨⟩
    to (1 + from bin + from bin)
  ≡⟨⟩
    to (suc (from bin + from bin))
  ≡⟨⟩
    inc (to (from bin + from bin))
  ≡⟨ cong (inc) (to-suc-n-2-O (from bin) (zero-<-from-one bin lone)) ⟩
    inc ((to (from bin)) O)
  ≡⟨⟩
   (to (from bin)) I
  ≡⟨ cong (_I) (to-from-can≡id (leading-one lone)) ⟩
    bin I
  ∎
